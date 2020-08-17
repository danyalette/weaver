{-# LANGUAGE
    BlockArguments,
    DeriveTraversable,
    FlexibleContexts,
    GADTs,
    ImplicitParams,
    LambdaCase,
    OverloadedStrings,
    PatternSynonyms,
    RankNTypes,
    RecordWildCards,
    ScopedTypeVariables,
    TupleSections,
    TypeOperators,
    UnicodeSyntax,
    ViewPatterns
  #-}

module Main (main) where

import           Prelude hiding (lookup, putStrLn, readFile)
import           Control.Exception.Base (evaluate)
import           Control.Monad (when)
import           Control.Monad.Except (runExceptT, throwError)
import           Control.Monad.IO.Class (MonadIO (..))
import           Data.Automata.Regex (Regex, canonical)
import           Data.Finite.Container (Index)
import           Data.Foldable (for_)
import           Data.IORef (modifyIORef', newIORef, readIORef, writeIORef)
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map as OrdMap
import qualified Data.Set as OrdSet
import           Data.Text (Text, pack)
import           Data.Text.IO (putStrLn, readFile)
import           Data.Void (Void)
import           Language.SMT.Expr (Expr, true, false)
import           Language.SMT.SExpr (SExpr, parseAll, prettyPrint)
import           Language.SMT.Solver (Solver, newSolver)
import           Numeric.Natural (Natural)
import           System.Exit (exitFailure)
import           System.IO (hFlush, stdout)
import           System.Clock (Clock (..), diffTimeSpec, getTime, toNanoSecs)
import           Text.Printf (printf)
import           Weaver.Algorithm (Assertions, Algorithm (..), Interface (..), Solver' (..))
import           Weaver.Config (Config, debug, minimize)
import           Weaver.Program (Program (..), compile)
import           Weaver.Stmt (V, Stmt, isArtificial, prove, isTriple, isIndep)
import           Weaver.Bound (Bound (..), bounded)
import           Weaver.Options (Options (..), parseOptions)

main ∷ IO ()
main = do
  Options filepath algorithm backend script config bound iters ← parseOptions
  file    ← readFile filepath
  sexprs  ← parseProgram file
  program ← compileProgram sexprs
  solver  ← newSolver (backend script)
  let ?config = config
  result  ← time "Total time" (verifyProgram bound iters solver algorithm program)
  case result of
    Nothing → putStrLn "SUCCESS"
    Just xs → do mapM_ prettyPrint xs
                 putStrLn "FAILURE"

parseProgram ∷ Text → IO [SExpr Void]
parseProgram text =
  case parseAll text of
    Right xs → return xs
    Left err → do
      putStrLn err
      exitFailure

compileProgram ∷ [SExpr Void] → IO Program
compileProgram sexprs = do
  result ← runExceptT (compile sexprs)
  case result of
    Right pair → return pair
    Left err → liftIO do
      putStrLn err
      exitFailure

time ∷ String → IO a → IO a
time label action = do
  start₁ ← getTime Monotonic
  start₂ ← getTime ProcessCPUTime
  result ← action
  end₁   ← getTime Monotonic
  end₂   ← getTime ProcessCPUTime
  printf "%s: [real] %0.6fs [process] %0.6fs\n"
    label
    (fromIntegral (toNanoSecs (diffTimeSpec start₁ end₁)) / 1000000000 ∷ Double)
    (fromIntegral (toNanoSecs (diffTimeSpec start₂ end₂)) / 1000000000 ∷ Double)
  hFlush stdout
  return result

verifyProgram ∷ (?config ∷ Config) ⇒ Bound → Natural → Solver V → Algorithm → Program → IO (Maybe [Stmt])
verifyProgram bound iters solver (Algorithm algorithm) (Program asserts (regex ∷ Regex (Index c))) = do
  start₁ ← getTime Monotonic
  start₂ ← getTime ProcessCPUTime

  isTripleCache ← newIORef OrdMap.empty
  isIndepCache  ← newIORef OrdMap.empty
  invalidCache  ← newIORef OrdSet.empty

  let isTriple' ∷ Expr V Bool → Stmt → Expr V Bool → IO Bool
      isTriple' φ s ψ = do
        isTripleCache₀ ← readIORef isTripleCache
        let key = (φ, s, ψ)
        case OrdMap.lookup key isTripleCache₀ of
          Just result → return result
          Nothing → do
            result ← isTriple solver φ (s) ψ
            writeIORef isTripleCache (OrdMap.insert key result isTripleCache₀)
            return result

      isIndep' ∷ Expr V Bool → Stmt → Stmt → IO Bool
      isIndep' φ s₁ s₂ = do
        isIndepCache₀ ← readIORef isIndepCache
        let key = (φ, s₁, s₂)
        case OrdMap.lookup key isIndepCache₀ of
          Just result → return result
          Nothing → do
            result ← isIndep solver φ s₁ s₂
            writeIORef isIndepCache (OrdMap.insert key result isIndepCache₀)
            return result

      program = canonical regex

  Interface initialize size check generalize display shrink ← return (algorithm (Solver' {..}) program)

  let loop π n = do
        when (iters /= 0 && n > iters) (error "Maximum iterations exceeded")

        putStrLn "------------------------------"
        printf "Iteration %d\n" n
        end₁   ← getTime Monotonic
        end₂   ← getTime ProcessCPUTime
        printf "Elapsed Time: [real] %0.6fs [process] %0.6fs\n"
          (fromIntegral (toNanoSecs (diffTimeSpec start₁ end₁)) / 1000000000 ∷ Double)
          (fromIntegral (toNanoSecs (diffTimeSpec start₂ end₂)) / 1000000000 ∷ Double)
        printf "Current proof size: %d\n" (size π)
        hFlush stdout

        bounded bound <$> time "Searching for counter-example" (evaluate (check π)) >>= \case
          []   → do
            π' ← if debug && minimize then shrink' π else return π
            display π'
            return (Nothing, n)
          cexs → do
            printf "Found %d counter-examples\n" (length cexs)
            when debug do
              for_ (zip cexs [0..]) \(cex, i ∷ Int) → do
                putStrLn ("[debug] ~~~ Counter-Example " <> pack (show i) <> " ~~~")
                for_ cex \x → do
                  putStr "        "
                  prettyPrint x

            time "Generating interpolants" (interpolate cexs) >>= \case
              Left bad → return (Just bad, n)
              Right φs → do
                π' ← time "Generalizing proof" (generalize φs π)
                loop π' (n + 1)

      shrink' π = do
        putStrLn "Shrinking..."
        hFlush stdout
        findM (null . bounded bound . check) (shrink π) >>= \case
          Nothing → return π
          Just π' → shrink' π'

      findM _ [] = return Nothing
      findM f (x:xs) = x >>= \y → if f y then return (Just y) else findM f xs

      interpolate ∷ [[Stmt]] → IO (Either [Stmt] [Assertions])
      interpolate = runExceptT . traverse \cex → do
        invalidCache₀ ← liftIO (readIORef invalidCache)
        if OrdSet.member cex invalidCache₀
        then return mempty
        else do
          result ← prove solver (NonEmpty.fromList cex)
          case result of
            Nothing | any isArtificial cex → do liftIO (writeIORef invalidCache (OrdSet.insert cex invalidCache₀))
                                                return mempty
                    | otherwise            → throwError cex
            Just π' → liftIO do
              for_ (zip3 (true:π') cex (π' ++ [false])) \(φ, x, ψ) →
                modifyIORef' isTripleCache (OrdMap.insert (φ, x, ψ) True)
              return (OrdSet.fromList π')

  π ← time "Initializing" (initialize (OrdSet.fromList (true : false : asserts)))

  (result, n) ← loop π 1
  printf "Iterations: %d\n" n
  hFlush stdout
  return result
