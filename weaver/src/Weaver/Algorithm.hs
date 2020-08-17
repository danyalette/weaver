{-# LANGUAGE
    BlockArguments,
    DeriveTraversable,
    FlexibleContexts,
    GADTs,
    ImplicitParams,
    LambdaCase,
    OverloadedLists,
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

module Weaver.Algorithm where

import           Prelude hiding (lookup, putStrLn, readFile)
import           Control.Monad (filterM, liftM, foldM)
import           Data.Automata.Graph (GraphM (..))
import           Data.Automata.NFA (NFAM, Edge (..))
import           Data.Automata.FnDFA (FnDFA (..))
import qualified Data.Automata.FnDFA as FnDFA
import           Data.Automata.FnNFA (FnNFA (..))
import qualified Data.Automata.FnNFA as FnNFA
import           Data.Automata.Regex (Regex)
import           Data.Finite.Class (universe)
import           Data.Finite.Container (Container, Index, lookup, reify)
import qualified Data.Finite.Set as Set
import           Data.Finite.Small.Map (Map)
import qualified Data.Finite.Small.Map as Map
import           Data.List (union)
import qualified Data.Map as OrdMap
import           Data.Set (Set, (\\))
import qualified Data.Set as OrdSet
import           Language.SMT.Expr (Expr, true, false)
import           Weaver.Program (Tag)
import           Weaver.Stmt (V, Stmt)
import           Weaver.Config
import           Weaver.Counterexample

type Assertions = Set (Expr V Bool)

data Solver' = Solver'
  { isTriple' ∷ Expr V Bool → Stmt → Expr V Bool → IO Bool
  , isIndep'  ∷ Expr V Bool → Stmt → Stmt → IO Bool
  }

newtype Algorithm = Algorithm (∀c.
  (Container c ([Tag], Stmt), ?config ∷ Config) ⇒
  Solver' →
  Regex (Index c) →
  Interface c)

data Interface c = ∀π. Interface
  (Assertions → IO π)       -- Initialize
  (π → Int)                 -- Size
  (π → Counterexample c)    -- Check
  ([Assertions] → π → IO π) -- Generalize
  (π → IO ())               -- Display
  (π → [IO π])              -- Shrink

proofToNFA ∷ Container c ([Tag], Stmt) ⇒ Solver' → Assertions → NFAM IO (Map (Index c))
proofToNFA (Solver' {..}) π = reify πlist \π'@(root:final:_) →
  let stmts  = universe
      next φ = do
        δ ← mapM (\s → (s,) <$> filterM (isTriple' (lookup φ) (snd (lookup s)) . lookup) π') stmts
        let δ' = map (fmap Set.fromList) (filter (not . null . snd) δ)
        return (Edge (Map.fromList δ') (φ == final))
  in UnfoldM next root
  where πlist = true : false : OrdSet.toList (π \\ [true, false])

proofToFnNFA :: Container c ([Tag], Stmt) ⇒ Solver' → Assertions -> IO (FnNFA (Expr V Bool) (Index c))
proofToFnNFA (Solver' {..}) π = reify πlist \π' →
    let states = OrdSet.fromList (map lookup π')
        alphabet = OrdSet.fromList universe
        initial = true
        final = (==) false
        tripsToMaps triples = foldl fn (OrdMap.empty, OrdMap.empty) triples
          where fn (dm,actm) (a, b, c) = (OrdMap.insertWith OrdSet.union (a, b) (OrdSet.singleton c) dm,
                                          OrdMap.insertWith union a [b] actm
                                          )
        mkDelta triples assrt stmt  = foldl fn OrdSet.empty triples
                              where fn acc (a, b, c) = if a == assrt && b == stmt then (OrdSet.insert c acc) else acc
        in do 
            triples <- filterLiftTriples [(a, b, c, (isTriple' a (mkStmt b) c)) | a <- (map lookup π'), b <- universe, c <- (map lookup π')]
            let (dMap, actMap) = tripsToMaps triples 
            let delta a s = case OrdMap.lookup (a, s) dMap of 
                              Just l -> l 
                              Nothing -> OrdSet.empty
            let active a = case OrdMap.lookup a actMap of 
                              Just l -> l 
                              Nothing -> []
            return FnNFA {..}
          where πlist = true : false : OrdSet.toList (π \\ [true, false])
                mkStmt i = snd (lookup i)
                filterLiftTriples :: [(a, b, c, IO Bool)] -> IO [(a, b, c)]
                filterLiftTriples [] = return [] 
                filterLiftTriples ((a, b, c, d'):xs) = do 
                  d <- d' 
                  rest <- filterLiftTriples xs
                  if d then return ((a, b, c):rest) else return rest 

proofToFnDFA :: ∀c. (Container c ([Tag], Stmt)) ⇒ Solver' → Assertions -> IO (FnDFA Assertions (Index c))
proofToFnDFA solver π = do
    nfa <- ((proofToFnNFA solver π) ::  (IO (FnNFA (Expr V Bool) (Index c))))
    let states = OrdSet.powerSet (FnNFA.states nfa) \\ (OrdSet.insert OrdSet.empty OrdSet.empty)
        initial = OrdSet.fromList [true]
        alphabet = FnNFA.alphabet nfa
        final q = OrdSet.member false q
        active assertions = OrdSet.foldl fn [] assertions
          where fn acc assertion = union acc ((FnNFA.active nfa) assertion)
        delta assertions stmt = OrdSet.foldl fn OrdSet.empty assertions
          where fn acc assertion = OrdSet.union acc ((FnNFA.delta nfa) assertion stmt)
    return FnDFA {..}