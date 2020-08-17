{-# LANGUAGE
    BlockArguments,
    FlexibleContexts,
    ImplicitParams,
    MonoLocalBinds,
    OverloadedStrings,
    ScopedTypeVariables,
    TupleSections,
    UnicodeSyntax
  #-}

module Weaver.Algorithm.SymmetryCanon where

import           Prelude hiding (lookup, putStr)
import           Control.Monad.State.Lazy (state, evalState)
import           Control.Monad.Writer (execWriter, tell)
import           Data.Automata.FnDFA (FnDFA (..), makeRegexDFA, difference, findCanon)
import           Data.Automata.Regex (Regex (..))
import           Data.Finite.Container (Container, Index, lookup)
import           Data.Foldable (foldl')
import           Data.List (elemIndex, sortOn, permutations, nub)
import qualified Data.Map as OrdMap
import           Data.Set (fromDistinctAscList, toAscList, toList, fromList)
import qualified Data.Set as OrdSet
import           Language.SMT.Expr (Expr, etraverse_, etraverse)
import           Weaver.Algorithm (Algorithm (..), Assertions, Solver' (..), Interface (..), proofToFnDFA)
import qualified Weaver.Algorithm.Normal as Normal
import           Weaver.Algorithm.Symmetry (allExprPerms, regexGetTIDs, stmtGetTIDs, exprGetTIDs, exprReplTIDsFn, regexReplTIDsFn, exprToSymbolic)
import           Weaver.Config (Config)
import           Weaver.Counterexample (Counterexample (..))
import qualified Weaver.Counterexample as C
import           Weaver.Program (Tag)
import           Weaver.Stmt (V, Stmt (..), threadID, withThreadID, ThreadID(..), straverse, straverse_)

algorithm ∷ Algorithm
algorithm = Algorithm \solver program → 
  let threadIDs = toList (regexGetTIDs program)
      dfa = makeRegexDFA program
  in Interface
  (initialize dfa solver threadIDs)
  size
  (check dfa threadIDs)
  (generalize dfa solver threadIDs)
  (\(φs, _) → Normal.display φs)
  (shrink dfa solver threadIDs)

type Proof c = (Assertions, FnDFA Assertions (Index c))

initialize ∷ ∀c. (Container c ([Tag], Stmt), ?config ∷ Config) ⇒ FnDFA (Regex (Index c)) (Index c) -> Solver' → [ThreadID] -> Assertions → IO (Proof c)
initialize _ solver threadIDs φs = do
  let φs' = foldl (\acc expr -> OrdSet.union acc (allExprPerms expr threadIDs)) φs φs
  π  <- ((proofToFnDFA solver φs') ::  (IO (FnDFA Assertions (Index c))))
  return (φs', π)

size ∷ Proof c → Int
size (φs, _) = length φs

check ∷ (Container c ([Tag], Stmt)) => FnDFA (Regex (Index c)) (Index c) → [ThreadID] -> Proof c -> Counterexample c
check program _ (_, πDFA) = case findCanon (difference program πDFA) stateToCanon of
                                               Nothing → mempty
                                               Just xs → C.singleton xs

generalize ∷ ∀c. (Container c ([Tag], Stmt), ?config ∷ Config) ⇒ FnDFA (Regex (Index c)) (Index c) -> Solver' → [ThreadID] -> [Assertions] → Proof c → IO (Proof c)
generalize dfa solver threadIDs φs' (φs, _) = initialize dfa solver threadIDs (foldl' (<>) φs φs')

shrink ∷ (?config ∷ Config, Container c ([Tag], Stmt)) ⇒ FnDFA (Regex (Index c)) (Index c) -> Solver' → [ThreadID] -> Proof c → [IO (Proof c)]
shrink dfa solver threadIDs (φs, _) = map (initialize dfa solver threadIDs . fromDistinctAscList) (deletes (toAscList φs))
  where deletes [] = []
        deletes (x:xs) = xs : map (x:) (deletes xs)
        
--------------------

stateToCanon :: ∀c. (Container c ([Tag], Stmt)) ⇒ (Regex (Index c), OrdSet.Set (Expr V Bool)) -> (Regex Stmt, [Expr V Bool])
stateToCanon (r, s) = (regexReplTIDsFn r perm, map (\e -> exprReplTIDsFn e perm) sortAssert) 
    where sortAssert = sortOn exprToSymbolic (OrdSet.toList s)
          tidsR = foldl (\acc ind -> (stmtGetTIDs (snd (lookup ind))) ++ acc) [] r 
          tidsA = foldl (\acc expr -> (exprGetTIDs expr) ++ acc) [] sortAssert
          permMap = OrdMap.fromList (zip (nub (tidsR ++ tidsA)) (map Symbolic [1..]))
          perm tid = case OrdMap.lookup tid permMap of 
              Nothing -> tid 
              Just t -> t