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

module Weaver.Algorithm.SymmetryClosed where

import           Prelude hiding (lookup, putStr)
import           Data.Automata.FnDFA (FnDFA (..), makeRegexDFA, difference, find)
import           Data.Automata.Regex (Regex (..))
import           Data.Finite.Container (Container, Index)
import           Data.Foldable (foldl')
import           Data.Set (fromDistinctAscList, toAscList, toList)
import qualified Data.Set as OrdSet
import           Weaver.Algorithm (Algorithm (..), Assertions, Solver' (..), Interface (..), proofToFnDFA)
import qualified Weaver.Algorithm.Normal as Normal
import           Weaver.Algorithm.Symmetry (allExprPerms, regexGetTIDs)
import           Weaver.Config (Config)
import           Weaver.Counterexample (Counterexample (..))
import qualified Weaver.Counterexample as C
import           Weaver.Program (Tag)
import           Weaver.Stmt (Stmt (..), ThreadID(..))

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
check program _ (_, πDFA) = case find (difference program πDFA) of
                                               Nothing → mempty
                                               Just xs → C.singleton xs

generalize ∷ ∀c. (Container c ([Tag], Stmt), ?config ∷ Config) ⇒ FnDFA (Regex (Index c)) (Index c) -> Solver' → [ThreadID] -> [Assertions] → Proof c → IO (Proof c)
generalize dfa solver threadIDs φs' (φs, _) = initialize dfa solver threadIDs (foldl' (<>) φs φs')

shrink ∷ (?config ∷ Config, Container c ([Tag], Stmt)) ⇒ FnDFA (Regex (Index c)) (Index c) -> Solver' → [ThreadID] -> Proof c → [IO (Proof c)]
shrink dfa solver threadIDs (φs, _) = map (initialize dfa solver threadIDs . fromDistinctAscList) (deletes (toAscList φs))
  where deletes [] = []
        deletes (x:xs) = xs : map (x:) (deletes xs)
        