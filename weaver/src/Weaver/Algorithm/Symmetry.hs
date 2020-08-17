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

module Weaver.Algorithm.Symmetry (algorithm, allExprPerms, regexGetTIDs, stmtGetTIDs, exprGetTIDs, exprReplTIDsFn, regexReplTIDsFn, exprToSymbolic) where

import           Prelude hiding (lookup, putStr)
import           Control.Monad.State.Lazy (state, evalState)
import           Control.Monad.Writer (execWriter, tell)
import qualified Data.Automata.FnDFA as FnDFA
import           Data.Automata.FnDFA (FnDFA (..), makeRegexDFA, difference, findSym)
import           Data.Automata.Regex (Regex (..))
import           Data.Finite.Container (Container, Index, lookup)
import           Data.Foldable (foldl')
import           Data.List (permutations, elemIndex, nub, delete)
import qualified Data.Map as OrdMap
import           Data.Set (fromDistinctAscList, toAscList, toList, fromList)
import qualified Data.Set as OrdSet
import           Language.SMT.Expr (Expr, etraverse, etraverse_)
import           Weaver.Algorithm (Algorithm (..), Assertions, Solver' (..), Interface (..), proofToFnDFA)
import qualified Weaver.Algorithm.Normal as Normal
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
check program threadIDs (_, πDFA) = case findSym dfa sym of
                                               Nothing → mempty
                                               Just xs → C.singleton xs
          where dfa = difference program πDFA
                sts = OrdSet.toList (FnDFA.states dfa)
                tids = delete Root threadIDs
                permFns = getAllPermFns tids
                sym (r1, a1) (r2, a2)  = any (\fn -> fmap (snd . lookup) r1 == regexReplTIDsFn r2 fn && a1 == OrdSet.map (\e -> exprReplTIDsFn e fn) a2) permFns

generalize ∷ ∀c. (Container c ([Tag], Stmt), ?config ∷ Config) ⇒ FnDFA (Regex (Index c)) (Index c) -> Solver' → [ThreadID] -> [Assertions] → Proof c → IO (Proof c)
generalize dfa solver threadIDs φs' (φs, _) = initialize dfa solver threadIDs (foldl' (<>) φs φs')

shrink ∷ (?config ∷ Config, Container c ([Tag], Stmt)) ⇒ FnDFA (Regex (Index c)) (Index c) -> Solver' → [ThreadID] -> Proof c → [IO (Proof c)]
shrink dfa solver threadIDs (φs, _) = map (initialize dfa solver threadIDs . fromDistinctAscList) (deletes (toAscList φs))
  where deletes [] = []
        deletes (x:xs) = xs : map (x:) (deletes xs)
        
--------------------
                        
exprToSymbolic :: Expr V Bool -> Expr V Bool
exprToSymbolic expr = exprReplTIDs expr (map tidToSymbolic threadIDs)
  where threadIDs = exprGetTIDs expr
        tidToSymbolic tid = case elemIndex tid (nub threadIDs)
                              of Just n -> Symbolic n 
                                 Nothing -> error "Thread ID is not in list of thread IDs."

exprGetTIDs :: Expr V Bool -> [ThreadID]
exprGetTIDs expr = execWriter (etraverse_ (\v -> tell [threadID v]) expr)

exprReplTIDs :: Expr V Bool -> [ThreadID] -> Expr V Bool
exprReplTIDs expr thrLst = evalState (etraverse (\v -> state (\(x:xs) -> (withThreadID x v, xs))) expr) thrLst

exprReplTIDsFn :: Expr V Bool -> (ThreadID -> ThreadID) -> Expr V Bool
exprReplTIDsFn expr f = evalState (etraverse (\v -> state (\(_:xs) -> (withThreadID (f (threadID v)) v, xs))) expr) [(1::Integer)..]

stmtReplTIDsFn :: Stmt -> (ThreadID -> ThreadID) -> Stmt
stmtReplTIDsFn stmt f = evalState (straverse (\v -> state (\(_:xs) -> (withThreadID (f (threadID v)) v, xs))) stmt) [(1::Integer)..]

regexReplTIDsFn :: (Container c ([Tag], Stmt)) => Regex (Index c) -> (ThreadID -> ThreadID) -> Regex Stmt
regexReplTIDsFn r f = fmap (\ind -> stmtReplTIDsFn (snd (lookup ind)) f) r

getAllPermFns :: Ord a => [a] -> [a -> a]
getAllPermFns tids = map (\p -> permToFn p tids) (permutations tids)

permToFn :: Ord p => [p] -> [p] -> p -> p
permToFn perm orig tid = case OrdMap.lookup tid (OrdMap.fromList (zip orig perm)) of 
                      Nothing -> tid 
                      Just t -> t 

allExprPerms :: Expr V Bool -> [ThreadID] -> OrdSet.Set (Expr V Bool)
allExprPerms expr threadIDs = fromList (map (\fn -> exprReplTIDsFn expr fn) (getAllPermFns threadIDs))

stmtGetTIDs :: Stmt -> [ThreadID]
stmtGetTIDs stmt = execWriter (straverse_ (\v -> tell [threadID v]) stmt)
                              
regexGetTIDs :: (Container c ([Tag], Stmt)) => Regex (Index c) -> OrdSet.Set ThreadID
regexGetTIDs regex = foldl 
                        (\acc ind -> 
                            let stmt = snd (lookup ind) 
                            in OrdSet.union acc (OrdSet.fromList (stmtGetTIDs stmt))) 
                        OrdSet.empty regex 


                              