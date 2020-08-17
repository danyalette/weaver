{-# LANGUAGE
  RecordWildCards,
  BlockArguments
#-}

module Data.Automata.FnDFA (FnDFA (..), difference, find, makeRegexDFA, explore, simplify, derive, findSym, findCanon) where 

import           Data.Automata.FnNFA (FnNFA (..))
import           Data.Automata.Regex (Regex (..))
import qualified Data.List as List
import           Data.List (intercalate, intersect, union)  
import qualified Data.Map as Map
import qualified Data.Set as Set 
import           Data.Set (toList, fromList)
import qualified Data.Sequence as Seq
import Debug.Trace (trace)

data FnDFA v e = FnDFA {
  states :: Set.Set v,
  alphabet :: Set.Set e,
  initial :: v,
  delta :: v -> e -> v,
  active :: v -> [e],
  final :: v -> Bool
}

difference :: (Ord a, Ord b, Ord c) => FnDFA a b -> FnDFA c b -> FnDFA (a, c) b
difference dfa1 dfa2 = (intersection dfa1 (complement dfa2))

-- Assume: dfa1 and dfa2 have the same alphabet
intersection :: (Ord a, Ord b, Ord c) => FnDFA a b -> FnDFA c b -> FnDFA (a, c) b
intersection dfa1 dfa2 =  case dfa1 of 
  (FnDFA states1 alphabet initial1 delta1 active1 final1) -> case dfa2 of 
      (FnDFA states2 _ initial2 delta2 active2 final2) -> 
            let states = Set.fromList [(q1, q2) | q1 <- Set.toList states1, q2 <- Set.toList states2]
                initial = (initial1, initial2)
                delta (q1, q2) stmt = (delta1 q1 stmt, delta2 q2 stmt)
                active (q1, q2) = intersect (active1 q1) (active2 q2)
                final (q1, q2) = final1 q1 && final2 q2
            in FnDFA {..}

complement :: FnDFA a b -> FnDFA a b
complement FnDFA {..} = FnDFA { final = not . final, .. }

find :: (Eq a, Ord a, Eq b, Ord b) => FnDFA a b -> Maybe [b]
find FnDFA {..} = do 
  let loop wordlst reach = 
                   let mfinal = List.find (\(_,q) -> final q) (toList nextWordlst)
                       (nextWordlst, nextReach) = foldl 
                                                    (\(wl, r) (w, q) -> foldl (\(wl',r') a -> 
                                                                             let nxt = delta q a
                                                                             in (if (Set.member nxt r') then (wl', r')
                                                                                else (Set.insert (w ++ [a], nxt) (Set.delete (w, q) wl') , Set.insert nxt r'))
                                                                              ) (wl, r) (active q)
                                                    )
                                                    (wordlst, reach) 
                                                    (toList wordlst)
                    in if (mfinal /= Nothing)
                           then mfinal
                           else if nextReach == reach then Nothing else (loop nextWordlst nextReach)
  res <- loop (Set.singleton ([], initial)) (Set.singleton initial)
  return (fst res)

findSym :: (Eq a, Ord a, Eq b, Ord b, Show a, Show b) => FnDFA a b -> (a -> a -> Bool) -> Maybe [b]
findSym (FnDFA {..}) sym = do 
  let loop wordlst reach = 
                   let mfinal = List.find (\(_,q) -> final q) (toList nextWordlst)
                       (nextWordlst, nextReach) = foldl 
                                                    (\(wl, r) (w, q) -> foldl (\(wl',r') a -> 
                                                                             let nxt = delta q a
                                                                             in (if (seen nxt r') then (wl', r')
                                                                                else (Set.insert (w ++ [a], nxt) (Set.delete (w, q) wl') , Set.insert nxt r'))
                                                                              ) (wl, r) (active q)
                                                    )
                                                    (wordlst, reach) 
                                                    (toList wordlst)
                    in if (mfinal /= Nothing)
                           then mfinal
                           else if nextReach == reach then Nothing else (loop nextWordlst nextReach)
  res <- loop (Set.singleton ([], initial)) (Set.singleton initial)
  return (fst res)
  where seen s reach = (Set.member s reach) || any (\s' -> sym s s') reach
  
findCanon :: (Eq a, Ord a, Eq b, Ord b, Ord c, Eq c) => FnDFA a b -> (a -> c) -> Maybe [b]
findCanon FnDFA {..} canon = do 
  let loop wordlst reach = 
                   let mfinal = List.find (\(_,q) -> final q) (toList nextWordlst)
                       (nextWordlst, nextReach) = foldl 
                                                    (\(wl, r) (w, q) -> foldl (\(wl',r') a -> 
                                                                             let nxt = delta q a
                                                                             in (if (Set.member (canon nxt) r') then (wl', r')
                                                                                else (Set.insert (w ++ [a], nxt) (Set.delete (w, q) wl') , Set.insert (canon nxt) r'))
                                                                              ) (wl, r) (active q)
                                                    )
                                                    (wordlst, reach) 
                                                    (toList wordlst)
                    in if (mfinal /= Nothing)
                           then mfinal
                           else if nextReach == reach then Nothing else (loop nextWordlst nextReach)
  res <- loop (Set.singleton ([], initial)) (Set.singleton (canon initial))
  return (fst res)
  
-- Brzozowski derivation
-- for creation of DFA from Regex 
-----------------------------------
-- source: 
--    Regular-expression derivatives reexamined (Owens, Reppy, Turon)

-- Generate DFA whoses states are regexes, from a regex, using Brzozowski derivation
makeRegexDFA :: (Ord a, Eq a, Show a) => Regex a -> FnDFA (Regex a) a
makeRegexDFA r' = FnDFA {..}
  where r = simplify r' 
        alphabet = getSymbols r
        (q', δ', a') = explore (Set.fromList [r]) alphabet Map.empty Map.empty r
        states = Set.delete Emp q'
        delta s e = case Map.lookup (s, e) δ' of 
          Nothing -> Emp
          Just q -> q
        active s = case Map.lookup s a' of 
          Nothing -> []
          Just l -> l
        final q = v q == Nil
        initial = r

-- Returns Nil if an expression is nullable i.e. recognizes Nil, and Emp otherwise
v :: Eq a => Regex a -> Regex a
v Emp = Emp 
v Nil = Nil 
v (Sym _) = Emp 
v (Alt r s) = if ((v r) == Nil) || ((v s) == Nil) then Nil else Emp
v (Cat r s) = if ((v r) == Nil) && ((v s) == Nil) then Nil else Emp
v (Par r s) = if ((v r) == Nil) && ((v s) == Nil) then Nil else Emp
v (Rep _) = Nil

-- Returns the derivation of a regular expression as per symbol <a>
derive :: Eq a => a -> Regex a -> Regex a
derive _ Emp = Emp 
derive _ Nil = Emp 
derive a (Sym b) = if a == b then Nil else Emp 
derive a (Alt r s) = Alt (derive a r) (derive a s)
derive a (Cat r s) = Alt (Cat (derive a r) s) (Cat (v r) (derive a s))
derive a (Par r s) = Alt (Par (derive a r) s) (Par r (derive a s))
derive a (Rep r) = Cat (derive a r) (Rep r)

-- Check equality of regular expressions (avoiding having Regex derive Eq)
eq :: Eq a => Regex a -> Regex a -> Bool 
eq = (==)

-- Simplify a regular expression. This function approximates a 
-- canonicalization function for equivalence classes of regular expressions. 
simplify :: (Ord a, Eq a, Show a) => Regex a -> Regex a
simplify Emp = Emp 
simplify Nil = Nil 
simplify (Sym a) = (Sym a) 
simplify (Alt Emp r) = simplify r 
simplify (Alt r Emp) = simplify r 
simplify (Cat Emp _) = Emp 
simplify (Cat _ Emp) = Emp
simplify (Cat Nil r) = simplify r
simplify (Cat r Nil) = simplify r
simplify (Rep Nil) = Nil 
simplify (Rep Emp) = Nil
simplify (Rep (Rep r)) = simplify (Rep r) 
simplify (Rep r) = if eq r r' then (Rep r') else simplify (Rep r')
  where r' = simplify r
simplify (Alt (Alt r s) t) = if (eq ss st) then (Alt r' s') else (Alt (simplify (Alt r' s')) st)
    where r' = if sr < ss then sr else ss 
          s' = if sr < ss then ss else sr
          sr = simplify r 
          ss = simplify s
          st = simplify t
simplify (Alt r s) = if (eq r' s') then r'
    else if ((not (eq r r')) || (not (eq s s'))) then simplify (Alt r' s')
                                   else (Alt r' s')
    where r' = if sr < ss then sr else ss 
          s' = if sr < ss then ss else sr
          sr = simplify r 
          ss = simplify s 
simplify (Cat r s) = if (not (eq r r') || not (eq s s')) then simplify (Cat r' s') else (Cat r' s')
    where r' = simplify r 
          s' = simplify s 
simplify (Par Nil s) = simplify s 
simplify (Par r Nil) = simplify r 
simplify (Par Emp s) = Emp 
simplify (Par r Emp) = Emp 
simplify (Par r s) = if (not (eq r sr) || not (eq s ss)) then simplify (Par r' s') else (Par r' s')
    where r' = if sr < ss then sr else ss 
          s' = if sr < ss then ss else sr
          sr = simplify r 
          ss = simplify s 

-- Check whether two regular expressions are approximately equivalent.  
-- This approximation, implemented in "simplify" above, is an implementation 
-- of (Owens, Reppy, Turon) regex similarity
-- This approximation is OK because 
--      "DFA construction is guaranteed to terminate if we use 
--       similarity as an approximation for equivalence"
equiv :: (Ord a, Eq a, Show a) => Regex a -> Regex a -> Bool 
equiv r s = eq (simplify r) (simplify s)

getSymbols :: (Ord a, Eq a) => Regex a -> Set.Set a
getSymbols r = foldl (\acc a -> Set.insert a acc) Set.empty r 

-- Generate all states and transitions for DFA of a regex 
explore :: (Ord a, Eq a, Show a) => Set.Set (Regex a) -> Set.Set a -> Map.Map ((Regex a), a) (Regex a) -> Map.Map (Regex a) [a] -> (Regex a) -> (Set.Set (Regex a), Map.Map ((Regex a), a) (Regex a), Map.Map (Regex a) [a])
explore states alphabet transitions active currState = Set.foldr (stepExplore currState) (states, transitions, active) alphabet
        where stepExplore curr a (s, t, act) = case (getEquiv nextState s) of
                                      Nothing -> explore s' alphabet t' act' nextState
                                            where s' = Set.insert nextState s 
                                                  t' = Map.insert (curr, a) nextState t
                                                  act' = if nextState == Emp then act else Map.insertWith union curr ([a]) act
                                      Just nextStateRep -> (s, t', act')
                                            where t' = Map.insert (curr, a) nextStateRep t
                                                  act' = if nextStateRep == Emp then act else Map.insertWith union curr ([a]) act
                        where nextState = simplify (derive a curr)

getEquiv :: (Ord a, Eq a, Show a) => Regex a -> Set.Set (Regex a) -> Maybe (Regex a)
getEquiv state states = case Set.toList (Set.filter (\s -> equiv s state) states) of 
    [] -> Nothing
    (x:_) -> Just x
