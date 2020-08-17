{-# LANGUAGE
  RecordWildCards
#-}

module Data.Automata.FnNFA (FnNFA (..)) where 
  
import Data.List (intercalate)  
import qualified Data.Set as Set 
import           Data.Set (toList)

data FnNFA v e = FnNFA {
  states :: Set.Set v,
  alphabet :: Set.Set e,
  initial :: v,
  delta :: v -> e -> Set.Set v,
  active :: v -> [e],
  final :: v -> Bool
}