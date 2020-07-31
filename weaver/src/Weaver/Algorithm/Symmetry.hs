{-# LANGUAGE
    BlockArguments,
    DeriveTraversable,
    FlexibleContexts,
    MonoLocalBinds,
    PatternSynonyms,
    ScopedTypeVariables,
    UnicodeSyntax
  #-}

module Weaver.Algorithm.Symmetry (algorithm, check) where

import           Data.Automata.DFA (DFA)
import qualified Data.Automata.Regex as Regex
import           Data.Finite.Container (Container, Index)
import           Data.Finite.Small.Map (Map)
import           Weaver.Algorithm (Algorithm (..), Interface (..))
import           Weaver.Algorithm.PartitionProgress (Proof, initialize, size, generalize, shrink)
import           Weaver.Algorithm.Normal (display)
import           Weaver.Counterexample (Counterexample (..))

algorithm ∷ Algorithm
algorithm = Algorithm \solver program → Interface
  (initialize solver)
  size
  (check (Regex.toDFA program))
  (generalize solver)
  (\(_, φs, _) → display φs)
  (shrink solver)

check ∷ ∀c a. Container c a ⇒ DFA (Map (Index c)) → Proof c -> Counterexample c
check programDFA (deps, _, πNFA) = error "Not Implemented"
