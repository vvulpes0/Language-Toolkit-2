> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.PT
> Copyright : (c) 2019 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is Piecewise Testable (PT) based on the semigroup characterization
> of Simon from his 1975 work "Piecewise testable events".
> -}
> module LTK.Decide.PT (isPT) where

> import LTK.FSA

> -- |True iff the automaton recognizes a PT stringset.
> isPT :: (Ord n, Ord e) => FSA n e -> Bool
> isPT = trivialUnder jEquivalence . syntacticMonoid
