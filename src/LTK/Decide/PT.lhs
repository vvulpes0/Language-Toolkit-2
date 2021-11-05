> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.PT
> Copyright : (c) 2019-2021 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is Piecewise Testable (PT) based on the semigroup characterization
> of Simon from his 1975 work "Piecewise testable events".
>
> @since 0.2
> -}
> module LTK.Decide.PT (isPT, isPTM) where

> import LTK.FSA
> import LTK.Algebra

> -- |True iff the automaton recognizes a PT stringset.
> isPT :: (Ord n, Ord e) => FSA n e -> Bool
> isPT = isPTM . syntacticMonoid

> -- |True iff the monoid is \(\mathcal{J}\)-trivial
> isPTM :: (Ord n, Ord e) => SynMon n e -> Bool
> isPTM = trivialUnder jEquivalence
