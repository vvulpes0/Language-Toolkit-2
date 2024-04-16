> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.PT
> Copyright : (c) 2019,2021-2024 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is Piecewise Testable (PT) based on the semigroup characterization
> of Simon from his 1975 work "Piecewise testable events".
>
> @since 0.2
> -}
> module LTK.Decide.PT (isPT, isPTM, isPTs) where

> import Data.Representation.FiniteSemigroup

> import LTK.FSA
> import LTK.Algebra(SynMon)

> -- |True iff the automaton recognizes a PT stringset.
> isPT :: (Ord n, Ord e) => FSA n e -> Bool
> isPT = isPTs . syntacticSemigroup

> -- |True iff the monoid is \(\mathcal{J}\)-trivial
> --
> -- @since 1.0
> isPTM :: (Ord n, Ord e) => SynMon n e -> Bool
> isPTM = trivialUnder jEquivalence

> -- |True iff the semigroup is \(\mathcal{J}\)-trivial
> --
> -- @since 1.2
> isPTs :: FiniteSemigroupRep s => s -> Bool
> isPTs = isJTrivial
