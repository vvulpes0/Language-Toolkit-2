> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.LT
> Copyright : (c) 2019,2021-2023 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is Locally Testable (LT) based on the semigroup characterization
> of Brzozowski and Simon from their 1973 work
> "Characterizations of locally testable events".
>
> @since 0.2
> -}
> module LTK.Decide.LT (isLT, isLTM, isLTs) where

> import Data.Representation.FiniteSemigroup

> import LTK.FSA
> import LTK.Algebra(SynMon)

> -- |True iff the automaton recognizes an LT stringset.
> isLT :: (Ord n, Ord e) => FSA n e -> Bool
> isLT = isLTs . syntacticSemigroup

A semigroup (S) [e.g. the syntactic semigroup] is locally testable iff
for all idempotent e, the generated subsemigroup eSe is an idempotent
commutative monoid.

> -- |True iff the given monoid is locally a semilattice.
> --
> -- @since 1.0
> isLTM :: (Ord n, Ord e) => SynMon n e -> Bool
> isLTM = isLT

> -- |True iff the given semigroup is locally a semilattice.
> isLTs :: FiniteSemigroupRep s => s -> Bool
> isLTs = locally (both isJTrivial isBand)
