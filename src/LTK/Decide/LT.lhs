> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.LT
> Copyright : (c) 2019,2021-2022 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is Locally Testable (LT) based on the semigroup characterization
> of Brzozowski and Simon from their 1973 work
> "Characterizations of locally testable events".
>
> @since 0.2
> -}
> module LTK.Decide.LT (isLT, isLTM) where

> import qualified Data.Set as Set

> import LTK.FSA
> import LTK.Algebra

> -- |True iff the automaton recognizes an LT stringset.
> isLT :: (Ord n, Ord e) => FSA n e -> Bool
> isLT = isLTM . syntacticMonoid

A semigroup (S) [e.g. the syntactic semigroup] is locally testable iff
for all idempotent e, the generated subsemigroup eSe is an idempotent
commutative monoid.

> -- |True iff the given monoid is locally a semilattice.
> --
> -- @since 1.0
> isLTM :: (Ord n, Ord e) => SynMon n e -> Bool
> isLTM s = all (both (isCommutative s) (isSubsetOf i) . ese s)
>           . Set.toList $ i
>     where i = idempotents s
