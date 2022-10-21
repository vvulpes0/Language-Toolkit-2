> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.Finite
> Copyright : (c) 2021-2022 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is finite.  Also included for convenience is a test for cofiniteness.
>
> @since 1.0
> -}
> module LTK.Decide.Finite ( isFinite, isFiniteM
>                          , isCofinite, isCofiniteM
>                          , isTFinite, isTFiniteM
>                          , isTCofinite, isTCofiniteM
>                          ) where

> import LTK.FSA
> import LTK.Algebra
> import LTK.Tiers (project)
> import LTK.Decide.PT (isPTM)

> -- |True iff the automaton accepts only finitely many words.
> isFinite :: (Ord n, Ord e) => FSA n e -> Bool
> isFinite = isFiniteM . syntacticMonoid

> -- |True iff the automaton accepts all but finitely many words.
> isCofinite :: (Ord n, Ord e) => FSA n e -> Bool
> isCofinite = isCofiniteM . syntacticMonoid

> -- |True iff the syntactic monoid is nilpotent
> -- and the sole idempotent is rejecting
> isFiniteM :: (Ord n, Ord e) => SynMon n e -> Bool
> isFiniteM s = isPTM s && (size i == 1) && not (isSubsetOf (finals s) i)
>     where i = idempotents s

> -- |True iff the syntactic monoid is nilpotent
> -- and the sole idempotent is accepting
> isCofiniteM :: (Ord n, Ord e) => SynMon n e -> Bool
> isCofiniteM s = isPTM s && (size i == 1) && isSubsetOf (finals s) i
>     where i = idempotents s

> -- |True iff the automaton is finite on a tier.
> isTFinite :: (Ord n, Ord e) => FSA n e -> Bool
> isTFinite = isFinite . project

> -- |True iff the syntactic monoid is nilpotent without its identity,
> -- and the sole other idempotent is rejecting
> isTFiniteM :: (Ord n, Ord e) => SynMon n e -> Bool
> isTFiniteM = isFiniteM . project

> -- |True iff the automaton is cofinite on a tier.
> isTCofinite :: (Ord n, Ord e) => FSA n e -> Bool
> isTCofinite = isCofinite . project

> -- |True iff the syntactic monoid is nilpotent without its identity,
> -- and the sole other idempotent is accepting
> isTCofiniteM :: (Ord n, Ord e) => SynMon n e -> Bool
> isTCofiniteM = isCofiniteM . project
