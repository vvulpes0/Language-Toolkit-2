> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.CB
> Copyright : (c) 2021-2024 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is in CB, the subclass of PT where additionally all elements of
> the syntactic monoid are idempotent. This is additionally a subclass
> of LT, because every submonoid of a semilattice remains a semilattice.
>
> @since 1.0
> -}
> module LTK.Decide.CB (isCB, isCBM, isCBs) where

> import Data.Representation.FiniteSemigroup

> import LTK.FSA
> import LTK.Algebra(SynMon)

> -- |True iff the automaton recognizes a semilattice stringset.
> isCB :: (Ord n, Ord e) => FSA n e -> Bool
> isCB = isCBs . syntacticSemigroup

> -- |True iff the monoid is a semilattice.
> isCBM :: (Ord n, Ord e) => SynMon n e -> Bool
> isCBM = isCB

> -- |True iff the semigroup is a semilattice.
> --
> -- @since 1.2
> isCBs :: FiniteSemigroupRep s => s -> Bool
> isCBs = both isJTrivial isBand
