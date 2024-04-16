> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.B
> Copyright : (c) 2022-2024 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is in B, the subclass of FO2[<] where all elements are idempotent
> but the operation is not necessarily commutative.  Thus, this is
> a superclass of CB.  The local and tier-local extensions are also
> provided.
>
> @since 1.0
> -}
> module LTK.Decide.B ( isB, isBM, isLB, isLBM, isTLB, isTLBM
>                     , isBs, isLBs, isTLBs) where

> import Data.Representation.FiniteSemigroup

> import LTK.FSA
> import LTK.Algebra(SynMon)
> import LTK.Tiers (project)

> -- |True iff the automaton recognizes a band stringset.
> isB :: (Ord n, Ord e) => FSA n e -> Bool
> isB = isBs . syntacticSemigroup

> -- |True iff the monoid is a band.
> isBM :: (Ord n, Ord e) => SynMon n e -> Bool
> isBM = isB

> -- |True iff the semigroup is a band.
> --
> -- @since 1.2
> isBs :: FiniteSemigroupRep s => s -> Bool
> isBs = isBand

> -- |True iff the recognized stringset is locally a band.
> isLB :: (Ord n, Ord e) => FSA n e -> Bool
> isLB = isLBs . syntacticSemigroup

> -- |True iff the monoid is locally a band.
> isLBM :: (Ord n, Ord e) => SynMon n e -> Bool
> isLBM = isLB

> -- |True iff the semigroup is locally a band.
> --
> -- @since 1.2
> isLBs :: FiniteSemigroupRep s => s -> Bool
> isLBs = locally isBand

> -- |True iff the recognized stringset is locally a band on some tier.
> isTLB :: (Ord n, Ord e) => FSA n e -> Bool
> isTLB = isLB . project

> -- |True iff the monoid is locally a band on some tier.
> isTLBM :: (Ord n, Ord e) => SynMon n e -> Bool
> isTLBM = isLBM . project

> -- |True iff the semigroup is locally a band on some tier.
> --
> -- @since 1.2
> isTLBs :: FiniteSemigroupRep s => s -> Bool
> isTLBs = isLBs . projectedSubsemigroup
