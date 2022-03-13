> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.B
> Copyright : (c) 2022 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is in B, the subclass of FO2[<] where all elements are idempotent
> but the operation is not necessarily commutative.  Thus, this is
> a superclass of CB.  The local and tier-local extensions are also
> provided.
> -}
> module LTK.Decide.B (isB, isBM, isLB, isLBM, isTLB, isTLBM) where

> import qualified Data.Set as Set

> import LTK.FSA
> import LTK.Algebra
> import LTK.Tiers (project)

> -- |True iff the automaton recognizes a band stringset.
> isB :: (Ord n, Ord e) => FSA n e -> Bool
> isB = isBM . syntacticMonoid

> -- |True iff the monoid is a band.
> isBM :: (Ord n, Ord e) => SynMon n e -> Bool
> isBM m = Set.union (initials m) (idempotents m) == states m

> -- |True iff the recognized stringset is locally a band.
> isLB :: (Ord n, Ord e) => FSA n e -> Bool
> isLB = isLBM . syntacticMonoid

> -- |True iff the monoid is locally a band.
> isLBM :: (Ord n, Ord e) => SynMon n e -> Bool
> isLBM m = allS f (states m)
>     where f x = Set.null (ese m x `Set.difference` i)
>           i = Set.union (initials m) (idempotents m)

> -- |True iff the recognized stringset is locally a band on some tier.
> isTLB :: (Ord n, Ord e) => FSA n e -> Bool
> isTLB = isLBM . syntacticMonoid . project

> -- |True iff the monoid is locally a band on some tier.
> isTLBM :: (Ord n, Ord e) => SynMon n e -> Bool
> isTLBM = isLBM . project
