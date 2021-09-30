> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.CB
> Copyright : (c) 2021 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is in CB, the subclass of PT where additionally all elements of
> the syntactic monoid are idempotent. This is additionally a subclass
> of LT, because every submonoid of a semilattice remains a semilattice.
> -}
> module LTK.Decide.CB (isCB) where

> import qualified Data.Set as Set

> import LTK.FSA
> import LTK.Algebra

> -- |True iff the automaton recognizes a semilattice stringset.
> isCB :: (Ord n, Ord e) => FSA n e -> Bool
> isCB f = trivialUnder jEquivalence m && (i == states m)
>     where m = syntacticMonoid f
>           i = Set.union (initials m) (idempotents m)
