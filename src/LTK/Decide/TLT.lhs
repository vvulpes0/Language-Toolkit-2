> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.TLT
> Copyright : (c) 2019,2021-2024 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is Tier-Based Locally Testable (TLT) by my own algorithm.
>
> @since 0.2
> -}
> module LTK.Decide.TLT (isTLT, isTLTM, isTLTs) where

> import Data.Representation.FiniteSemigroup

> import LTK.Decide.LT (isLT, isLTM, isLTs)
> import LTK.FSA (FSA)
> import LTK.Tiers (project)
> import LTK.Algebra (SynMon)

> -- |True iff the automaton recognizes a TLT stringset.
> isTLT :: (Ord n, Ord e) => FSA n e -> Bool
> isTLT = isLT . project

> -- |True iff the monoid recognizes a TLT stringset.
> --
> -- @since 1.0
> isTLTM :: (Ord n, Ord e) => SynMon n e -> Bool
> isTLTM = isLTM . project

> -- |True iff the semigroup recognizes a TLT stringset.
> --
> -- @since 1.2
> isTLTs :: FiniteSemigroupRep s => s -> Bool
> isTLTs = isLTs . projectedSubsemigroup
