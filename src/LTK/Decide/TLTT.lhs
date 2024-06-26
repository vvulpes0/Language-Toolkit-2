> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.TLTT
> Copyright : (c) 2019,2021-2024 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is Tier-Based Locally Threshold Testable (TLTT) by my own algorithm.
>
> @since 0.2
> -}
> module LTK.Decide.TLTT (isTLTT, isTLTTM, isTLTTs) where

> import Data.Representation.FiniteSemigroup

> import LTK.Decide.LTT (isLTT, isLTTM, isLTTs)
> import LTK.FSA (FSA)
> import LTK.Tiers (project)
> import LTK.Algebra (SynMon)

> -- |True iff the automaton recognizes a TLTT stringset.
> isTLTT :: (Ord n, Ord e) => FSA n e -> Bool
> isTLTT = isLTT . project

> -- |True iff the monoid recognizes a TLTT stringset.
> --
> -- @since 1.0
> isTLTTM :: (Ord n, Ord e) => SynMon n e -> Bool
> isTLTTM = isLTTM . project

> -- |True iff the semigroup recognizes a TLTT stringset.
> --
> -- @since 1.2
> isTLTTs :: FiniteSemigroupRep s => s -> Bool
> isTLTTs = isLTTs . projectedSubsemigroup
