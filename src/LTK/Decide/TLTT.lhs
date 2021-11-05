> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.TLTT
> Copyright : (c) 2019-2021 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is Tier-Based Locally Threshold Testable (TLTT) by my own algorithm.
>
> @since 0.2
> -}
> module LTK.Decide.TLTT (isTLTT, isTLTTM) where

> import LTK.Decide.LTT (isLTT, isLTTM)
> import LTK.FSA (FSA)
> import LTK.Tiers (project)
> import LTK.Algebra (SynMon)

> -- |True iff the automaton recognizes a TLTT stringset.
> isTLTT :: (Ord n, Ord e) => FSA n e -> Bool
> isTLTT = isLTT . project

> -- |True iff the monoid recognizes a TLTT stringset.
> isTLTTM :: (Ord n, Ord e) => SynMon n e -> Bool
> isTLTTM = isLTTM . project
