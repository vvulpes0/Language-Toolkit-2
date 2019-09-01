> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.TLTT
> Copyright : (c) 2019 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is Tier-Based Locally Threshold Testable (TLTT) by my own algorithm.
> -}
> module LTK.Decide.TLTT (isTLTT) where

> import LTK.FSA (FSA)
> import LTK.Decide.LTT (isLTT)
> import LTK.Tiers (project)

> -- |True iff the automaton recognizes a TLT stringset.
> isTLTT :: (Ord n, Ord e) => FSA n e -> Bool
> isTLTT = isLTT . project
