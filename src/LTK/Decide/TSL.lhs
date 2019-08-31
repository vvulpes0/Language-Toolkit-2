> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.TSL
> Copyright : (c) 2019 Dakotah Lambert
> License   : BSD-style, see LICENSE

> This module implements an algorithm to decide whether a given FSA
> is Tier-Based Strictly Local (TSL) by my own algorithm.
> -}
> module LTK.Decide.TSL (isTSL) where

> import LTK.FSA (FSA)
> import LTK.Decide.SL (isSL)
> import LTK.Tiers (project)

> -- |True iff the automaton recognizes a TSL stringset.
> isTSL :: (Ord n, Ord e) => FSA n e -> Bool
> isTSL = isSL . project
