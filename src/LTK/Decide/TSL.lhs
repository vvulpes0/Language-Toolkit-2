> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.TSL
> Copyright : (c) 2019 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is Tier-Based Strictly Local (TSL) by my own algorithm.
>
> @since 0.2
> -}
> module LTK.Decide.TSL (isTSL) where

> import LTK.Decide.SL (isSL)
> import LTK.FSA (FSA)
> import LTK.Tiers (project)

> -- |True iff the automaton recognizes a TSL stringset.
> isTSL :: (Ord n, Ord e) => FSA n e -> Bool
> isTSL = isSL . project
