> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.TLT
> Copyright : (c) 2019 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is Tier-Based Locally Testable (TLT) by my own algorithm.
>
> @since 0.2
> -}
> module LTK.Decide.TLT (isTLT) where

> import LTK.Decide.LT (isLT)
> import LTK.FSA (FSA)
> import LTK.Tiers (project)

> -- |True iff the automaton recognizes a TLT stringset.
> isTLT :: (Ord n, Ord e) => FSA n e -> Bool
> isTLT = isLT . project
