> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.Trivial
> Copyright : (c) 2022 Dakotah Lambert
> License   : MIT

> This module implements a test for whether a given FSA has only
> a single state.
> -}
> module LTK.Decide.Trivial (isTrivial) where

> import LTK.FSA
> import qualified Data.Set as Set

> -- |True iff the automaton has a single state.
> isTrivial :: (Ord n, Ord e) => FSA n e -> Bool
> isTrivial = (< 2) . Set.size . states
