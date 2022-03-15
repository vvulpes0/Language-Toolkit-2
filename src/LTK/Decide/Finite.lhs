> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.Finite
> Copyright : (c) 2021 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is finite.  Also included for convenience is a test for cofiniteness.
>
> @since 1.0
> -}
> module LTK.Decide.Finite (isFinite, isCofinite) where

> import LTK.FSA
> import LTK.Traversals

> -- |True iff the automaton accepts only finitely many words.
> isFinite :: (Ord n, Ord e) => FSA n e -> Bool
> isFinite = isAcyclic . normalize

> -- |True iff the automaton accepts all but finitely many words.
> isCofinite :: (Ord n, Ord e) => FSA n e -> Bool
> isCofinite = isFinite . complement
