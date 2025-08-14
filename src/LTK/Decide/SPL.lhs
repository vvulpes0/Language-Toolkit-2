> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.SPL
> Copyright : (c) 2025 Dakotah Lambert
> License   : MIT

> A language is strictly piecewise-local if whenever
> a word w is accepted, and a word u has the same subsequences
> of length up to j of substrings of length up to k
> (i.e. generalized j,k-subsequences),
> then u, too, must be accepted.
> -}
> module LTK.Decide.SPL (isSPL, isSPLM, isSPLs) where

> import Data.Representation.FiniteSemigroup

> import LTK.FSA
> import LTK.Algebra(SynMon)

> -- |True iff the language is strictly piecewise-local,
> -- characterized by a set of forbidden subsequences of substrings.
> --
> -- @since 1.3
> isSPL :: (Ord n, Ord e) => FSA n e -> Bool
> isSPL = isSPLs . syntacticOSemigroup

> -- |True iff the language is strictly piecewise-local,
> -- characterized by a set of forbidden subsequences of substrings.
> --
> -- @since 1.3
> isSPLM :: (Ord n, Ord e) => SynMon n e -> Bool
> isSPLM = isSPL

> -- |True iff the semigroup satisifes
> -- \(x^{\omega}\leq x^{\omega}yx^{\omega}\).
> --
> -- @since 1.3
> isSPLs :: FiniteSemigroupRep s => OrderedSemigroup s -> Bool
> isSPLs s = maybe False id $ isVariety "[x*<x*yx*]" s
