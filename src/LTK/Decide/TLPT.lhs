> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.TLPT
> Copyright : (c) 2021-2024 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a syntactic
> semigroup \(S\) is tier-based locally Piecewise Testable (TLPT).
> This is the case iff its tier-projection is LPT.
>
> @since 1.0
> -}
> module LTK.Decide.TLPT (isTLPT, isTLPTM, isTLPTs) where

> import Data.Representation.FiniteSemigroup

> import LTK.FSA
> import LTK.Decide.LPT (isLPT, isLPTM, isLPTs)
> import LTK.Tiers (project)
> import LTK.Algebra (SynMon)

> -- |True iff the automaton recognizes a TLPT stringset.
> isTLPT :: (Ord n, Ord e) => FSA n e -> Bool
> isTLPT = isLPT . project

> -- |True iff the monoid recognizes a TLPT stringset.
> isTLPTM :: (Ord n, Ord e) => SynMon n e -> Bool
> isTLPTM = isLPTM . project

> -- |True iff the semigroup recognizes a TLPT stringset.
> --
> -- @since 1.2
> isTLPTs :: FiniteSemigroupRep s => s -> Bool
> isTLPTs = isLPTs . projectedSubsemigroup
