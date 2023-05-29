> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.TLPT
> Copyright : (c) 2021-2022 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a syntactic
> semigroup \(S\) is tier-based locally Piecewise Testable (TLPT).
> This is the case iff its tier-projection is LPT.
>
> @since 1.0
> -}
> module LTK.Decide.TLPT (isTLPT, isTLPTM) where

> import LTK.FSA
> import LTK.Decide.LPT (isLPT, isLPTM)
> import LTK.Tiers (project)
> import LTK.Algebra (SynMon)

> -- |True iff the automaton recognizes a TLPT stringset.
> isTLPT :: (Ord n, Ord e) => FSA n e -> Bool
> isTLPT = isLPT . project

> -- |True iff the monoid recognizes a TLPT stringset.
> isTLPTM :: (Ord n, Ord e) => SynMon n e -> Bool
> isTLPTM = isLPTM . project
