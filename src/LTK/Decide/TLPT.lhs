> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.TLPT
> Copyright : (c) 2021 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a syntactic
> semigroup \(S\) is tier-based locally Piecewise Testable (TLPT).
> This is the case iff its tier-projection is LPT.
> -}
> module LTK.Decide.TLPT (isTLPT) where

> import qualified Data.Set as Set

> import LTK.FSA
> import LTK.Decide.LPT (isLPT)
> import LTK.Tiers (project)

> -- |True iff the automaton recognizes a TLPT stringset.
> isTLPT :: (Ord n, Ord e) => FSA n e -> Bool
> isTLPT = isLPT . project
