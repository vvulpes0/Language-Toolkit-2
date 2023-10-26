> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.LPT
> Copyright : (c) 2021-2023 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a syntactic
> semigroup \(S\) is locally Piecewise Testable (LPT).  This is the
> case iff each of its idempotents \(e\) satisfies the property that
> \(eSe\) is \(\mathcal{J}\)-trivial.
>
> @since 1.0
> -}
> module LTK.Decide.LPT (isLPT, isLPTM, isLPTs) where

> import Data.Representation.FiniteSemigroup

> import LTK.FSA
> import LTK.Algebra

> -- |True iff the automaton recognizes an LPT stringset.
> isLPT :: (Ord n, Ord e) => FSA n e -> Bool
> isLPT = isLPTs . syntacticSemigroup

> -- |True iff the monoid is locally \(\mathcal{J}\)-trivial.
> isLPTM :: (Ord n, Ord e) => SynMon n e -> Bool
> isLPTM = isLPT

> -- |True iff the semigroup is locally \(\mathcal{J}\)-trivial.
> isLPTs :: FiniteSemigroupRep s => s -> Bool
> isLPTs = locally isJTrivial
