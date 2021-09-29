> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.LPT
> Copyright : (c) 2021 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a syntactic
> semigroup \(S\) is locally Piecewise Testable (LPT).  This is the
> case iff each of its idempotents \(e\) satisfies the property that
> \(eSe\) is \(\mathcal{J}\)-trivial.
> -}
> module LTK.Decide.LPT (isLPT) where

> import qualified Data.Set as Set

> import LTK.FSA
> import LTK.Algebra

> -- |True iff the automaton recognizes an LPT stringset.
> isLPT :: (Ord n, Ord e) => FSA n e -> Bool
> isLPT f = all (jtriv . ese m) . Set.toList $ idempotents m
>     where m       = syntacticMonoid f
>           jcs     = Set.toList $ jEquivalence m
>           jtriv x = null . filter ((>1) . Set.size)
>                     $ map (Set.intersection x) jcs
