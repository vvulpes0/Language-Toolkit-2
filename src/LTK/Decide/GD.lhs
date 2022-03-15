> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.GD
> Copyright : (c) 2021 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is Generalized Definite (GD) based on the semigroup characterization,
> or if it is Tier-Based Generalized Definite (TGD).
> -}
> module LTK.Decide.GD (isGD, isGDM, isTGD, isTGDM) where

> import qualified Data.Set as Set

> import LTK.FSA
> import LTK.Algebra
> import LTK.Tiers (project)

> -- |True iff the automaton recognizes a generalized definite stringset.
> isGD :: (Ord n, Ord e) => FSA n e -> Bool
> isGD = isGDM . syntacticMonoid

> -- |True iff the monoid satisfies \(eSe=e\) for all idempotents \(e\).
> isGDM :: (Ord n, Ord e) => SynMon n e -> Bool
> isGDM m = all ((== 1) . Set.size . ese m) . Set.toList $ idempotents m

> -- |True iff the language is generalized definite for some tier.
> isTGD :: (Ord n, Ord e) => FSA n e -> Bool
> isTGD = isGD . project

> -- |True iff the projected subsemigroup satisfies eSe=e
> isTGDM :: (Ord n, Ord e) => SynMon n e -> Bool
> isTGDM = isGDM . project
