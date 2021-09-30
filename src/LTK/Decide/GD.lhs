> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.GD
> Copyright : (c) 2021 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is Generalized Definite (GD) based on the semigroup characterization,
> or if it is Tier-Based Generalized Definite (TGD).
> -}
> module LTK.Decide.GD (isGD, isTGD) where

> import Data.Set (Set)
> import qualified Data.Set as Set

> import LTK.FSA
> import LTK.Algebra
> import LTK.Tiers (project)

> -- |True iff the automaton recognizes a generalized definite stringset.
> isGD :: (Ord n, Ord e) => FSA n e -> Bool
> isGD f = all ((== 1) . Set.size . ese m) . Set.toList $ idempotents m
>     where m = syntacticMonoid f

> -- |True iff the language is generalized definite for some tier.
> isTGD :: (Ord n, Ord e) => FSA n e -> Bool
> isTGD = isGD . project
