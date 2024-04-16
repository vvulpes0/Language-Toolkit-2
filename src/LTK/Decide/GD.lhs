> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.GD
> Copyright : (c) 2021-2024 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is Generalized Definite (GD) based on the semigroup characterization,
> or if it is Tier-Based Generalized Definite (TGD).
>
> @since 1.0
> -}
> module LTK.Decide.GD (isGD, isGDM, isGDs, isTGD, isTGDM, isTGDs) where

> import Data.Representation.FiniteSemigroup

> import LTK.FSA
> import LTK.Algebra(SynMon)
> import LTK.Tiers (project)

> -- |True iff the automaton recognizes a generalized definite stringset.
> isGD :: (Ord n, Ord e) => FSA n e -> Bool
> isGD = isGDs . syntacticSemigroup

> -- |True iff the monoid satisfies \(eSe=e\) for all idempotents \(e\),
> -- except the identity if it is not instantiated.
> isGDM :: (Ord n, Ord e) => SynMon n e -> Bool
> isGDM = isGD

> -- |True iff the semigroup satisfies \(eSe=e\)
> -- for all idempotents \(e\).
> --
> -- @since 1.2
> isGDs :: FiniteSemigroupRep s => s -> Bool
> isGDs = locally isTrivial

> -- |True iff the language is generalized definite for some tier.
> isTGD :: (Ord n, Ord e) => FSA n e -> Bool
> isTGD = isGD . project

> -- |True iff the projected subsemigroup satisfies eSe=e
> isTGDM :: (Ord n, Ord e) => SynMon n e -> Bool
> isTGDM = isGDM . project

> -- |True iff the projected subsemigroup satisfies eSe=e
> --
> -- @since 1.2
> isTGDs :: FiniteSemigroupRep s => s -> Bool
> isTGDs = isGDs . projectedSubsemigroup
