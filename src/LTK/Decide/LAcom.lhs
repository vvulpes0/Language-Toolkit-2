> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.LAcom
> Copyright : (c) 2019-2023 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> has a syntactic semigroup which is Locally Commutative and Aperiodic,
> a near superclass of the Locally Threshold Testable languages.
>
> @since 1.1
> -}
> module LTK.Decide.LAcom (isLAcom, isLAcomM, isLAcoms) where

> import Data.Representation.FiniteSemigroup

> import LTK.FSA
> import LTK.Algebra(SynMon)

> -- |True iff the automaton recognizes a LAcom stringset.
> isLAcom :: (Ord n, Ord e) => FSA n e -> Bool
> isLAcom = isLAcoms . syntacticSemigroup

> -- |True iff the monoid recognizes a LAcom stringset.
> isLAcomM :: (Ord n, Ord e) => SynMon n e -> Bool
> isLAcomM = isLAcom

> -- |True iff the semigroup recognizes a LAcom stringset.
> isLAcoms :: FiniteSemigroupRep s => s -> Bool
> isLAcoms = locally (both isAperiodic isCommutative)
