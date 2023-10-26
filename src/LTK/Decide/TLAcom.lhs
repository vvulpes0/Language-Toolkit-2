> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.TLAcom
> Copyright : (c) 2022-2023 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is Tier-Based Locally Acom (TLAcom) by my own algorithm.
>
> @since 1.1
> -}
> module LTK.Decide.TLAcom (isTLAcom, isTLAcomM, isTLAcoms) where

> import Data.Representation.FiniteSemigroup

> import LTK.Decide.LAcom (isLAcom, isLAcomM, isLAcoms)
> import LTK.FSA (FSA)
> import LTK.Tiers (project)
> import LTK.Algebra (SynMon)

> -- |True iff the automaton recognizes a TLAcom stringset.
> isTLAcom :: (Ord n, Ord e) => FSA n e -> Bool
> isTLAcom = isLAcom . project

> -- |True iff the monoid recognizes a TLAcom stringset.
> isTLAcomM :: (Ord n, Ord e) => SynMon n e -> Bool
> isTLAcomM = isLAcomM . project

> -- |True iff the semigroup recognizes a TLAcom stringset.
> isTLAcoms :: FiniteSemigroupRep s => s -> Bool
> isTLAcoms = isLAcoms . projectedSubsemigroup
