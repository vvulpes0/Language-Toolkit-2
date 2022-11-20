> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.TLAcom
> Copyright : (c) 2022 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is Tier-Based Locally Acom (TLAcom) by my own algorithm.
> -}
> module LTK.Decide.TLAcom (isTLAcom, isTLAcomM) where

> import LTK.Decide.LAcom (isLAcom, isLAcomM)
> import LTK.FSA (FSA)
> import LTK.Tiers (project)
> import LTK.Algebra (SynMon)

> -- |True iff the automaton recognizes a TLAcom stringset.
> isTLAcom :: (Ord n, Ord e) => FSA n e -> Bool
> isTLAcom = isLAcom . project

> -- |True iff the monoid recognizes a TLAcom stringset.
> isTLAcomM :: (Ord n, Ord e) => SynMon n e -> Bool
> isTLAcomM = isLAcomM . project
