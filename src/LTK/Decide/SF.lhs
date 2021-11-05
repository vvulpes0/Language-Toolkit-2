> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.SF
> Copyright : (c) 2019 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is Star-Free (SF) based on the semigroup characterization
> of Schutzenberger as reported by Pin in his chapter
> "Syntactic Semigroups" of "Handbook of Formal Languages"
>
> @since 0.2
> -}
> module LTK.Decide.SF (isSF, isSFM) where

> import LTK.FSA
> import LTK.Algebra

> -- |True iff the automaton recognizes a Star-Free stringset.
> isSF :: (Ord n, Ord e) => FSA n e -> Bool
> isSF = isSFM . syntacticMonoid

> -- |True iff the monoid is aperiodic.
> isSFM :: (Ord n, Ord e) => SynMon n e -> Bool
> isSFM = trivialUnder hEquivalence
