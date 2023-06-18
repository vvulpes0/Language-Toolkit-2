> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.LAcom
> Copyright : (c) 2019-2022 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> has a syntactic semigroup which is Locally Commutative and Aperiodic,
> a near superclass of the Locally Threshold Testable languages.
>
> @since 1.1
> -}
> module LTK.Decide.LAcom (isLAcom, isLAcomM) where

> import LTK.Decide.SF (isSFM)
> import LTK.Decide.Acom (comTest)
> import LTK.FSA
> import LTK.Algebra

> -- |True iff the automaton recognizes a LAcom stringset.
> isLAcom :: (Ord n, Ord e) => FSA n e -> Bool
> isLAcom = isLAcomM . syntacticMonoid

> -- |True iff the monoid recognizes a LAcom stringset.
> isLAcomM :: (Ord n, Ord e) => SynMon n e -> Bool
> isLAcomM = both isSFM eseCom
>     where eseCom m = all (comTest m . ese m) (idempotents m)
