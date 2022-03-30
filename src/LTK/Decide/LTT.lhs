> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.LTT
> Copyright : (c) 2019-2022 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is Locally Testable (LTT) based on the semigroup characterization
> of Beaquier and Pin from their 1989 work "Factors of Words"
> coupled with a connection by Almeida (1989) to Acom.
>
> @since 0.2
> -}
> module LTK.Decide.LTT (isLTT, isLTTM) where

> import LTK.Decide.SF (isSFM)
> import LTK.Decide.Acom (comTest)
> import LTK.FSA
> import LTK.Algebra

> -- |True iff the automaton recognizes an LTT stringset.
> isLTT :: (Ord n, Ord e) => FSA n e -> Bool
> isLTT = isLTTM . syntacticMonoid

> -- |True iff the monoid recognizes an LTT stringset.
> --
> -- @since 1.0
> isLTTM :: (Ord n, Ord e) => SynMon n e -> Bool
> isLTTM = both isSFM eseCom
>     where eseCom m = all (comTest m . ese m) (idempotents m)
