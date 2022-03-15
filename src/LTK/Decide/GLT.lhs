> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.GLT
> Copyright : (c) 2021 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is generalized locally testable in the sense of Brzozowski and
> Fich (1984):
> https://doi.org/10.1016/0012-365X(84)90045-1
> -}
> module LTK.Decide.GLT (isGLT, isGLTM) where

> import qualified Data.Set as Set

> import LTK.FSA
> import LTK.Algebra

> -- |True iff the automaton recognizes a generalized locally-testable
> -- stringset.
> isGLT :: (Ord n, Ord e) => FSA n e -> Bool
> isGLT = isGLTM . syntacticMonoid

> -- |True iff the monoid satisfies the generalized local testabiltiy
> -- condition.
> isGLTM :: (Ord n, Ord e) => FSA (n, [Symbol e]) e -> Bool
> isGLTM f = all commutativeBand . map (emee f) $ Set.toList i
>     where i = idempotents f
>           commutativeBand = both (isCommutative f) (isSubsetOf i)
