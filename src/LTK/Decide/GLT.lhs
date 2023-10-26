> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.GLT
> Copyright : (c) 2021-2023 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is generalized locally testable in the sense of Brzozowski and
> Fich (1984):
> https://doi.org/10.1016/0012-365X(84)90045-1
>
> @since 1.0
> -}
> module LTK.Decide.GLT (isGLT, isGLTM, isGLTs) where

> import Data.Representation.FiniteSemigroup

> import LTK.FSA
> import LTK.Algebra(SynMon)

> -- |True iff the automaton recognizes a generalized locally-testable
> -- stringset.
> isGLT :: (Ord n, Ord e) => FSA n e -> Bool
> isGLT = isGLTs . syntacticSemigroup

> -- |True iff the monoid satisfies the generalized local testabiltiy
> -- condition.
> isGLTM :: (Ord n, Ord e) => SynMon n e -> Bool
> isGLTM = isGLT

> -- |True iff the semigroup lies in \(M_e J_1\).
> isGLTs :: FiniteSemigroupRep s => s -> Bool
> isGLTs = all (both isJTrivial isBand) . emee
