> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.LTT
> Copyright : (c) 2019,2021-2024 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is Locally Testable (LTT) based on the semigroup characterization
> of Beaquier and Pin from their 1989 work
> "Factors of Words".
>
> @since 0.2
> -}
> module LTK.Decide.LTT (isLTT, isLTTM, isLTTs) where

> import Data.Representation.FiniteSemigroup
> import qualified Data.IntSet as IntSet

> import LTK.FSA
> import LTK.Algebra(SynMon)

> -- |True iff the automaton recognizes an LTT stringset.
> isLTT :: (Ord n, Ord e) => FSA n e -> Bool
> isLTT = isLTTs . syntacticSemigroup

> -- |True iff the monoid recognizes an LTT stringset.
> --
> -- @since 1.0
> isLTTM :: (Ord n, Ord e) => SynMon n e -> Bool
> isLTTM = isLTT

A semigroup (S) [e.g. the syntactic semigroup] is
locally threshold testable iff
for all idempotent e and f, and for all a,b,u it holds that
eafuebf = ebfueaf.

> -- |True iff the semigroup recognizes an LTT stringset.
> --
> -- @since 1.2
> isLTTs :: FiniteSemigroupRep s => s -> Bool
> isLTTs s = isAperiodic s && all (uncurry go) [(a,b) | a <- is, b <- is]
>     where t = fstable s
>           is = IntSet.toList $ idempotents t
>           xs = [0..fssize t - 1]
>           eval = foldr1 (fsappend t)
>           go e f = let ps = map (\i -> eval [e,i,f]) xs
>                    in all (uncurry check) [(a,b) | a <- ps, b <- ps]
>           check a b = all (\i -> eval [a,i,b] == eval [b,i,a]) xs
