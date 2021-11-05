> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.LTT
> Copyright : (c) 2019-2021 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is Locally Testable (LTT) based on the semigroup characterization
> of Beaquier and Pin from their 1989 work
> "Factors of Words".
>
> @since 0.2
> -}
> module LTK.Decide.LTT (isLTT, isLTTM) where

> import Data.Set (Set)
> import qualified Data.Set as Set

> import LTK.Decide.SF (isSF)
> import LTK.FSA
> import LTK.Algebra

> type S n e = (n, [Symbol e])
> type T n e = State (S n e)

> -- |True iff the automaton recognizes an LTT stringset.
> isLTT :: (Ord n, Ord e) => FSA n e -> Bool
> isLTT = isLTTM . syntacticMonoid

> -- |True iff the monoid recognizes an LTT stringset.
> isLTTM :: (Ord n, Ord e) => SynMon n e -> Bool
> isLTTM = both isSF isSynMonOfLTT

A semigroup (S) [e.g. the syntactic semigroup] is
locally threshold testable iff
for all idempotent e and f, and for all a,b,u it holds that
eafuebf = ebfueaf.

> isSynMonOfLTT :: (Ord n, Ord e) => FSA (n, [Symbol e]) e -> Bool
> isSynMonOfLTT s = allS (\(e,f) ->
>                         allS (\(a,b,u) ->
>                               lttTest s e f a u b
>                              ) . triples $ states s
>                        ) . pairs $ idempotents s

> lttTest :: (Ord n, Ord e) =>
>            FSA (S n e) e ->
>            T n e -> T n e -> T n e -> T n e -> T n e ->
>            Bool
> lttTest s e f a u b
>     = follow s (g a ++ g f ++ g u ++ g e ++ g b ++ g f) e ==
>       follow s (g b ++ g f ++ g u ++ g e ++ g a ++ g f) e
>     where g = snd . nodeLabel

> pairs :: Ord a => Set a -> Set (a, a)
> pairs xs = collapse (union . f) empty xs
>     where f x = Set.mapMonotonic ((,) x) xs

> triples :: Ord a => Set a -> Set (a, a, a)
> triples xs = collapse (union . f) empty (pairs xs)
>     where f (a, b) = Set.mapMonotonic (\x -> (x, a, b)) xs
