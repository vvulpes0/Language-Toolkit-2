> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.LTT
> Copyright : (c) 2019 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is Locally Testable (LTT) based on the semigroup characterization
> of Beaquier and Pin from their 1989 work
> "Factors of Words".
> -}
> module LTK.Decide.LTT (isLTT) where

> import LTK.FSA
> import LTK.Decide.SF (isSF)

> import Data.Set (Set)
> import qualified Data.Set as Set

> type S n e = (n, [Symbol e])
> type T n e = State (S n e)

> -- |True iff the automaton recognizes an LTT stringset.
> isLTT :: (Ord n, Ord e) => FSA n e -> Bool
> isLTT = both isSF (isSynMonOfLTT . syntacticMonoid)
>     where both g h x = g x && h x

A semigroup (S) [e.g. the syntactic semigroup] is locally testable iff
for all idempotent e, the generated subsemigroup eSe is an idempotent
commutative monoid.

> isSynMonOfLTT :: (Ord n, Ord e) =>
>                  FSA (n, [Symbol e]) e -> Bool
> isSynMonOfLTT s = allS (\(e,f) ->
>                         allS (\(a,b,u) ->
>                               lttTest s e f a u b
>                              )
>                         (triples (states s))
>                        )
>                   (pairs (idempotents s))

> lttTest :: (Ord n, Ord e) =>
>            FSA (S n e) e -> T n e -> T n e -> T n e -> T n e -> T n e -> Bool
> lttTest s e f a u b = follow s (g a ++ g f ++ g u ++ g e ++ g b ++ g f) e ==
>                       follow s (g b ++ g f ++ g u ++ g e ++ g a ++ g f) e
>     where g = snd . nodeLabel

An element x is idempotent iff xx == x.
Here we use the syntactic monoid and simply exclude the identity
if it does not appear in the syntactic semigroup.

> idempotents :: (Ord n, Ord e) =>
>                FSA (n, [Symbol e]) e -> Set (State (n, [Symbol e]))
> idempotents f = keep isIdem . tmap destination $ transitions f
>     where isIdem x = follow f (snd $ nodeLabel x) x == singleton x

> pairs :: Ord a => Set a -> Set (a, a)
> pairs xs = collapse (union . f) empty xs
>     where f x = Set.mapMonotonic ((,) x) xs
> triples :: Ord a => Set a -> Set (a, a, a)
> triples xs = collapse (union . f) empty (pairs xs)
>     where f (a, b) = Set.mapMonotonic (\x -> (x, a, b)) xs
