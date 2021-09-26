> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Algebra
> Copyright : (c) 2021 Dakotah Lambert
> License   : MIT

> This module centralizes definitions of some commonly used
> algebraic properties.
> -}

> module LTK.Algebra
>     ( -- *Tests
>       isCommutative
>       -- *Generated Submonoids
>     , me
>     , emee
>       -- *Powers
>     , idempotents
>     , omega
>     ) where

> import Data.Set (Set)
> import qualified Data.Set as Set

> import LTK.FSA

> type S n e = (n, [Symbol e])
> type T n e = State (S n e)


Generated Submonoids
====================

For a monid M and idempotent e, Me is the set
    {m : e is in the two-sided ideal of m}.

The class MeV, for some variety V, is the set of all monoids M
where for all idempotents e, e*Me*e is in V.


> me :: (Ord n, Ord e) => FSA (S n e) e -> T n e -> Set (T n e)
> me monoid e = keep (contains e . primitiveIdeal2 monoid)
>               $ states monoid

emee is e*Me*e: first follow the label of e from all the states,
then take the resulting labels and follow those from e.

> emee :: (Ord n, Ord e) => FSA (S n e) e -> T n e -> Set (T n e)
> emee monoid e = collapse (union . flip (follow monoid) e . s) empty
>                 . collapse (union . follow monoid (s e)) empty
>                 $ x
>     where x = me monoid e
>           s = snd . nodeLabel


Commutativity
=============

Testing commutativity by checking that all elements commute with one another.

> -- |True iff the supplied elements commute with one another
> -- in the provided monoid.
> isCommutative :: (Ord n, Ord e) =>
>                  FSA (n, [Symbol e]) e -> Set (State (n, [Symbol e])) ->
>                  Bool
> isCommutative f ss = allS (uncurry commute) (pairs ss)
>     where commute u v = follow f (snd $ nodeLabel u) v ==
>                         follow f (snd $ nodeLabel v) u


Powers
======

An element x is idempotent iff xx == x.
Here we use the syntactic monoid and simply exclude the identity
if it does not appear in the syntactic semigroup.

> -- |All elements \(e\) of the given monoid such that \(e*e=e\).
> idempotents :: (Ord n, Ord e) =>
>                FSA (n, [Symbol e]) e -> Set (T n e)
> idempotents f = keep isIdem . tmap destination $ transitions f
>     where isIdem x = follow f (snd $ nodeLabel x) x == singleton x

> -- |@omega monoid s@ is the unique element \(t\) where \(t*t\) = \(t\)
> -- and \(t\) is in \(\{s, s^2, s^3, \ldots\}\).
> -- In other words, \(t\) is the unique idempotent element
> -- in this set.
> -- This method used here assumes @monoid@ is aperiodic and finite
> -- and uses this to skip many otherwise necessary checks.
> omega :: (Ord n, Ord e) => FSA (S n e) e -> T n e -> T n e
> omega monoid s = fst
>                  . until (uncurry (==)) (\(_,b) -> (b, f b))
>                  $ (s, f s)
>     where f x = Set.findMin $ follow monoid (snd (nodeLabel x)) x


Helpers
=======

> pairs :: Ord a => Set a -> Set (a, a)
> pairs xs = collapse (union . f) empty xs
>     where f x = Set.mapMonotonic ((,) x) xs
