> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.LT
> Copyright : (c) 2019 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is Locally Testable (LT) based on the semigroup characterization
> of Brzozowski and Simon from their 1973 work
> "Characterizations of locally testable events".
>
> @since 0.2
> -}
> module LTK.Decide.LT (isLT) where

> import Data.Set (Set)
> import qualified Data.Set as Set

> import LTK.FSA

> -- |True iff the automaton recognizes an LT stringset.
> isLT :: (Ord n, Ord e) => FSA n e -> Bool
> isLT = isSynMonOfLT . syntacticMonoid

A semigroup (S) [e.g. the syntactic semigroup] is locally testable iff
for all idempotent e, the generated subsemigroup eSe is an idempotent
commutative monoid.

> isSynMonOfLT :: (Ord n, Ord e) =>
>                 FSA (n, [Symbol e]) e -> Bool
> isSynMonOfLT s = allS (both (isCommutative s) (isIdempotent s) .
>                        generatedSubsemigroup s
>                       ) $ idempotents s

An element x is idempotent iff xx == x.
Here we use the syntactic monoid and simply exclude the identity
if it does not appear in the syntactic semigroup.

> idempotents :: (Ord n, Ord e) =>
>                FSA (n, [Symbol e]) e -> Set (State (n, [Symbol e]))
> idempotents f = keep isIdem . tmap destination $ transitions f
>     where isIdem x = follow f (snd $ nodeLabel x) x == singleton x

> generatedSubsemigroup :: (Ord n, Ord e) =>
>                          FSA (n, [Symbol e]) e -> State (n, [Symbol e]) ->
>                          Set (State (n, [Symbol e]))
> generatedSubsemigroup f x
>     = collapse (union . follow f (snd $ nodeLabel x)) empty $
>       primitiveIdealR f x

> isIdempotent :: (Ord n, Ord e) =>
>                 FSA (n, [Symbol e]) e -> Set (State (n, [Symbol e])) ->
>                 Bool
> isIdempotent f = isSubsetOf (idempotents f)

Testing commutativity by checking that all elements commute with one another.

> isCommutative :: (Ord n, Ord e) =>
>                  FSA (n, [Symbol e]) e -> Set (State (n, [Symbol e])) ->
>                  Bool
> isCommutative f ss = allS (uncurry commute) (pairs ss)
>     where commute u v = follow f (snd $ nodeLabel u) v ==
>                         follow f (snd $ nodeLabel v) u

> pairs :: (Ord a) => Set a -> Set (a, a)
> pairs xs = collapse (union . f) empty xs
>     where f x = Set.mapMonotonic ((,) x) . snd $ Set.split x xs
