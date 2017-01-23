> {-# Language
>   FlexibleInstances,
>   FunctionalDependencies,
>   MultiParamTypeClasses
>   #-}
> module LogicClasses where

> import qualified Data.Set as Set

In mathematics, we typically use the same symbols to denote similar
operations on objects with similar structure.  For example, both
numbers and matrices can be multiplied, even though what constitutes
multiplication differs between them.  In this module, a few classes
are defined to allow such polymorphism.

The first class, `Container`, defines a common interface to objects
which can contain other objects and later be inspected.  Let `A` be a
type and `C` be a container of elements of type `A`.  Then,

> class (Eq a) => Container c a | c -> a where
>     isIn :: c -> a -> Bool
>     isNotIn :: c -> a -> Bool
>     contains :: a -> c -> Bool
>     doesNotContain :: a -> c -> Bool
>     union :: c -> c -> c
>     intersection :: c -> c -> c
>     difference :: c -> c -> c
>     empty :: c
>     insert :: a -> c -> c
>     singleton :: a -> c
>
>     isIn = flip contains
>     isNotIn c = not . isIn c
>     contains = flip isIn
>     doesNotContain = flip isNotIn
>     insert a c = union (singleton a) c
>     singleton a = insert a empty

The `Linearizable` class is used for types that can be traversed
linearly in one direction.  The class provides a function `choose`
where for any linearizable structure `ls`, `choose ls` returns as
a pair both a single element contained in `ls` and another structure
containing all and only those elements of `ls` that were not chosen.
The first and second parts of this pair may be returned alone by
`chooseOne` or `discardOne`, respectively.

Instances of Linearizable must provide a definition for either
`choose` or both `chooseOne` and `discardOne`.

> class Linearizable l where
>     choose :: l a -> (a, l a)
>     chooseOne :: l a -> a
>     discardOne :: l a -> l a
>
>     choose x    = (chooseOne x, discardOne x)
>     chooseOne   = fst . choose
>     discardOne  = snd . choose

In this module, a structure is said to be `Collapsible` if it can be
collapsed to a single value, like a fold over a list.  Any structure c
that is Collapsible must necessarily be Linearizable, since
	collapse (:) [] c
performs a linearization.

Instances of Collapsible must provide a definition for at least one of
`collapse` or `size`.  The other may be derived.

> class Linearizable c => Collapsible c where
>     collapse :: (a -> b -> b) -> b -> c a -> b
>     size :: (Integral a) => c b -> a
>
>     collapse f = curry (fst . until ((== 0) . size . snd) continue)
>         where continue (a, bs) = let (x, xs) = choose bs in (f x a, xs)
>     size = collapse (const succ) 0


Consequences
============

A collapsible structure of containers may be merged into a single
container with either unions or intersections:

> unionAll :: (Container c a, Collapsible s) => s c -> c
> unionAll = collapse union empty

> intersectAll :: (Container c a, Collapsible s) => s c -> c
> intersectAll xs
>     | size xs == 0  = empty
>     | otherwise     = collapse intersection x xs'
>     where (x, xs')  = choose xs

It is nice to have tests for existential and universal satisfaction of
predicates:

> anyS :: Collapsible s => (a -> Bool) -> s a -> Bool
> anyS f = collapse ((||) . f) False

> allS :: Collapsible s => (a -> Bool) -> s a -> Bool
> allS f = collapse ((&&) . f) True

If something is a `Collapsible` `Container`, then we can use
properties of each typeclass to build map and filter, here called
`tmap` and `keep` to avoid namespace collisions.

> tmap :: (Collapsible s, Container (s b) b) => (a -> b) -> s a -> s b
> tmap f xs = collapse (insert . f) empty xs

> keep :: (Collapsible s, Container (s a) a) => (a -> Bool) -> s a -> s a
> keep f xs = collapse maybeKeep empty xs
>     where maybeKeep a as
>               | f a        = insert a as
>               | otherwise  = as


Standard Prelude Types
=======================

A Haskell list is a Collapsible Container:

> instance Linearizable [] where
>     chooseOne   = head
>     discardOne  = tail
> instance Collapsible [] where
>     collapse = foldr
> instance (Eq a) => Container [a] a where
>     contains = elem
>     union = (++)
>     intersection a b = filter (isIn b) a
>     difference a b = filter (isNotIn b) a
>     empty = []
>     insert = (:)

A Set is like a list with no duplicates, so it should act similarly:

> instance Linearizable Set.Set where
>     choose  = Set.deleteFindMin
> instance Collapsible Set.Set where
>     collapse = Set.fold
>     size = fromIntegral . Set.size
> instance (Ord a) => Container (Set.Set a) a where
>     contains = Set.member
>     union = Set.union
>     intersection = Set.intersection
>     difference = (Set.\\)
>     empty = Set.empty
>     insert = Set.insert
