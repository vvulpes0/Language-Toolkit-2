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
which can contain other objects.  Let `A` be a type and `C` be a
container of elements of type `A`.  Then,

> class (Eq a) => Container c a | c -> a where
>     isIn :: c -> a -> Bool
>     isNotIn :: c -> a -> Bool
>     contains :: a -> c -> Bool
>     doesNotContain :: a -> c-> Bool
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

> instance (Eq a) => Container [a] a where
>     contains = elem
>     union a b = a ++ (difference b a)
>     intersection a b = difference a (difference a b)
>     difference a b = filter (isNotIn b) a
>     empty = []
>     insert = (:)

> instance (Ord a) => Container (Set.Set a) a where
>     contains = Set.member
>     union = Set.union
>     intersection = Set.intersection
>     difference = (Set.\\)
>     empty = Set.empty
>     insert = Set.insert

In this module, a structure is said to be `Collapsible` if it can be
collapsed to a single value, like a fold over a list.

> class Collapsible c where
>     collapse :: (a -> b -> b) -> b -> c a -> b
>     size :: (Integral a) => c b -> a
>
>     size = collapse (\_ -> (\y -> y + 1)) 0

> instance Collapsible [] where
>     collapse = foldr

> instance Collapsible Set.Set where
>     collapse = Set.fold
>     size = fromIntegral . Set.size

> unionAll :: (Ord a, Container c a, Collapsible s) => s c -> c
> unionAll = collapse union empty

> allS :: (Collapsible s) => (a -> Bool) -> s a -> Bool
> allS f = collapse ((&&) . f) True

> anyS :: (Collapsible s) => (a -> Bool) -> s a -> Bool
> anyS f = collapse ((||) . f) False

If something is a `Collapsible` `Container`, then we can use properties
of each typeclass to build map and filter, here called `tmap` and
`keep` to avoid namespace collisions.

> tmap :: (Collapsible s, Container (s b) b) => (a -> b) -> s a -> s b
> tmap f xs = collapse (insert . f) empty xs

> keep :: (Collapsible s, Container (s a) a) => (a -> Bool) -> s a -> s a
> keep f xs = collapse maybeKeep empty xs
>     where maybeKeep a as
>               | f a       = insert a as
>               | otherwise = as
