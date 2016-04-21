> {-# Language
>   FlexibleInstances,
>   FunctionalDependencies,
>   MultiParamTypeClasses,
>   UnicodeSyntax
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

> class (Eq a) ⇒ Container c a | c → a where
>     infixl 8 ∈
>     (∈) ∷ a → c → Bool
>     infixl 8 ∋
>     (∋) ∷ c → a → Bool
>     infixl 8 ∉
>     (∉) ∷ a → c→ Bool
>     infixl 8 ∌
>     (∌) ∷ c→ a → Bool
>     infixl 6 ∪
>     (∪) ∷ c → c → c
>     infixl 7 ∩
>     (∩) ∷ c → c → c
>     infixl 6 ∖
>     (∖) ∷ c → c → c
>     (∅) ∷ c
>     insert ∷ a → c → c
>     singleton ∷ a → c
>
>     (∋) = flip (∈)
>     a ∉ c = not (a ∈ c)
>     c ∌ a = not (c ∋ a)
>     singleton a = insert a (∅)
>     insert a c = singleton a ∪ c

> instance (Eq a) ⇒ Container [a] a where
>     (∈)    = elem
>     a ∪ b  = a ++ (b ∖ a)
>     a ∩ b  = a ∖ (a ∖ b)
>     a ∖ b  = filter (∉ b) a
>     (∅)    = []
>     insert = (:)

> instance (Ord a) ⇒ Container (Set.Set a) a where
>     (∈)    = Set.member
>     (∪)    = Set.union
>     (∩)    = Set.intersection
>     (∖)    = (Set.\\)
>     (∅)    = Set.empty
>     insert = Set.insert

In this module, a structure is said to be `Collapsible` if it can be
collapsed to a single value, like a fold over a list.

> class Collapsible c where
>     collapse ∷ (a → b → b) → b → c a → b
>     size ∷ (Integral a) ⇒ c b → a
>
>     size = collapse (\_ → (\y → y + 1)) 0

> instance Collapsible [] where
>     collapse = foldr

> instance Collapsible Set.Set where
>     collapse = Set.fold
>     size     = fromIntegral . Set.size

> (⋃) ∷ (Eq a, Container c a, Collapsible s) ⇒ s c → c
> (⋃) = collapse (∪) (∅)

> unionAll ∷ (Ord a, Container c a, Collapsible s) ⇒ s c → c
> unionAll = (⋃)

> allS ∷ (Collapsible s) ⇒ (a → Bool) → s a → Bool
> allS f = collapse ((&&) . f) True

> anyS ∷ (Collapsible s) ⇒ (a → Bool) → s a → Bool
> anyS f = collapse ((||) . f) False

If something is a `Collapsible` `Container`, then we can use properties
of each typeclass to build map and filter, here called `tmap` and
`keep` to avoid namespace collisions.

> tmap ∷ (Collapsible s, Container (s b) b) ⇒ (a → b) → s a → s b
> tmap f xs = collapse (insert . f) (∅) xs

> keep ∷ (Collapsible s, Container (s a) a) ⇒ (a → Bool) → s a → s a
> keep f xs = collapse maybeKeep (∅) xs
>     where maybeKeep a as
>               | f a       = insert a as
>               | otherwise = as
