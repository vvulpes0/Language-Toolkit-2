> {-# Language UnicodeSyntax #-}
> {-# Language FlexibleInstances #-}
> {-# Language MultiParamTypeClasses #-}
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
>
>     (∋) = flip (∈)
>     a ∉ c = not (a ∈ c)
>     c ∌ a = not (c ∋ a)

> instance (Eq a) ⇒ Container [a] a where
>     (∈)   = elem
>     a ∪ b = a ++ (b ∖ a)
>     a ∩ b = a ∖ (a ∖ b)
>     a ∖ b = filter (∉ b) a
>     (∅)   = []

> instance (Ord a) ⇒ Container (Set.Set a) a where
>     (∈) = Set.member
>     (∪) = Set.union
>     (∩) = Set.intersection
>     (∖) = (Set.\\)
>     (∅) = Set.empty

In this module, a `Container` is said to be `Collapsible` if it can be
collapsed to a single value in a way that resembles a fold over a
list.  In more recent versions of the Haskell compiler, there exists a
`Foldable` typeclass for this purpose.

> class (Container c a) ⇒ Collapsible c a | c → a where
>     collapse ∷ (a → b → b) → b → c → b

> instance (Eq a) ⇒ Collapsible [a] a where
>     collapse = foldr

> instance (Ord a) ⇒ Collapsible (Set.Set a) a where
>     collapse = Set.fold

> (⋃) ∷ (Eq a, Container c a, Collapsible s c) ⇒ s → c
> (⋃) = collapse (∪) (∅)

> unionAll ∷ (Ord a, Container c a, Collapsible s c) ⇒ s → c
> unionAll = (⋃)

> allS ∷ (Collapsible s a) ⇒ (a → Bool) → s → Bool
> allS f = collapse ((&&) . f) True

> anyS ∷ (Collapsible s a) ⇒ (a → Bool) → s → Bool
> anyS f = collapse ((||) . f) False

> x = [1,2,3] ∩ [2,3,4]
