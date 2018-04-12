
> {-# OPTIONS_HADDOCK show-extensions #-}
> {-# Language
>   FlexibleInstances,
>   FunctionalDependencies,
>   MultiParamTypeClasses,
>   Trustworthy
>   #-}
> {-|
> Module      : Containers
> Copyright   : (c) 2016-2018 Dakotah Lambert
> License     : BSD-style, see LICENSE
> 
> Containers: a uniform way to work with entities that may
> contain other entities.
> -}
> module Containers ( Container(..)
>                   , Linearizable(..)
>                   , chooseOne
>                   , discardOne
>                   , Collapsible(..)
>                   , fromCollapsible
>                     -- *Combining multiple Containers
>                   , unionAll
>                   , intersectAll
>                     -- *Generic versions of Prelude functions
>                   , anyS
>                   , allS
>                   , tmap
>                   , keep
>                     -- *Multisets
>                   , Multiset
>                   , multiplicity
>                   , multisetFromList
>                   , setFromMultiset
>                   ) where
> 
> import safe Data.Monoid (Monoid(..))
> import safe Data.Set (Set)
> import safe qualified Data.Set as Set
> 

In mathematics, we typically use the same symbols to denote similar
operations on objects with similar structure.  For example, both
numbers and matrices can be multiplied, even though what constitutes
multiplication differs between them.  In this module, a few classes
are defined to allow such polymorphism.


> -- |The 'Container' class is used for types that can contain objects
> -- and can be combined with 'union', 'intersection', and 'difference'
> -- (relative complement).  Instances of 'Container' should satisfy the
> -- following laws:
> --
> -- > isIn == flip contains
> -- > isNotIn == flip doesNotContain
> -- > doesNotContain a == not . contains a
> -- > contains a empty == False
> -- > contains a (singleton b) == (a == b)
> -- > contains a (insert b c) == (a == b) || contains a c
> -- > contains a (union c1 c2) == contains a c1 || contains a c2
> -- > contains a (intersection c1 c2) == contains a c1 && contains a c2
> -- > intersection c c == c
> -- > difference c c == empty
> class (Eq a) => Container c a | c -> a where
>     isIn :: c -> a -> Bool
>     isNotIn :: c -> a -> Bool
>     contains :: a -> c -> Bool
>     doesNotContain :: a -> c -> Bool
>     isEmpty :: (Eq c) => c -> Bool
>     -- |@(union a b)@ returns a collection of elements that
>     -- are in one of @a@ or @b@, or both.
>     union :: c -> c -> c
>     -- |@(intersection a b)@ returns a collection of elements that
>     -- are in both @a@ and @b@.
>     intersection :: c -> c -> c
>     -- |@(difference a b)@ returns a collection of elements that
>     -- are in @a@ but not in @b@.
>     difference :: c -> c -> c
>     -- |@(symmetricDifference a b)@ returns a collection of elements
>     -- that are in one of @a@ or @b@, but not both.
>     symmetricDifference :: c -> c -> c
>     empty :: c
>     insert :: a -> c -> c
>     singleton :: a -> c
>     -- |@(isSubsetOf y x)@ tells whether @x@ is a subset of @y@.
>     isSubsetOf :: (Eq c) => c -> c -> Bool
>     isSubsetOf a b = intersection a b == b
>     -- |@(isSupersetOf y x)@ tells whether @x@ is a superset of @y@.
>     isSupersetOf :: (Eq c) => c -> c -> Bool
>     isSupersetOf = flip isSubsetOf
>     -- |@(isProperSubsetOf y x)@ tells whether @x@ is a proper subset of @y@.
>     isProperSubsetOf :: (Eq c) => c -> c -> Bool
>     isProperSubsetOf a b = isSubsetOf a b && a /= b
>     -- |@(isProperSupersetOf y x)@ tells whether @x@ is a proper superset of @y@.
>     isProperSupersetOf :: (Eq c) => c -> c -> Bool
>     isProperSupersetOf a b = isSupersetOf a b && a /= b
> 
>     isEmpty = (== empty)
>     isIn = flip contains
>     isNotIn c = not . isIn c
>     contains = flip isIn
>     doesNotContain = flip isNotIn
>     insert a c = union (singleton a) c
>     singleton a = insert a empty
>     symmetricDifference a b = union (difference a b) (difference b a)
>     {-# MINIMAL
>       (contains | isIn),
>       union,
>       intersection,
>       difference,
>       empty,
>       (insert | singleton) #-}
> 

The `Linearizable` class is used for types that can be traversed
linearly in one direction.  The class provides a function `choose`
where for any linearizable structure `ls`, `choose ls` returns as
a pair both a single element contained in `ls` and another structure
containing all and only those elements of `ls` that were not chosen.
The first and second parts of this pair may be returned alone by
`chooseOne` or `discardOne`, respectively.


> -- |The 'Linearizable' class is used for types that can be
> -- traversed linearly in one direction.
> class Linearizable l where
>     -- |Return the next element and the collection of remaining elements.
>     choose :: l a -> (a, l a)
> 
> -- |Like 'choose', but discards the remaining elements.
> chooseOne :: (Linearizable l) => l a -> a
> chooseOne   = fst . choose
> -- |Like 'choose', but discards the next element.
> discardOne :: (Linearizable l) => l a -> l a
> discardOne  = snd . choose
> 
> -- |The 'Collapsible' class is used for types that can be collapsed
> -- to a single value, like a fold over a list.  Any structure \(c\)
> -- that is 'Collapsible' must necessarily be 'Linearizable', since:
> --
> -- > collapse (:) [] c
> --
> -- performs a linearization.
> class Linearizable c => Collapsible c where
>     collapse :: (a -> b -> b) -> b -> c a -> b
>     size :: (Integral a) => c b -> a
> 
>     collapse f = curry (fst . until ((== 0) . size . snd) continue)
>         where continue (a, bs) = let (x, xs) = choose bs in (f x a, xs)
>     size = collapse (const succ) 0
>     {-# MINIMAL collapse | size #-}
> 


Consequences
============

A collapsible structure of containers may be merged into a single
container with either unions or intersections:


> -- |Combine 'Container's with 'union'.
> unionAll :: (Container c a, Collapsible s) => s c -> c
> unionAll = collapse union empty
> 
> -- |Combine 'Container's with 'intersection'.
> -- An empty source yields an empty result.
> intersectAll :: (Container c a, Collapsible s) => s c -> c
> intersectAll xs
>     | size xs == 0  = empty
>     | otherwise     = collapse intersection x xs'
>     where (x, xs')  = choose xs
> 

It is nice to have tests for existential and universal satisfaction of
predicates:


> -- |True iff some element satisfies a predicate.
> anyS :: Collapsible s => (a -> Bool) -> s a -> Bool
> anyS f = collapse ((||) . f) False
> {-# INLINE[1] anyS #-}
> {-# RULES
> "anyS/[]" forall (a :: [x]) f.
>     anyS f a = any f a
>   #-}
> 
> -- |True iff all elements satisfy a predicate.
> allS :: Collapsible s => (a -> Bool) -> s a -> Bool
> allS f = collapse ((&&) . f) True
> {-# INLINE[1] allS #-}
> {-# RULES
> "allS/[]" forall (a :: [x]) f.
>     allS f a = all f a
>   #-}
> 

If something is a `Collapsible` `Container`, then we can use
properties of each typeclass to build map and filter, here called
`tmap` and `keep` to avoid namespace collisions.


> -- |Appy a function to each element of a 'Collapsible'.
> tmap :: (Collapsible s, Container (s b1) b) => (a -> b) -> s a -> s b1
> tmap f xs = collapse (insert . f) empty xs
> {-# INLINE[1] tmap #-}
> {-# RULES
> "tmap/[]"  tmap = map
> "tmap/Set" forall (x :: Ord a => Set a) (f :: Ord b => x -> b) .
>        tmap f x = Set.map f x
>   #-}
> 
> -- |Retain only those elements that satisfy a predicate.
> keep :: (Collapsible s, Container (s a) a) => (a -> Bool) -> s a -> s a
> keep f xs = collapse maybeKeep empty xs
>     where maybeKeep a as
>               | f a        = insert a as
>               | otherwise  = as
> {-# INLINE[1] keep #-}
> {-# RULES
> "keep/[]" keep = filter
> "keep/Set" keep = Set.filter
> "keep/compose" forall (f :: a -> Bool) (g :: a -> Bool) xs.
>       keep f (keep g xs) = keep (\x -> f x && g x) xs
>   #-}
> 
> -- |Build a 'Container' from the elements of a 'Collapsible'.
> -- This can be used to cast between most types of 'Container'.
> -- Time complexity is \(O(nci)\), where \(n\) is the number of
> -- elements in the source, \(c\) is the cost of accessing a next
> -- element of the source, and \(i\) is the cost of inserting
> -- an element into the destination.
> fromCollapsible :: (Collapsible s, Container c a) => s a -> c
> fromCollapsible = collapse insert empty
> {-# INLINE[1] fromCollapsible #-}
> {-# RULES
> "fromCollapsible/multisetFromSet"
>         fromCollapsible = Multiset . Set.mapMonotonic (flip (,) 1)
> "fromCollapsible/setFromMultiset"  fromCollapsible = setFromMultiset
> "fromCollapsible/setFromList"      forall (xs :: Ord a => [a]).
>                                    fromCollapsible xs = Set.fromList xs
>   #-}
> 


Standard Prelude Types
=======================

A Haskell list is a Collapsible Container:


> instance Linearizable [] where
>     choose (x:xs) = (x, xs)
>     choose _      = (error "cannot choose an element from an empty list", [])
> instance Collapsible [] where
>     collapse = foldr
> instance (Eq a) => Container [a] a where
>     contains = elem
>     union = (++)
>     intersection a b = filter (isIn b) a
>     difference a b = filter (isNotIn b) a
>     empty = []
>     insert = (:)
> 

A Set is like a list with no duplicates, so it should act similarly:


> instance Linearizable Set where
>     choose xs
>         | Set.null xs  = (error "cannot choose an element from an empty set",
>                           Set.empty)
>         | otherwise    = Set.deleteFindMin xs
> instance Collapsible Set where
>     collapse = Set.fold
>     size = fromIntegral . Set.size
> instance (Ord a) => Container (Set a) a where
>     contains = Set.member
>     union = Set.union
>     intersection = Set.intersection
>     difference = (Set.\\)
>     empty = Set.empty
>     insert = Set.insert
>     isSubsetOf = flip Set.isSubsetOf
>     isProperSubsetOf = flip Set.isProperSubsetOf
>     isSupersetOf = Set.isSubsetOf
>     isProperSupersetOf = Set.isProperSubsetOf
> 


A new Multiset type, able to contain duplicates but still have
lookup-time logarithmic in the number of distinct elements.


> -- |A 'Multiset' is a 'Set' that may contain more than one instance
> -- of any given element.
> newtype Multiset a = Multiset (Set (a, Integer))
>     deriving (Eq, Ord)
> 
> -- |Analogous to 'isIn', returning the number of occurrences of an
> -- element in a 'Multiset'.
> -- Time complexity is \(O(\log{n})\),
> -- where \(n\) is the number of distinct elements in the 'Multiset'.
> multiplicity :: (Ord a) => Multiset a -> a -> Integer
> multiplicity (Multiset xs) x = maybe 0 (f . fst)  .
>                                Set.minView . snd  $
>                                Set.split (x, 0) xs
>     where f (y, m)
>               | y == x     =  m
>               | otherwise  =  0
> 
> -- |A specialization of 'fromCollapsible'
> -- with time complexity \(O(n)\),
> -- where \(n\) is the number of distinct elements in the source.
> setFromMultiset :: Multiset a -> Set a
> setFromMultiset (Multiset a) = Set.mapMonotonic fst a
> 
> instance Linearizable Multiset where
>     choose (Multiset xs)
>         | Set.null xs  =  (error "cannot choose an element from an empty multiset",
>                            Multiset (Set.empty))
>         | m == 1       =  (a, f as)
>         | otherwise    =  (a, f ((a, pred m) : as))
>         where ((a,m):as) = Set.toAscList xs
>               f = Multiset . Set.fromDistinctAscList
> instance Collapsible Multiset where
>     size (Multiset xs) = fromIntegral . sum . map snd $ Set.toList xs
>     collapse f x (Multiset xs) = collapse f x .
>                                  concatMap (uncurry (flip replicate) .
>                                             fmap fromIntegral) $
>                                  Set.toAscList xs
> instance Ord a => Container (Multiset a) a where
>     contains x = contains x . setFromMultiset
>     insert x (Multiset xs) = Multiset (insert newX noX)
>         where hasX = keep ((== x) . fst) xs
>               noX  = difference xs hasX
>               newX = Set.fold add (x, 1) hasX
>               add (a, c1) (b, c2) = (a, c1 + c2)
>     empty = Multiset empty
>     union (Multiset xs) (Multiset ys) =
>         Multiset (Set.fromDistinctAscList zs)
>         where xs' = Set.toAscList xs
>               ys' = Set.toAscList ys
>               zs  = unionSortedMultis xs' ys'
>     intersection (Multiset xs) (Multiset ys) =
>         Multiset (Set.fromDistinctAscList zs)
>         where xs' = Set.toAscList xs
>               ys' = Set.toAscList ys
>               zs  = intersectSortedMultis xs' ys'
>     difference (Multiset xs) (Multiset ys) =
>         Multiset (Set.fromDistinctAscList zs)
>         where xs' = Set.toAscList xs
>               ys' = Set.toAscList ys
>               zs  = differenceSortedMultis xs' ys'
> instance Ord a => Monoid (Multiset a) where
>     mempty = empty
>     mappend = union
> 
> instance Show a => Show (Multiset a) where
>     showsPrec p m = showParen (p > 10) $
>                     showString "multisetFromList " .
>                     shows (collapse (:) [] m)
> instance (Ord a, Read a) => Read (Multiset a) where
>     readsPrec p = readParen (p > 10) $ \r ->
>                   do
>                     ("multisetFromList", s) <- lex r
>                     (xs, t) <- reads s
>                     return (multisetFromList xs, t)
> 
> -- |A specialization of 'fromCollapsible'.
> multisetFromList :: Ord a => [a] -> Multiset a
> multisetFromList = fromCollapsible
> 
> unionSortedMultis :: Ord a => [(a, Integer)] -> [(a, Integer)] -> [(a, Integer)]
> unionSortedMultis xs [] = xs
> unionSortedMultis [] ys = ys
> unionSortedMultis (x:xs) (y:ys)
>     | fst x < fst y  =  x : unionSortedMultis xs (y:ys)
>     | fst x > fst y  =  y : unionSortedMultis (x:xs) ys
>     | otherwise      =  unionSortedMultis ((fst x, snd x + snd y) : xs) ys
> 
> intersectSortedMultis :: Ord a => [(a, Integer)] -> [(a, Integer)] -> [(a, Integer)]
> intersectSortedMultis _ [] = []
> intersectSortedMultis [] _ = []
> intersectSortedMultis (x:xs) (y:ys)
>     | fst x < fst y  =  intersectSortedMultis xs (y:ys)
>     | fst x > fst y  =  intersectSortedMultis (x:xs) ys
>     | otherwise      =  (fst x, min (snd x) (snd y)) :
>                         intersectSortedMultis xs ys
> 
> differenceSortedMultis :: Ord a => [(a, Integer)] -> [(a, Integer)] -> [(a, Integer)]
> differenceSortedMultis xs [] = xs
> differenceSortedMultis [] _  = []
> differenceSortedMultis (x:xs) (y:ys)
>     | fst x < fst y   =  x : differenceSortedMultis xs (y:ys)
>     | fst x > fst y   =  differenceSortedMultis (x:xs) ys
>     | snd x <= snd y  =  differenceSortedMultis xs ys
>     | otherwise       =  (fst x, snd x - snd y) :
>                          differenceSortedMultis xs ys

