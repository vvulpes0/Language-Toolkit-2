> {-# OPTIONS_HADDOCK show-extensions #-}
> {-# Language
>   CPP,
>   FlexibleInstances,
>   FunctionalDependencies,
>   MultiParamTypeClasses,
>   Trustworthy
>   #-}

#if !defined(MIN_VERSION_base)
# define MIN_VERSION_base(a,b,c) 0
#endif
#if !defined(MIN_VERSION_containers)
# define MIN_VERSION_containers(a,b,c) 0
#endif

> {-|
> Module      : LTK.Containers
> Copyright   : (c) 2016-2019 Dakotah Lambert
> License     : MIT
> 
> Containers: a uniform way to work with entities that may
> contain other entities.
> -}
> module LTK.Containers
>        ( Container(..)
>        , Linearizable(..)
>        , chooseOne
>        , discardOne
>        , Collapsible(..)
>        , isize
>        , zsize
>        , fromCollapsible
>        -- *Combining multiple Containers
>        , unionAll
>        , intersectAll
>        -- *Generic versions of Prelude functions and similar
>        , anyS
>        , allS
>        , both
>        , tmap
>        , keep
>        , groupBy
>        , partitionBy
>        , refinePartitionBy
>        -- *Multisets
>        , Multiset
>        , multiplicity
>        , multisetFromList
>        , setFromMultiset
>        -- *Set of Set with alternate ordering
>        -- |The 'choose' instance for 'Set' will always pick
>        -- the least available element.
>        -- If one wants to process elements
>        -- in a different order,
>        -- one can simply wrap the elements in such a way
>        -- that they sort in the intended order of processing.
>        -- This section contains some such wrapper types.
>        , IncreasingSize(..)
>        , DecreasingSize(..)
>        -- *Miscellaneous functions
>        , extractMonotonic
>        , tr
>        ) where

> import safe Data.Monoid (Monoid, mempty, mappend)
#if MIN_VERSION_base(4,9,0)
> import safe Data.Semigroup (Semigroup, (<>))
#endif
> import safe Data.Set (Set)
> import safe qualified Data.Set as Set

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
> class (Eq a) => Container c a | c -> a
>     where isIn :: c -> a -> Bool
>           isNotIn :: c -> a -> Bool
>           contains :: a -> c -> Bool
>           doesNotContain :: a -> c -> Bool
>           isEmpty :: (Eq c) => c -> Bool
>           -- |@(union a b)@ returns a collection of elements that
>           -- are in one of @a@ or @b@, or both.
>           union :: c -> c -> c
>           -- |@(intersection a b)@ returns a collection of elements that
>           -- are in both @a@ and @b@.
>           intersection :: c -> c -> c
>           -- |@(difference a b)@ returns a collection of elements that
>           -- are in @a@ but not in @b@.
>           difference :: c -> c -> c
>           -- |@(symmetricDifference a b)@ returns a collection of elements
>           -- that are in one of @a@ or @b@, but not both.
>           symmetricDifference :: c -> c -> c
>           empty :: c
>           insert :: a -> c -> c
>           singleton :: a -> c
>           -- |@(isSubsetOf y x)@ tells whether @x@ is a subset of @y@.
>           isSubsetOf :: (Eq c) => c -> c -> Bool
>           -- |@(isSupersetOf y x)@ tells whether @x@ is a superset of @y@.
>           isSupersetOf :: (Eq c) => c -> c -> Bool
>           -- |@(isProperSubsetOf y x)@ tells whether
>           -- @x@ is a proper subset of @y@.
>           isProperSubsetOf :: (Eq c) => c -> c -> Bool
>           -- |@(isProperSupersetOf y x)@ tells whether
>           -- @x@ is a proper superset of @y@.
>           isProperSupersetOf :: (Eq c) => c -> c -> Bool
>           -- Default definitions:
>           isEmpty = (== empty)
>           isIn = flip contains
>           isNotIn c = not . isIn c
>           contains = flip isIn
>           doesNotContain = flip isNotIn
>           insert a c = union (singleton a) c
>           singleton a = insert a empty
>           symmetricDifference a b = union (difference a b) (difference b a)
>           isSubsetOf a b = intersection a b == b
>           isSupersetOf = flip isSubsetOf
>           isProperSubsetOf a b = isSubsetOf a b && a /= b
>           isProperSupersetOf a b = isSupersetOf a b && a /= b
>           {-# MINIMAL
>               (contains | isIn)
>             , union
>             , intersection
>             , difference
>             , empty
>             , (insert | singleton) #-}

The `Linearizable` class is used for types that can be traversed
linearly in one direction.  The class provides a function `choose`
where for any linearizable structure `ls`, `choose ls` returns as
a pair both a single element contained in `ls` and another structure
containing all and only those elements of `ls` that were not chosen.
The first and second parts of this pair may be returned alone by
`chooseOne` or `discardOne`, respectively.

> -- |The 'Linearizable' class is used for types that can be
> -- traversed linearly in one direction.
> class Linearizable l
>     where choose :: l a -> (a, l a)
>           -- ^Return the next element and
>           -- the collection of remaining elements.

> -- |Like 'choose', but discards the remaining elements.
> chooseOne :: (Linearizable l) => l a -> a
> chooseOne   = fst . choose
> -- |Like 'choose', but discards the next element.
> discardOne :: (Linearizable l) => l a -> l a
> discardOne  = snd . choose

> -- |The 'Collapsible' class is used for types that can be collapsed
> -- to a single value, like a fold over a list.  Any structure \(c\)
> -- that is 'Collapsible' must necessarily be 'Linearizable', since:
> --
> -- > collapse (:) [] c
> --
> -- performs a linearization.
> class Linearizable c => Collapsible c
>     where collapse :: (a -> b -> b) -> b -> c a -> b
>           size :: (Integral a) => c b -> a

>           collapse f = curry (fst . until ((== 0) . isize . snd) cont)
>               where cont (a, bs) = let (x, xs) = choose bs in (f x a, xs)
>           size = collapse (const succ) 0
>           {-# MINIMAL collapse | size #-}

> -- |Analogue to @isEmpty@ for Collapsible structures
> zsize :: Collapsible c => c b -> Bool
> zsize = collapse (const $ const False) True
> {-# INLINE[1] zsize #-}
> {-# RULES
> "zsize/Set" zsize = (== 0) . Set.size
>   #-}

> -- |The size of the input as an integer
> isize :: Collapsible c => c b -> Integer
> isize = size


Consequences
============

A collapsible structure of containers may be merged into a single
container with either unions or intersections:

> -- |Combine 'Container's with 'union'.
> unionAll :: (Container c a, Collapsible s) => s c -> c
> unionAll = collapse union empty

> -- |Combine 'Container's with 'intersection'.
> -- An empty source yields an empty result.
> intersectAll :: (Container c a, Collapsible s) => s c -> c
> intersectAll xs
>     | size xs == (0 :: Integer)  = empty
>     | otherwise                  = collapse intersection x xs'
>     where (x, xs')               = choose xs

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

> -- |True iff all elements satisfy a predicate.
> allS :: Collapsible s => (a -> Bool) -> s a -> Bool
> allS f = collapse ((&&) . f) True
> {-# INLINE[1] allS #-}
> {-# RULES
> "allS/[]" forall (a :: [x]) f.
>     allS f a = all f a
>   #-}

> -- |True iff the given object satisfies both given predicates.
> both :: (a -> Bool) -> (a -> Bool) -> a -> Bool
> both f g x = f x && g x

If something is a `Collapsible` `Container`, then we can use
properties of each typeclass to build map and filter, here called
`tmap` and `keep` to avoid namespace collisions.

> -- |Appy a function to each element of a 'Collapsible'.
> tmap :: (Collapsible s, Container (s b1) b) => (a -> b) -> s a -> s b1
> tmap f xs = collapse (insert . f) empty xs
> {-# INLINE[1] tmap #-}
> {-# RULES
> "tmap/[]"  tmap = map
> "tmap/Set" forall (x :: Ord a => Set a) (f :: Ord b => a -> b) .
>        tmap f x = Set.map f x
>   #-}

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

> -- |Partition a Container.  For example,
> --
> -- > groupBy (`mod` 3) [0..9] == [[0,3,6,9],[1,4,7],[2,5,8]]
> groupBy :: ( Eq b, Collapsible s, Container (s a) a
>            , Container (s (s a)) (s a) ) =>
>            (a -> b) -> s a -> s (s a)
> groupBy f xs
>     | isEmpty xs  =  empty
>     | otherwise   =  insert currentGroup $ groupBy f others
>     where y = f (chooseOne xs)
>           (currentGroup, others)
>               = collapse (\a (cg, os) ->
>                           if f a == y
>                           then (insert a cg, os)
>                           else (cg, insert a os)) (empty, empty) xs


Notes on partitionBy:
First, the elements of the set are prefixed by their result under f.
This sorts them by this value, which we can then extract monotonically.
If we have a collection with identical first values,
then the second-projection is monotonic.
Set.splitAt doesn't exist in older versions of containers,
so we use Set.split with Set.findMax instead.

> -- |A fast 'groupBy' for 'Set' objects.
> --
> -- @since 0.2
> partitionBy :: (Ord a, Ord n) => (n -> a) -> Set n -> Set (Set n)
> partitionBy f = fst .
>                 until (isEmpty . snd)
>                 (\(x, y) ->
>                      let extracted  =  extractMonotonic fst
>                                        (fst (chooseOne y)) y
>                          (_, y')    =  Set.split (Set.findMax extracted) y
>                      in (insert (Set.mapMonotonic snd extracted) x, y')
>                 ) .
>                 (,) empty . Set.map (\x -> (f x, x))

> -- |A convenience function for the common partition refinement operation.
> --
> -- @since 0.2
> refinePartitionBy :: (Ord a, Ord n) => (n -> a) -> Set (Set n) -> Set (Set n)
> refinePartitionBy f = collapse (union . partitionBy f) empty

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


Standard Prelude Types
=======================

A Haskell list is a Collapsible Container:

> instance Linearizable []
>     where choose (x:xs) = (x, xs)
>           choose _
>               = (error "cannot choose an element from an empty list", [])
> instance Collapsible []
>     where collapse = foldr
> instance (Eq a) => Container [a] a
>     where contains = elem
>           union = (++)
>           intersection a b = filter (isIn a) b
>           -- intersection must maintain order of B for subset to work
>           difference a b = filter (isNotIn b) a
>           empty = []
>           insert = (:)
>           isSubsetOf a b = intersection a b == b

A Set is like a list with no duplicates, so it should act similarly:

> instance Linearizable Set
>     where choose xs
>               | Set.null xs
>                   = ( error "cannot choose an element from an empty set"
>                     , Set.empty)
>               | otherwise = Set.deleteFindMin xs
> instance Collapsible Set
>     where collapse = Set.fold
>           size = fromIntegral . Set.size
> instance (Ord a) => Container (Set a) a
>     where contains            =  Set.member
>           union               =  Set.union
>           intersection        =  Set.intersection
>           difference          =  (Set.\\)
>           empty               =  Set.empty
>           insert              =  Set.insert
>           isSubsetOf          =  flip Set.isSubsetOf
>           isProperSubsetOf    =  flip Set.isProperSubsetOf
>           isSupersetOf        =  Set.isSubsetOf
>           isProperSupersetOf  =  Set.isProperSubsetOf


A new Multiset type, able to contain duplicates but still have
lookup-time logarithmic in the number of distinct elements.

> -- |A 'Multiset' is a 'Set' that may contain more than one instance
> -- of any given element.
> newtype Multiset a = Multiset (Set (a, Integer)) deriving (Eq, Ord)

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

> -- |A specialization of 'fromCollapsible'
> -- with time complexity \(O(n)\),
> -- where \(n\) is the number of distinct elements in the source.
> setFromMultiset :: Multiset a -> Set a
> setFromMultiset (Multiset a) = Set.mapMonotonic fst a

> instance Linearizable Multiset
>     where choose (Multiset xs)
>               | Set.null xs
>                   =  ( error
>                        "cannot choose an element from an empty multiset"
>                      , Multiset Set.empty)
>               | m == 1       =  (a, f as)
>               | otherwise    =  (a, f ((a, pred m) : as))
>               where ((a,m):as) = Set.toAscList xs
>                     f = Multiset . Set.fromDistinctAscList
> instance Collapsible Multiset
>     where size (Multiset xs) = fromIntegral . sum . map snd $ Set.toList xs
>           collapse f x (Multiset xs)
>               = collapse f x .
>                 concatMap (uncurry (flip replicate) .
>                            fmap fromIntegral) $
>                 Set.toAscList xs
> instance Ord a => Container (Multiset a) a
>     where contains x = contains x . setFromMultiset
>           insert x (Multiset xs) = Multiset (insert newX noX)
>               where hasX = keep ((== x) . fst) xs
>                     noX  = difference xs hasX
>                     newX = Set.fold add (x, 1) hasX
>                     add (a, c1) (_, c2) = (a, c1 + c2)
>           empty = Multiset empty
>           union (Multiset xs) (Multiset ys)
>               = Multiset (Set.fromDistinctAscList zs)
>                 where xs' = Set.toAscList xs
>                       ys' = Set.toAscList ys
>                       zs  = unionSortedMultis xs' ys'
>           intersection (Multiset xs) (Multiset ys)
>               = Multiset (Set.fromDistinctAscList zs)
>                 where xs' = Set.toAscList xs
>                       ys' = Set.toAscList ys
>                       zs  = intersectSortedMultis xs' ys'
>           difference (Multiset xs) (Multiset ys)
>               = Multiset (Set.fromDistinctAscList zs)
>                 where xs' = Set.toAscList xs
>                       ys' = Set.toAscList ys
>                       zs  = differenceSortedMultis xs' ys'

#if MIN_VERSION_base(4,9,0)
> instance Ord a => Semigroup (Multiset a)
>     where (<>) = mappend
#endif

> instance Ord a => Monoid (Multiset a)
>     where mempty = empty
>           mappend = union

> instance Show a => Show (Multiset a)
>     where showsPrec p m = showParen (p > 10) $
>                           showString "multisetFromList " .
>                           shows (collapse (:) [] m)
> instance (Ord a, Read a) => Read (Multiset a)
>     where readsPrec p = readParen (p > 10) $ \r ->
>                         do ("multisetFromList", s) <- lex r
>                            (xs, t) <- reads s
>                            return (multisetFromList xs, t)

> -- |A specialization of 'fromCollapsible'.
> multisetFromList :: Ord a => [a] -> Multiset a
> multisetFromList = fromCollapsible

> unionSortedMultis :: Ord a =>
>                      [(a, Integer)] -> [(a, Integer)] -> [(a, Integer)]
> unionSortedMultis xs [] = xs
> unionSortedMultis [] ys = ys
> unionSortedMultis (x:xs) (y:ys)
>     | fst x < fst y  =  x : unionSortedMultis xs (y:ys)
>     | fst x > fst y  =  y : unionSortedMultis (x:xs) ys
>     | otherwise      =  unionSortedMultis ((fst x, snd x + snd y) : xs) ys

> intersectSortedMultis :: Ord a =>
>                          [(a, Integer)] -> [(a, Integer)] -> [(a, Integer)]
> intersectSortedMultis _ [] = []
> intersectSortedMultis [] _ = []
> intersectSortedMultis (x:xs) (y:ys)
>     | fst x < fst y  =  intersectSortedMultis xs (y:ys)
>     | fst x > fst y  =  intersectSortedMultis (x:xs) ys
>     | otherwise      =  (fst x, min (snd x) (snd y)) :
>                         intersectSortedMultis xs ys

> differenceSortedMultis :: Ord a =>
>                           [(a, Integer)] -> [(a, Integer)] -> [(a, Integer)]
> differenceSortedMultis xs [] = xs
> differenceSortedMultis [] _  = []
> differenceSortedMultis (x:xs) (y:ys)
>     | fst x < fst y   =  x : differenceSortedMultis xs (y:ys)
>     | fst x > fst y   =  differenceSortedMultis (x:xs) ys
>     | snd x <= snd y  =  differenceSortedMultis xs ys
>     | otherwise       =  (fst x, snd x - snd y) :
>                          differenceSortedMultis xs ys


Subsets sorted by increasing and decreasing size
================================================

> -- |Wrap a 'Collapsible' type to sort in order of increasing size.
> -- For elements of the same size, treat them normally.
> newtype IncreasingSize x = IncreasingSize
>     { getIncreasing :: x } deriving (Eq, Read, Show)

> -- |Wrap a 'Collapsible' type to sort in order of decreasing size.
> -- For elements of the same size, treat them normally.
> newtype DecreasingSize x = DecreasingSize
>     { getDecreasing :: x } deriving (Eq, Read, Show)

> instance (Collapsible x, Ord (x a)) => Ord (IncreasingSize (x a))
>     where compare (IncreasingSize x) (IncreasingSize y)
>               = case compare (isize x) (isize y)
>                 of LT  ->  LT
>                    GT  ->  GT
>                    _   ->  compare x y

> instance (Collapsible x, Ord (x a)) => Ord (DecreasingSize (x a))
>     where compare (DecreasingSize x) (DecreasingSize y)
>               = case compare (isize x) (isize y)
>                 of LT  ->  GT
>                    GT  ->  LT
>                    _   ->  compare x y

> instance Functor IncreasingSize
>     where fmap f (IncreasingSize x) = IncreasingSize (f x)

> instance Functor DecreasingSize
>     where fmap f (DecreasingSize x) = DecreasingSize (f x)


Miscellaneous functions
=======================

> -- |Translate elements.  All instances of elements of the search set
> -- are replaced by the corresponding elements of the replacement set
> -- in the given string.  If the replacement set is smaller than the
> -- search set, it is made longer by repeating the last element.
> --
> -- >>> tr "aeiou" "x" "colorless green ideas"
> -- "cxlxrlxss grxxn xdxxs"
> -- >>> tr "abcdefghijklmnopqrstuvwxyz" "nopqrstuvwxyzabcdefghijklm" "cat"
> -- "png"
> tr :: (Container (s a) a, Collapsible s, Eq a) => [a] -> [a] -> s a -> s a
> tr search replace xs = tmap translate xs
>     where translate x = snd . last . ((x, x) :) . keep ((== x) . fst) $
>                         zip search (makeInfinite replace)
>           makeInfinite []      =  []
>           makeInfinite (y:[])  =  repeat y
>           makeInfinite (y:ys)  =  y : makeInfinite ys

A fast method to extract elements from a set
that works to find elements whose image under a monotonic function
falls within a given range.
The precondition that for all x,y in xs, x < y ==> f x <= f y
is not checked.

#if MIN_VERSION_containers(0,5,8)
From containers-0.5.8, a range can be extracted from a Set in
guaranteed log-time.

> extractRange :: (Ord a, Ord b) => (a -> b) -> b -> b -> Set a -> Set a
> extractRange f m n = Set.takeWhileAntitone ((<= n) . f) .
>                      Set.dropWhileAntitone ((< m) . f)

#else
If we are using an older version of the containers library
that doesn't contain the necessary functions, we can make do
with a variant that is at least still faster than filter.

> extractRange :: (Ord a, Ord b) => (a -> b) -> b -> b -> Set a -> Set a
> extractRange f m n = Set.fromDistinctAscList .
>                      takeWhile ((<= n) . f) . dropWhile ((< m) . f) .
>                      Set.toAscList

#endif

> -- |A fast method to extract elements from a set
> -- whose image under a monotonic function is a certain value.
> -- The precondition that the function is monotonic is not checked.
> --
> -- @since 0.2
> extractMonotonic :: (Ord a, Ord b) => (a -> b) -> b -> Set a -> Set a
> extractMonotonic f a = extractRange f a a
