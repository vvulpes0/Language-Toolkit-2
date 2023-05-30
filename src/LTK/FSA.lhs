> {-# OPTIONS_HADDOCK show-extensions #-}
> {-# Language
>   CPP,
>   FlexibleContexts,
>   FlexibleInstances,
>   MultiParamTypeClasses,
>   Trustworthy
>   #-}

#if !defined(MIN_VERSION_base)
# define MIN_VERSION_base(a,b,c) 0
#endif

> {-|
> Module    : LTK.FSA
> Copyright : (c) 2014-2023 Dakotah Lambert
> License   : MIT

> The purpose of this module is to define an interface to a generic,
> reusable impementation of finite-state automata (FSAs).  The primary
> motivation for this is to allow for efficient analysis of stringsets
> in a linguistic context, although the nature of the project should 
> allow more general use.
> -}
> module LTK.FSA
>        ( FSA(..)
>        , states
>        , isNull
>        , follow
>        , accepts
>        -- * Constructing simple automata
>        , totalWithAlphabet
>        , emptyWithAlphabet
>        , emptyLanguage
>        , singletonWithAlphabet
>        , singletonLanguage
>        -- * Derived automata
>        , brzozowskiDerivative
>        , loopify
>        , tierify
>        , neutralize
>        , quotLeft
>        , quotMid
>        , quotRight
>        , kleeneClosure
>        , powersetGraph
>        , syntacticMonoid
>        , residue
>        , coresidue
>        -- * Primitive ideals
>        , primitiveIdeal2
>        , primitiveIdealL
>        , primitiveIdealR
>        -- * Transformations
>        , flatIntersection
>        , flatUnion
>        , flatShuffle
>        , LTK.FSA.reverse
>        , autDifference
>        , autShuffle
>        , complement
>        , complementDeterministic
>        , determinize
>        -- ** Minimization
>        , minimize
>        , minimizeDeterministic
>        , normalize
>        , trimUnreachables
>        -- *** Equivalence Classes
>        , minimizeOver
>        , nerode
>        , hEquivalence
>        , jEquivalence
>        , trivialUnder
>        -- ** Alphabetic Transformations
>        , extendAlphabetTo
>        , semanticallyExtendAlphabetTo
>        , contractAlphabetTo
>        , forceAlphabetTo
>        , desemantify
>        , renameSymbolsBy
>        -- ** Transformations of 'State' labels
>        , renameStatesBy
>        , renameStates
>        -- * Miscellaneous
>        , State(..)
>        , Symbol(..)
>        , unsymbols
>        , Transition(..)
>        , module LTK.Containers
>        ) where

> import Control.DeepSeq (NFData, rnf)
#if !MIN_VERSION_base(4,8,0)
> import Control.Applicative (Applicative, pure, (<*>))
> import Data.Functor ((<$>))
> import Data.Monoid (Monoid, mappend, mempty)
#endif
#if MIN_VERSION_base(4,9,0)
#if !MIN_VERSION_base(4,11,0)
> import safe Data.Semigroup (Semigroup, (<>))
#endif
#endif
> import Data.Maybe (fromMaybe)
> import Data.Set (Set)
> import qualified Data.Set as Set
> import qualified Data.Map.Lazy as Map

> import Control.Parallel (par, pseq)

> import LTK.Containers


Data Structures
===============

An FSA has four main parts:

* a set of symbols representing its alphabet
* a set of edges that describe transitions from state to state
* a set of initial states, from which computations begin
* a set of final states, which determine computational success

Further, given an FSA F, if for every symbol a in the alphabet of F
and for every state q in the set of states in F, there exists exactly
one edge exiting q labelled with a, and if F has exactly one initial
state, then F can be described as a deterministic finite-state
automaton, or DFA.  Determinism allows for useful optimizations in
some operations, but can be slow to verify.  This module sacrifices
space for speed, treating determinism as a property of the datatype
itself.

> -- |A finite-state automaton (FSA) is represented by a directed
> -- graph, the edges of which are labelled by formal symbols.
> data FSA n e
>     = FSA
>       { -- |@since 0.3
>         sigma            ::  Set e
>       , transitions      ::  Set (Transition n e)
>       , initials         ::  Set (State n)
>       , finals           ::  Set (State n)
>       , isDeterministic  ::  Bool
>       }
>     deriving (Show, Read)

> -- |The collection of all states in an FSA.
> states :: (Ord e, Ord n) => FSA n e -> Set (State n)
> states f = unionAll [initials f, finals f, others]
>    where others           = collapse extractStates empty ts
>          extractStates t  = insert (source t) . insert (destination t)
>          ts               = transitions f

> -- |An automaton accepting every string over a given alphabet.
> totalWithAlphabet :: (Ord e, Enum n, Ord n) => Set e -> FSA n e
> totalWithAlphabet as = FSA as trans (singleton q) (singleton q) True
>     where trans  = Set.mapMonotonic
>                    (flip (`Transition` q) q . Symbol)
>                    as
>           q      = State $ toEnum 0

> -- |An automaton accepting no strings over a given alphabet.
> emptyWithAlphabet :: (Ord e, Enum n, Ord n) => Set e -> FSA n e
> emptyWithAlphabet as = (totalWithAlphabet as) {finals = empty}

> -- |A specialization of 'emptyWithAlphabet' where the alphabet
> -- is itself empty.
> emptyLanguage :: (Ord e, Ord n, Enum n) => FSA n e
> emptyLanguage = emptyWithAlphabet empty

A singleton FSA is one that accepts exactly one (possibly-empty)
string.  The number of states in such an FSA is equal to the length of
the string plus two.

> -- |An automaton that accepts only the given string,
> -- over a given alphabet.
> singletonWithAlphabet :: (Ord e, Enum n, Ord n) =>
>                          Set e -> [e] -> FSA n e
> singletonWithAlphabet as str
>     = FSA
>       { sigma = as
>       , transitions = trans str
>       , initials = begins
>       , finals = fins
>       , isDeterministic = True
>       }
>     where trans xs = trans' xs (toEnum 1) `union` failTransitions
>           trans' [] n
>               = tmap (\a -> Transition (Symbol a) (State n) qfail) as
>           trans' (x:xs) n
>               = let m = succ n
>                 in union (trans' xs m) $
>                    Set.mapMonotonic
>                    (\y ->
>                     Transition (Symbol y) (State n) $
>                     if x == y then State m else qfail
>                    ) as
>           qfail = State $ toEnum 0
>           failTransitions
>               = Set.mapMonotonic
>                 (\a -> Transition (Symbol a) qfail qfail)
>                 as
>           begins  =  singleton (State $ toEnum 1)
>           qlast   =  (+ 1) $ size str
>           fins    =  singleton (State $ toEnum qlast)

> -- |An automaton that accepts only the given string,
> -- over the minimal alphabet required to represent this string.
> singletonLanguage :: (Ord e, Enum n, Ord n) => [e] -> FSA n e
> singletonLanguage s = singletonWithAlphabet (Set.fromList s) s


Formal Symbols
--------------

The edges of an FSA are labelled by either a formal symbol or the
pseudo-symbol Epsilon.  Specifically, an edge labelled by Epsilon
represents a transition that may occur without consuming any further
input.


> -- |The label of a 'Transition'.
> data Symbol e = Epsilon  -- ^The edge may be taken without consuming input.
>               | Symbol e -- ^The edge requires consuming this symbol.
>               deriving (Eq, Ord, Read, Show)

The Symbol type is used to adjoin Epsilon to an alphabet.  We often
want only the real portion of a string, where instances of Epsilon are
not important.  The 'unsymbols' function does this transformation:

    unsymbols [Symbol 'a', Epsilon, Symbol 'b', Epsilon] :: [Char]

becomes simply

    "ab".

This transformed a [Symbol Char] to a [Char].  The container type need not
be the same though:

    unsymbols [Symbol 'a', Epsilon, Symbol 'b', Epsilon] :: Set Char

becomes

    fromList ['a', 'b'].

> -- |Remove 'Epsilon' from a 'Collapsible' of 'Symbol'
> -- and present the unwrapped results as a new 'Container'.
> unsymbols :: (Collapsible s, Container c e, Monoid c) => s (Symbol e) -> c
> unsymbols = collapse (mappend . f) mempty
>     where f (Symbol x)  =  singleton x
>           f _           =  empty

States
------

> -- |A vertex of the graph representation of an 'FSA' is a 'State',
> -- which can be labelled with any arbitrary value, so long as every
> -- vertex of a single automaton is labelled with a distinct value
> -- of the same type.
> newtype State n = State {nodeLabel :: n} deriving (Eq, Ord, Read, Show)

Transitions
-----------

If a state is the vertex of a graph, then a transition is its edge.
Since an FSA is represented by a directed graph, there are three
components to a transition: an edge label, and two states.  If a
computation in the first state encounters a symbol matching the
transition's edge label, then it moves to the second state.

> -- |The edges of an 'FSA'.
> data Transition n e
>     = Transition
>       { edgeLabel   :: Symbol e
>       , source      :: State n
>       , destination :: State n
>       }
>     deriving (Eq, Ord, Show, Read)


Class Instances
===============

Here we define class instances for FSAs and their component types.


Symbol
------

> instance Functor Symbol
>     where fmap _ Epsilon     =  Epsilon
>           fmap f (Symbol e)  =  Symbol (f e)

> instance (NFData e) => NFData (Symbol e)
>     where rnf Epsilon     =  ()
>           rnf (Symbol e)  =  rnf e


State
-----

> instance Functor State
>     where fmap f = State . f . nodeLabel

> instance Applicative State
>     where pure   =  State
>           (<*>)  =  fmap . nodeLabel

> instance Monad State
>     where a >>= f  =  f $ nodeLabel a
#if !MIN_VERSION_base(4,8,0)
>           return    =  pure
#endif

#if MIN_VERSION_base(4,9,0)
Semigroup instance to satisfy base-4.11

> instance (Semigroup n) => Semigroup (State n)
>     where (<>) = fmap . nodeLabel . fmap (<>)
#endif

> instance (Monoid n) => Monoid (State n)
>     where mempty   =  State mempty

#if MIN_VERSION_base(4,11,0)
> -- mappend will eventually be removed
#elif MIN_VERSION_base(4,9,0)
>           mappend  = (<>)
#else
>           mappend  =  fmap . nodeLabel . fmap mappend
#endif

> instance (NFData n) => NFData (State n)
>     where rnf (State n) = rnf n


Transition
----------

> instance (NFData n, NFData e) => NFData (Transition n e)
>     where rnf t = rnf (edgeLabel t) `seq`
>                   rnf (source t)    `seq`
>                   rnf (destination t)

> newtype Noitisnart e n = Noitisnart { transition :: Transition n e }

> instance Functor (Transition n)
>     where fmap f t = t { edgeLabel = fmap f (edgeLabel t) }

> instance Functor (Noitisnart e)
>     where fmap f = Noitisnart . fmap' . transition
>               where fmap' t
>                         = t { source       =  fmap f (source t)
>                             , destination  =  fmap f (destination t)
>                             }


FSA
---

FSAs represent languages, so it makes sense to use equivalence of the
represented languages as the criterion for equivalence of the FSAs
themselves.  First, an FSA represents the empty language if it has
no reachable accepting states:

> -- |True iff the input accepts no strings.
> isNull :: (Ord e, Ord n) => FSA n e -> Bool
> isNull = (== empty) . finals . trimUnreachables

Two FSAs are considered equal iff they are isomorphic.

> instance (Ord e, Ord n) => Eq (FSA n e)
>     where a == b = isomorphic (normalize a) (normalize b)

Calls to `isomorphic` should work for NFAs as well as DFAs, but in the
current implementation, in general, will not.  This is because
multiple start states are combined with the cartesian product to
create c, rather than mapped from a to their counterparts in b, a much
harder problem.

> isomorphic :: (Ord e, Ord n1, Ord n2) => FSA n1 e -> FSA n2 e -> Bool
> isomorphic a b = (alphabet a         == alphabet b)          &&
>                  (isize (initials a) == isize (initials b))  &&
>                  (isize (finals a)   == isize (finals b))    &&
>                  (isize (states a)   == isize (states b))    &&
>                  (isize (initials a) == isize (initials c))  &&
>                  (isize (finals a)   == isize (finals c))    &&
>                  (isize (states a)   == s)
>     where c  =  autUnion a b
>           s  =  isize . keep (State (Nothing, Nothing) /=) $ states c

A Set of FSAs could be useful, and an Ord instance is needed for that.
If two automata are equal, they should certainly compare EQ.
If A is a subset of B, compare A B ought be LT and the reverse GT.
When neither is a subset of the other, they are incomparable by this
measure, so instead they are compared by a standard Haskell comparison
of tuples consisting of their alphabets, transitions, initial states,
and final states.

> instance (Ord e, Ord n) => Ord (FSA n e)
>     where compare a b
>               | a == b                  =  EQ
>               | isSubsetOf (f b) (f a)  =  LT
>               | isSubsetOf (f a) (f b)  =  GT
>               | otherwise               =  compare (g a) (g b)
>               where f :: (Ord e, Ord n) => FSA n e -> FSA Integer e
>                     f = renameStates
>                     g x = (alphabet x, transitions x, initials x, finals x)

> instance (Enum n, Ord n, Ord e) => Container (FSA n e) [e]
>     where isEmpty       =  isNull
>           isIn          =  accepts
>           union         =  apply autUnion
>           intersection  =  apply autIntersection
>           difference    =  apply autDifference
>           empty         =  emptyLanguage
>           singleton     =  singletonLanguage
>           symmetricDifference
>               =  apply autSymmetricDifference

Here we consider FSAs to be Semigroups (and Monoids) under concatenation

#if MIN_VERSION_base(4,9,0)
Semigroup instance to satisfy base-4.9

> instance (Enum n, Ord n, Ord e) => Semigroup (FSA n e)
>     where (<>) = apply autConcatenation
#endif

> instance (Enum n, Ord n, Ord e) => Monoid (FSA n e)
>     where mempty   =  singletonLanguage empty

#if MIN_VERSION_base(4,11,0)
-- mappend will eventually be removed
#elif MIN_VERSION_base(4,9,0)

>           mappend = (<>)

#else

>           mappend  =  apply autConcatenation

#endif

> apply :: (Ord e, Ord n1, Ord n2, Enum n2) =>
>          (a -> b -> FSA n1 e) -> a -> b -> FSA n2 e
> apply f = curry (renameStates . uncurry f)

> pfold :: (a -> a -> a) -> [a] -> a
> pfold = fmap (. treeFromList) treeFold

It is better to use flatIntersection and flatUnion than the
appropriate fold, because the flat- functions take advantage
of parallelism if possible.

> -- |Intersect all given automata, in parallel if possible.
> -- An empty intersection is undefined.
> -- In theory it should be the total language over the
> -- total alphabet, but the latter cannot be defined.
> -- Intermediate results are evaluated to normal form.
> flatIntersection :: (Enum n, Ord n, NFData n, Ord e, NFData e) =>
>                     [FSA n e] -> FSA n e
> flatIntersection [] = error "Cannot take a nullary intersection"
> flatIntersection xs = pfold i xs
>     where i a b = let x = renameStates . minimize $ autIntersection a b
>                   in rnf x `seq` x

> -- |Union all given automata, in parallel if possible.
> -- An empty union is defined as the empty language over
> -- an empty alphabet.
> -- Intermediate results are evaluated to normal form.
> flatUnion :: (Enum n, Ord n, NFData n, Ord e, NFData e) =>
>              [FSA n e] -> FSA n e
> flatUnion []  =  emptyLanguage
> flatUnion xs  =  pfold u xs
>     where u a b = let x = renameStates . minimize $ autUnion a b
>                   in rnf x `seq` x

> -- |Shuffle all given automata, in parallel if possible.
> -- An empty shuffle is defined as the single language over
> -- an empty alphabet containing only the empty string.
> -- Intermediate results are evaluated to normal form.
> flatShuffle :: (Enum n, Ord n, NFData n, Ord e, NFData e) =>
>                [FSA n e] -> FSA n e
> flatShuffle []  =  singletonLanguage []
> flatShuffle xs  =  pfold s xs
>     where s a b = let x = renameStates . minimize $ autShuffle a b
>                   in rnf x `seq` x

> instance (NFData n, NFData e) => NFData (FSA n e)
>     where rnf (FSA a t i f d)
>               = rnf a `seq` rnf t `seq` rnf i `seq` rnf f `seq` rnf d

> instance HasAlphabet (FSA n)
>     where alphabet = sigma


Acceptance and the Transition Function
======================================

To determine whether an FSA accepts a string of Symbols, there must
exist a mechanism to determine which State to enter upon consuming a
Symbol.  The set of Transitions describes the map, and we will use
that to define the transition function.

> data ID n e = ID (State n) [Symbol e] deriving (Eq, Ord, Read, Show)

> state :: ID n e -> State n
> state (ID a _) = a

> string :: ID n e -> [Symbol e]
> string (ID _ xs) = xs

> epsilonClosure :: (Ord e, Ord n) =>
>                   FSA n e -> Set (State n) -> Set (State n)
> epsilonClosure fsa qs
>     | isDeterministic fsa  = qs
>     | otherwise            = epsilonClosure' qs qs
>     where epsilons = extractMonotonic edgeLabel Epsilon (transitions fsa)
>           epsilonClosure' seen new
>               | isEmpty new  =  seen
>               | otherwise    =  epsilonClosure'
>                                 (seen `union` closure)
>                                 (difference closure seen)
>               where seens    =  keep (isIn new . source) epsilons
>                     closure  =  tmap destination seens

> step :: (Ord e, Ord n) => FSA n e -> Set (ID n e) -> Set (ID n e)
> step fsa ids
>     | filteredIDs == empty  =  empty
>     | otherwise             =  collapse (union . next) empty filteredIDs
>     where ts = transitions fsa
>           filterID i = ID (state i) (keep (/= Epsilon) (string i))
>           filteredIDs = tmap filterID ids
>           next i
>               | null s     = tmap (`ID` []) closure
>               | otherwise  = tmap (`ID` tail s) outStates
>               where s = string i
>                     closure = epsilonClosure fsa (singleton (state i))
>                     outStates  = epsilonClosure fsa
>                                  . tmap destination
>                                  . keep (isIn closure . source)
>                                  $ extractMonotonic edgeLabel
>                                    (head s) ts

We should not have to produce IDs ourselves.  We can define the transition
function `delta` from an FSA, a symbol, and a state to a set of states:

> delta :: (Ord e, Ord n) =>
>          FSA n e -> Symbol e -> Set (State n) -> Set (State n)
> delta f x = tmap state . step f . Set.mapMonotonic (`ID` [x])

> compute :: (Ord e, Ord n) => FSA n e -> [Symbol e] -> Set (ID n e)
> compute fsa str = until (allS (null . string)) (step fsa) initialIDs
>     where initialIDs = Set.mapMonotonic (`ID` str) expandedInitials
>           expandedInitials = epsilonClosure fsa $ initials fsa

> accepts :: (Ord e, Ord n) => FSA n e -> [e] -> Bool
> accepts fsa = anyS (isIn (finals fsa)) . tmap state
>               . compute fsa . tmap Symbol

The Brzozowski derivative of an FSA with respect to some string
is an FSA representing the valid continuations from that string.

> -- |Return an FSA representing possible continuations from a given
> -- sequence of symbols.  If the input automaton is not complete
> -- then the output may have no states when given incompatible input.
> --
> -- @since 1.0
> brzozowskiDerivative :: (Ord e, Ord n) => [e] -> FSA n e -> FSA n e
> brzozowskiDerivative xs f = trimUnreachables
>                             $ f { initials = tmap state . compute f
>                                              $ tmap Symbol xs}

A generalization of the Brzozowski derivative is the left quotient
of a language by another language.  In fact, the following operations,
quotLeft, quotRight, and quotMid, offer a start toward computing
in the free group rather than the free monoid generated by the alphabet.

> -- |Return an FSA representing possible continuations in the second
> -- language from strings in the first language.
> -- In other words, @quotLeft a b@ returns \(\{w : x\in a, xw\in b\}\).
> --
> -- @since 1.0
> quotLeft :: (Ord e, Ord n1, Ord n2) =>
>             FSA n1 e -> FSA n2 e
>          -> FSA (Maybe (Either n1 ()), Maybe n2) e
> quotLeft a b = p { initials = i
>                  , isDeterministic = d }
>     where a' = x (autConcatenation (trimUnreachables a) t)
>           x m = m {finals = finals m `Set.union` tmap State f}
>           t  = totalWithAlphabet (sigma a `Set.union` sigma b)
>           p  = autIntersection a' (trimUnreachables b)
>           f  = tmap (Left . nodeLabel) $ finals a
>           i  = keep ( maybe False (`Set.member` f)
>                     . fst . nodeLabel) $ states p
>           d  = isDeterministic p && Set.size i == 1

Doing quotRight similarly should be fairly simple,
but it's easier to just do left-quotient on reversals.

> -- |Return an FSA representing possible strings in the first language
> -- which end with a string in the second language.
> -- In other words, @quotRight a b@ is \(\{w : wx\in a, x\in b\}\).
> --
> -- @since 1.0
> quotRight :: (Ord e, Ord n1, Ord n2) =>
>              FSA n1 e -> FSA n2 e -> FSA Integer e
> quotRight a b = normalize . LTK.FSA.reverse
>                 $ quotLeft (LTK.FSA.reverse b) (LTK.FSA.reverse a)

> -- |@quotMid a b c@ is \(\{wz : wx\in a, yx\in b, yz\in c\}\).
> -- This lifts strings to a group, placing b-inverse between a and c.
> -- The time complexity of this function is abysmal,
> -- performing a left and a right quotient for each state in @b@.
> --
> -- @since 1.0
> quotMid :: (Ord e, Ord n1, Ord n2, Ord n3) =>
>            FSA n1 e -> FSA n2 e -> FSA n3 e -> FSA Integer e
> quotMid a b c = unionAll . map bridge . Set.toList $ states b'
>     where a' = normalize a
>           b' = normalize b
>           c' = normalize c
>           bridge n = let b1 = b' {initials = Set.singleton n}
>                          b2 = b' {finals = Set.singleton n}
>                      in renameStates
>                         (quotRight a' b1
>                          `autConcatenation` quotLeft b2 c')


Logical Operators
=================

> combine :: State a -> State b -> State (a, b)
> combine q1 q2 = (,) <$> q1 <*> q2

> makePairs :: (Ord a, Ord b) => Set a -> Set b -> Set (a, b)
> makePairs xs ys = collapse (union . f) empty xs
>     where f x = Set.mapMonotonic ((,) x) ys

> makeJustPairs :: (Ord a, Ord b) =>
>                  Set (State a) -> Set (State b) ->
>                  Set (State (Maybe a), State (Maybe b))
> makeJustPairs xs ys = makePairs (justify xs) (justify ys)
>     where justify = Set.mapMonotonic (fmap Just)

The Cartesian construction for automata is closely related to the
tensor product of graphs.  Given two automata, M1 and M2, we construct
a new automata M3 such that:

* states(M3) is a subset of the Cartesian product of
  (states(M1) or Nothing) with (states(M2) or Nothing)
* Any lack of explicit transition in either M1 or M2 is
  considered a transition to Nothing in that automaton.
  This effectively makes each input total.
* If (q1, q2) and (q1', q2') are states of M3,
  then there is a transition from (q1, q2) to (q1', q2')
  iff there exists both a transition from q1 to q1' in M1
  and a transition from q2 to q2' in M2.

This construction results in an automaton that tracks a string through
both of its input automata.  States may be tagged as accepting to
obtain either an intersection or a union:

* For a intersection, a state (q1, q2) in states(M3) is accepting
  iff q1 is accepting in M1 and q2 is accepting in M2.
* For a union, a state (q1, q2) in states(M3) is accepting
  iff q1 is accepting in M1 or q2 is accepting in M2.

In either case, the set of initial states in the new automaton is
equal to the Cartesian product of the initial states of M1 with
the initial states of M2.

The Cartesian construction preserves determinism
and guarantees totality of the result.

> cartesianConstruction :: (Ord e, Ord n1, Ord n2) =>
>                          (Bool -> Bool -> Bool) -> FSA n1 e -> FSA n2 e ->
>                          FSA (Maybe n1, Maybe n2) e
> cartesianConstruction isFinal' f1 f2
>     = FSA
>       { sigma            =  alpha
>       , transitions      =  ts
>       , initials         =  qi
>       , finals           =  qf
>       , isDeterministic  =  isDet
>       }
>     where alpha  =  alphabet f1 `union` alphabet f2
>           isDet  =  isDeterministic f1 && isDeterministic f2
>           qi     =  Set.mapMonotonic (uncurry combine) $
>                     makeJustPairs (initials f1) (initials f2)
>           isFinal q
>               =  let (a,b)  =  nodeLabel q
>                      f m    =  maybe False (isIn (finals m) . State)
>                  in isFinal' (f f1 a) (f f2 b)
>           (_,_,ts,qf)
>               = until
>                 (\(new, _, _, _) -> isEmpty new)
>                 (\(new, prev, partial, fins) ->
>                  let exts   =  collapse (union . extensions)
>                                empty new
>                      seen   =  union new prev
>                      dests  =  tmap destination exts
>                      fins'  =  keep isFinal dests
>                  in ( difference dests seen
>                     , seen
>                     , exts `union` partial
>                     , fins `union` fins'
>                     )
>                 )
>                 (qi, empty, empty, keep isFinal qi)
>           extensions q =  collapse (union . exts' q) empty $
>                           Set.mapMonotonic Symbol alpha
>           exts' q x    =  Set.mapMonotonic (Transition x q) $ nexts x q
>           nexts x q    =  let n1   =  nexts' x f1 $ fmap fst q
>                               n2   =  nexts' x f2 $ fmap snd q
>                               f a  =  Set.mapMonotonic (combine a) n2
>                           in collapse (union . f) empty n1
>           nexts' x f   =  maybe
>                           (singleton $ State Nothing)
>                           (mDests x f . State) . nodeLabel
>           mDests x f q
>               | isEmpty exts  =  singleton $ State Nothing
>               | otherwise     =  Set.mapMonotonic (fmap Just) exts
>               where exts = delta f x $ singleton q

> autIntersection :: (Ord e, Ord n1, Ord n2) => FSA n1 e -> FSA n2 e ->
>                    FSA (Maybe n1, Maybe n2) e
> autIntersection = cartesianConstruction (&&)

> autUnion :: (Ord e, Ord n1, Ord n2) => FSA n1 e -> FSA n2 e ->
>             FSA (Maybe n1, Maybe n2) e
> autUnion = cartesianConstruction (||)

For the difference A - B, the final states are those that are
accepting in A and non-accepting in B.

Note that the relative complement requires functionality.  Consider
the case of (A - B) where B is nondeterministic in such a way that
there exists a string w for which a computation leads to both an
accepting state qa and a nonaccepting state qn.  Suppose that w leads
to an accepting state in A, qf.  Then the cartesian construction will
contain both (qf, qa) and (qf, qn).

When selecting states to be accepting, (qf, qn) will be included since
qn is nonaccepting in B, and (qf, qn) will be excluded since qa is
accepting in B.  This is not what we want, as it means that w is still
accepted.  Thus we cannot use the cartesian construction to gain an
advantage over the naive implementation (A & not B).

> autDifference :: (Ord e, Ord n1, Ord n2) => FSA n1 e -> FSA n2 e ->
>                  FSA (Maybe n1, Maybe (Set n2)) e
> autDifference = fmap (. complement) autIntersection

Much like the one-sided difference, the symmetric difference of two
automata relies on determinism.

> autSymmetricDifference :: (Ord e, Ord n1, Ord n2) => FSA n1 e -> FSA n2 e ->
>                           FSA (Maybe (Maybe n1, Maybe n2),
>                                Maybe (Set (Maybe n1, Maybe n2))) e
> autSymmetricDifference f1 f2
>     = autDifference (autUnion f1 f2) $ autIntersection f1 f2

For a total functional FSA, the complement can be obtained by simply
inverting the notion of accepting states.  Totality is necessary, as
any sink-states in the original will be accepting in the complement.
Functionality is necessary, as:

        -> (0)  -a-> ((1)) -a)        (x) is a state, ((x)) is accepting
            |                         -a-> represents a transition on a
            +----a->  (2)  -a)        -a) represents a self-edge on a

becomes under this construction:

        ->((0)) -a->  (1)  -a)
           |
           +-----a-> ((2)) -a)

and the string "a" is accepted in both.

> -- |Returns an 'FSA' accepting all and only those strings not
> -- accepted by the input.
> complement :: (Ord e, Ord n) => FSA n e -> FSA (Set n) e
> complement = complementDeterministic . determinize

> -- |Returns the 'complement' of a deterministic 'FSA'.
> -- The precondition that the input is deterministic
> -- is not checked.
> complementDeterministic :: (Ord e, Ord n) => FSA n e -> FSA n e
> complementDeterministic f = f { finals = difference (states f) (finals f) }

> -- |@(residue a b)@ is equivalent to @(difference a b)@.
> -- In the context of an approximation and its source,
> -- represents the strings accepted by the approximation
> -- that should not be.
> residue :: (Ord n, Ord e, Enum n) => FSA n e -> FSA n e -> FSA n e
> residue = curry (renameStates . minimize . uncurry difference)

> -- |@(coresidue a b)@ is equivalent to @(complement (residue a b))@.
> -- In the context of an approximation and its source,
> -- represents unmet constraints of the source.
> coresidue :: (Ord n, Ord e, Enum n) => FSA n e -> FSA n e -> FSA n e
> coresidue a = renameStates . minimize .
>               union (renameStates $ complement a)

The shuffle product of two languages can be constructed
similarly to their intersection.
The difference is that in the standard Cartesian construction,
an edge follows its labeling symbol in both source automata,
while in the shuffle product it follows in only one.
Thus rather than one out-edge per symbol per state,
there are two.

> -- |Returns the shuffle product of its two input autamata.
> autShuffle :: (Ord e, Ord n1, Ord n2) => FSA n1 e -> FSA n2 e
>            -> FSA (Maybe n1, Maybe n2) e
> autShuffle f1 f2 = FSA { sigma            =  alpha
>                        , transitions      =  ts
>                        , initials         =  qi
>                        , finals           =  qf
>                        , isDeterministic  =  False
>                        }
>     where alpha  =  alphabet f1 `union` alphabet f2
>           qi     =  Set.mapMonotonic (uncurry combine)
>                     $ makeJustPairs (initials f1) (initials f2)
>           isFinal q
>               = let (a,b)  =  nodeLabel q
>                     f m    =  maybe False (isIn (finals m) . State)
>                 in f f1 a && f f2 b
>           (_,_,ts,qf)
>               = until
>                 (\(new, _, _, _) -> isEmpty new)
>                 (\(new, prev, partial, fins) ->
>                  let exts   =  collapse (union . extensions)
>                                empty new
>                      seen   =  new `union` prev
>                      dests  =  tmap destination exts
>                      fins'  =  keep isFinal dests
>                  in ( difference dests seen
>                     , seen
>                     , exts `union` partial
>                     , fins `union` fins'
>                     )
>                 )
>                 (qi, empty, empty, keep isFinal qi)
>           extensions q =  collapse (union . exts' q) empty
>                           $ Set.mapMonotonic Symbol alpha
>           exts' q x    =  Set.mapMonotonic (Transition x q) $ nexts x q
>           nexts x q    =  let n1 = nexts' x f1 $ fmap fst q
>                               n2 = nexts' x f2 $ fmap snd q
>                           in Set.mapMonotonic (`combine` fmap snd q) n1
>                              `union`
>                              Set.mapMonotonic (combine (fmap fst q)) n2
>           nexts' x f   =  maybe
>                           (singleton $ State Nothing)
>                           (mDests x f . State) . nodeLabel
>           mDests x f q
>               | isEmpty exts  =  singleton $ State Nothing
>               | otherwise     =  Set.mapMonotonic (fmap Just) exts
>               where exts = delta f x $ singleton q


Other Combinations
==================

> autConcatenation :: (Ord n1, Ord n2, Ord e) =>
>                     FSA n1 e -> FSA n2 e
>                  -> FSA (Either n1 n2) e
> autConcatenation f1 f2
>     = FSA
>       { sigma = alphabet f1' `union` alphabet f2'
>       , transitions
>           = unionAll
>             [ transitions f1'
>             , transitions f2'
>             , combiningTransitions
>             ]
>       , initials = initials f1'
>       , finals   = finals f2'
>       , isDeterministic = False
>       }
>     where f1' = renameStatesByMonotonic Left f1
>           f2' = renameStatesByMonotonic Right f2
>           combiningTransitions = collapse (union . cts) empty
>                                  (finals f1')
>           cts f = Set.mapMonotonic
>                   (\i ->
>                    Transition
>                    { edgeLabel = Epsilon
>                    , source = f
>                    , destination = i
>                    }
>                   )
>                   (initials f2')

> -- |The Kleene Closure of an automaton is
> -- the free monoid under concatenation generated by all strings
> -- in the automaton's represented stringset.
> -- The resulting automaton is nondeterministic.
> kleeneClosure :: (Ord n, Ord e) => FSA n e -> FSA (Either n Bool) e
> kleeneClosure f
>     = FSA
>       { sigma = alphabet f'
>       , transitions
>           = unionAll [ transitions f'
>                      , toOldInitials
>                      , toNewFinal
>                      ]
>       , initials = singleton ni
>       , finals = singleton nf
>       , isDeterministic = False
>       }
>     where f' = renameStatesByMonotonic Left f
>           ni = State (Right False)
>           nf = State (Right True)
>           toOldInitials = collapse (union . cts) empty
>                           (insert ni (finals f'))
>           cts q = tmap
>                   (\i ->
>                    Transition
>                    { edgeLabel = Epsilon
>                    , source = q
>                    , destination = i
>                    }
>                   )
>                   (initials f')
>           toNewFinal = tmap
>                        (\q ->
>                         Transition
>                         { edgeLabel = Epsilon
>                         , source = q
>                         , destination = nf
>                         }
>                        )
>                        (insert ni (finals f'))


Minimization
============

In general, operations on FSAs have run time proportional to some
(increasing) function of how many states the FSA has.  With this in
mind, we provide a function to make an FSA as small as possible
without loss of information.

We begin by constructing the set of Myhill-Nerode equivalence classes
for the states of the input FSA, then simply replace each state by its
equivalence class.

> -- |Returns a deterministic 'FSA' recognizing the same stringset
> -- as the input, with a minimal number of states.
> minimize :: (Ord e, Ord n) => FSA n e -> FSA (Set (Set n)) e
> minimize = minimizeDeterministic . determinize

> -- |Returns a deterministic 'FSA' recognizing the same stringset
> -- as the input, with a minimal number of states.
> -- The precondition that the input is deterministic
> -- is not checked.
> minimizeDeterministic :: (Ord e, Ord n) => FSA n e -> FSA (Set n) e
> minimizeDeterministic = setD . minimizeOver nerode
>     where setD f = f {isDeterministic = True}

> -- |Returns a non-necessarily deterministic 'FSA'
> -- minimized over a given relation.
> -- Some, but not all, relations do guarantee deterministic output.
> -- The precondition that the input is deterministic
> -- is not checked.
> minimizeOver :: (Ord e, Ord n) =>
>                 (FSA n e -> Set (Set (State n))) -> FSA n e -> FSA (Set n) e
> minimizeOver r fsa = FSA
>                      { sigma = alphabet fsa
>                      , transitions = trans
>                      , initials = qi
>                      , finals = fin
>                      , isDeterministic = False
>                      }
>     where classes = r fsa
>           classOf x = State . tmap nodeLabel . unionAll $
>                       keep (contains x) classes
>           qi = tmap classOf $ initials fsa
>           fin = tmap classOf $ finals fsa
>           trans = tmap
>                   (\t ->
>                    t
>                    { source = classOf (source t)
>                    , destination = classOf (destination t)
>                    }
>                   ) $ transitions fsa

> -- |Two strings \(u\) and \(v\) are equivalent iff
> -- for all strings \(w\), \(uw\) and \(vw\) lead to
> -- states in the same equivalence class.
> nerode :: (Ord e, Ord n) => FSA n e -> Set (Set (State n))
> nerode fsa = tmap eqClass sts
>     where sts = states fsa
>           i = union i' $ Set.mapMonotonic (\x -> (x, x)) sts
>           i' = difference (pairs sts) $ distinguishedPairs fsa
>           eqClass x = unionAll
>                       [ singleton x
>                       , tmap snd $ extractMonotonic fst x i
>                       , Set.mapMonotonic fst $ keep ((== x) . snd) i
>                       ]

The easiest way to construct the equivalence classes is to iteratively
build a set of known-distinct pairs.  In the beginning we know that
any accepting state is distinct from any non-accepting state.  At each
further iteration, two states p and q are distinct if there exists
some symbol x such that delta<sub>x</sub>(p) is distinct from
delta<sub>x</sub>(q).

When an iteration completes without updating the set of known-distinct
pairs, the algorithm is finished; all possible distinctions have been
discovered.  The Myhill-Nerode equivalence class of a state p, then,
is the set of states not distinct from p.

> distinguishedPairs :: (Ord e, Ord n) => FSA n e -> Set (State n, State n)
> distinguishedPairs fsa = fst result
>     where allPairs = pairs (states fsa)
>           initiallyDistinguished
>               = collapse (union . pairs' (finals fsa)) empty .
>                 difference (states fsa) $ finals fsa
>           f d (a, b) = areDistinguishedByOneStep fsa d a b
>           result = until
>                    (\(x, y) -> isize x == isize y)
>                    (\(x, _) ->
>                     ( union x $
>                       keep (f x) (difference allPairs x)
>                     , x
>                     )
>                    )
>                    (initiallyDistinguished, empty)

> areDistinguishedByOneStep :: (Ord e, Ord n) =>
>                              FSA n e ->
>                              Set (State n, State n) ->
>                              State n ->
>                              State n ->
>                              Bool
> areDistinguishedByOneStep fsa knownDistinct p q
>     | isIn knownDistinct (makePair p q) = True
>     | otherwise = anyS (isIn knownDistinct) newPairs
>     where destinations s x = delta fsa (Symbol x) (singleton s)
>           newPairs' a = collapse (union . pairs' (destinations q a))
>                         empty
>                         (destinations p a)
>           newPairs = collapse (union . newPairs') empty (alphabet fsa)

We only need to check each pair of states once: (1, 2) and (2, 1) are
equivalent in this sense.  Since they are not equivalent in Haskell,
we define a function to ensure that each pair is only built in one
direction.

> makePair :: (Ord a) => a -> a -> (a, a)
> makePair a b = (min a b, max a b)

> pairs :: (Ord a) => Set a -> Set (a, a)
> pairs xs = collapse (union . f) empty xs
>     where f x = Set.mapMonotonic ((,) x) . snd $ Set.split x xs

> pairs' :: (Ord a) => Set a -> a -> Set (a, a)
> pairs' xs x = Set.mapMonotonic (makePair x) xs

An FSA is certainly not minimal if there are states that cannot be
reached by any path from the initial state.  We can trim those.

> -- |The input automaton with unreachable states removed.
> --
> -- @since 1.0
> trimUnreachables :: (Ord e, Ord n) => FSA n e -> FSA n e
> trimUnreachables fsa = FSA alpha trans qi fin (isDeterministic fsa)
>     where alpha  =  alphabet fsa
>           qi     =  initials fsa
>           fin    =  intersection reachables $ finals fsa
>           trans  =  keep (isIn reachables . source) $ transitions fsa
>           reachables = reachables' qi
>           reachables' qs
>               | newqs == qs  =  qs
>               | otherwise    =  reachables' newqs
>               where initialIDs a = Set.mapMonotonic (`ID` [a]) qs
>                     next = collapse
>                            (union . tmap state . step fsa .
>                             initialIDs . Symbol
>                            )
>                            empty
>                            alpha
>                     newqs = next `union` qs

An FSA will often contain states from which no path at all leads to an
accepting state.  These represent failure to match a pattern, which
can be represented equally well by explicit lack of a transition.
Thus we can safely remove them.  Given that we already have a function
to remove states that cannot be reached, the simplest way to remove
these fail-states is to trim the unreachable states in the reversal of
the FSA.

> -- |The reversal of an automaton accepts the reversals of all
> -- strings accepted by the original.
> reverse :: (Ord e, Ord n) => FSA n e -> FSA n e
> reverse f = f { isDeterministic = False
>               , transitions = reverseTransitions f
>               , initials = finals f
>               , finals = initials f
>               }
>     where reverseTransition t = t { source = destination t
>                                   , destination = source t
>                                   }
>           reverseTransitions = tmap reverseTransition . transitions

> trimFailStates :: (Ord e, Ord n) => FSA n e -> FSA n e
> trimFailStates = LTK.FSA.reverse . trimUnreachables . LTK.FSA.reverse

> -- |Returns a normal form of the input.
> -- An FSA is in normal form if it is minimal and deterministic,
> -- and contains neither unreachable states nor nonaccepting sinks.
> -- Node labels are irrelevant, so 'Int' is used as a small
> -- representation.
> normalize :: (Ord e, Ord n) => FSA n e -> FSA Integer e
> normalize = f . trimFailStates . minimize . trimUnreachables
>     where f fsa
>               | isEmpty (states fsa) = complementDeterministic $
>                                        totalWithAlphabet (alphabet fsa)
>               | otherwise            = renameStates fsa


J-Minimization
==============

Note that a state in an FSA is a representation of a (set of)
string(s).  The standard minimization algorithm considers two strings
w and v equivalent iff for all u, wu and vu are the same state or
otherwise equivalent by a recursive application of this definition.

A different equivalence relation exists, though.  Consider a syntactic
monoid M.  Then two elements w and v are J-equivalent iff the
two-sides ideals MwM and MvM are equal.

This is not equivalent to the statement that wM and vM are equivalent
as well as Mw and Mv.  There are stringsets for which two or more
elements are considered distinct when looking at each one-sided ideal
but are actually equivalent in terms of their two-sided ideals.

> -- |Given an automaton whose syntactic monoid is \(M\),
> -- two strings \(u\) and \(v\) are equivalent iff
> -- \(MuM=MvM\)
> jEquivalence :: (Ord e, Ord n) =>
>                 FSA ([Maybe n], [Symbol e]) e ->
>                 Set (Set (State ([Maybe n], [Symbol e])))
> jEquivalence f = partitionBy (primitiveIdeal2 f) (states f)

The primitive left-ideal of an element x of the syntactic monoid is
the set of elements {ax} for all elements a:

> -- |The primitive left ideal.
> --
> -- @since 0.2
> primitiveIdealL :: (Ord n, Ord e) => FSA (n, [Symbol e]) e ->
>                    State (n, [Symbol e]) -> Set (State (n, [Symbol e]))
> primitiveIdealL f x = collapse
>                       (union . follow f (snd $ nodeLabel x))
>                       empty $
>                       states f

> -- |The generalized \(\delta\) function,
> -- follow each symbol in a string in order.
> --
> -- @since 0.2
> follow :: (Ord n, Ord e) => FSA n e ->
>           [Symbol e] -> State n -> Set (State n)
> follow f xs q = collapse (flip (.) . delta f) id xs $ singleton q

The primitive right-ideal is {xa} for all a,
i.e. the reachability relation.
We already have a function that computes this: @epsilonClosure@.
In order to make use of that, we just replace every edge by Epsilon.
Ideally we would use an uninhabited type for the alphabet,
but since Haskell does not have such a type out of the box,
we use the unit type @()@ instead.

> ignoreSymbols :: (Ord n, Ord e) => FSA n e -> FSA n ()
> ignoreSymbols f = f { sigma = empty
>                     , transitions = Set.map x (transitions f)
>                     , isDeterministic = False
>                     }
>     where x t = t {edgeLabel = Epsilon}

> -- |The primitive right ideal.
> --
> -- @since 0.2
> primitiveIdealR :: (Ord n, Ord e) => FSA n e -> State n -> Set (State n)
> primitiveIdealR f x = epsilonClosure (ignoreSymbols f) $ singleton x

Then the two-sided ideal is {axb} for all a and b,
i.e. the right-ideals of every left-ideal (or v.v.).

> -- |The primitive two-sided ideal.
> --
> -- @since 0.2
> primitiveIdeal2 :: (Ord n, Ord e) => FSA (n, [Symbol e]) e ->
>                    State (n, [Symbol e]) -> Set (State (n, [Symbol e]))
> primitiveIdeal2 f = collapse (union . primitiveIdealR f) empty .
>                     primitiveIdealL f

> -- |An automaton is considered trivial under some equivalence relation
> -- if each of its equivalence classes is singleton.
> --
> -- @since 0.2
> trivialUnder :: (FSA n e -> Set (Set (State n))) -> FSA n e -> Bool
> trivialUnder f = all ((== 1) . isize) . f


H-Minimization
==============

Where two strings are J-equivalent iff their two-sided ideals are equal,
they are H-equivalent if their corresponding one-sided ideals are equal.
That is, w is equivalent to v iff wM == vM and Mw == Mv.

> -- |Given an automaton whose syntactic monoid is \(M\),
> -- two strings \(u\) and \(v\) are equivalent if
> -- \(Mu=Mv\) and \(uM=vM\).
> --
> -- @since 0.2
> hEquivalence :: (Ord n, Ord e) =>
>                 FSA (n, [Symbol e]) e -> Set (Set (State (n, [Symbol e])))
> hEquivalence f = refinePartitionBy (primitiveIdealR f) .
>                  partitionBy (primitiveIdealL f) $ states f


Determinization
================

Converting a non-deterministic FSA to a deterministic one (DFA) can
improve the speed of determining whether the language represented by
the FSA contains a string.  Further, both complexity-classification
and minimization require DFAs as input.

> metaFlip :: Ord n => Set (State n) -> State (Set n)
> metaFlip = State . Set.mapMonotonic nodeLabel

> powersetConstruction :: (Ord e, Ord n) =>
>                         FSA n e ->
>                         Set (State n) ->
>                         (Set (State n) -> Bool) ->
>                         FSA (Set n) e
> powersetConstruction f start isFinal = FSA (alphabet f) trans qi fin True
>     where qi = singleton (metaFlip start)
>           buildTransition a q = (a, q, delta f (Symbol a) q)
>           buildTransitions' q
>               = Set.mapMonotonic (`buildTransition` q) $ alphabet f
>           buildTransitions = collapse (union . buildTransitions') empty
>           (trans',qs,_)
>               = until
>                 (\(_, b, c) -> isize b == isize c)
>                 (\(a, b, c) ->
>                  let d = buildTransitions (difference c b)
>                  in ( a `union` d
>                     , c
>                     , union c $ tmap (\(_, _, z) -> z) d
>                     )
>                 )
>                 (empty, empty, singleton start)
>           makeRealTransition (a, b, c)
>               = Transition
>                 { edgeLabel = Symbol a
>                 , source = metaFlip b
>                 , destination = metaFlip c
>                 }
>           trans = Set.mapMonotonic makeRealTransition trans'
>           fin = Set.mapMonotonic metaFlip $ keep isFinal qs

> -- |Returns a deterministic automaton representing the same
> -- stringset as the potentially nondeterministic input.
> determinize :: (Ord e, Ord n) => FSA n e -> FSA (Set n) e
> determinize f
>     | isDeterministic f = renameStatesByMonotonic singleton f
>     | otherwise = powersetConstruction f (initials f) isFinal
>     where isFinal = anyS (isIn (finals f)) . epsilonClosure f


The Powerset Graph
==================

When determinizing an FSA, we use a powerset construction building out
from the set of initial states.  We can use the same construction but
begin instead with the set of all states to obtain a different
powerset graph.  Though there are many possible initial conditions,
including the one used for determinization, we call this particular
instance *the* powerset graph.  If our source FSA happens to be
normalized, we can gather a lot of information from this graph.

We will tag any states not disjoint from the set of final states in
the source as accepting.

> -- |Given an automaton \(M\) with stateset \(Q\),
> -- the powerset graph of \(M\) is an automaton with
> -- stateset in the powerset of \(Q\).
> -- From a node \(\{q_1,q_2,\ldots,q_n\}\),
> -- there is an edge labelled \(\sigma\) that leads to
> -- \(\{\delta(q_1,\sigma), \delta(q_2,\sigma), \ldots, \delta(q_n, \sigma)\}\),
> -- where \(\delta\) is the transition function of the input.
> -- The initial state is \(Q\), and the result is complete.
> powersetGraph :: (Ord e, Ord n) => FSA n e -> FSA (Set n) e
> powersetGraph f = powersetConstruction f (states f) hasAccept
>     where hasAccept qs = intersection (finals f) qs /= empty


The Syntactic Monoid
====================

In the powerset graph (PSG), states are labelled by sets of states.
For all states Q and symbols x, there is an edge labelled by x from Q
to the state labelled by Q' such that for all q' in Q', there exists
some q in Q such that q goes to q' on x.  The syntactic monoid differs
in that the states are effectively labelled by functions.  Here we
will use lists of the form [q_0, q_1, ..., q_n].

The syntactic monoid a DFA whose states are labelled [0, 1, ..., n]
will always contain the state [0, 1, ..., n].  This is the initial
state.  There exist edges between states are found by mapping over the
list.  That is, if delta is the transition function from QxSigma->Q:

    delta' [q_0, ..., q_n] x = [delta q_0 x, ..., delta q_n x]

Any state labelled by a function mapping an initial state to a final
state is considered accepting in the syntactic monoid.

> -- |Given an automaton \(M\) with stateset \(Q\),
> -- the syntactic monoid of \(M\) is an automaton with
> -- stateset in \((Q\rightarrow Q)\).
> -- Here these functions are represented by lists,
> -- where \(q_i\) maps to the \(i^\text{th}\) element of the list.
> -- From a node \(\langle q_1,q_2,\ldots,q_n\rangle\),
> -- there is an edge labelled \(\sigma\) that leads to
> -- \(\langle\delta(q_1,\sigma), \delta(q_2,\sigma), \ldots, \delta(q_n, \sigma)\rangle\),
> -- where \(\delta\) is the transition function of the input.
> -- The initial state is the identity function, and the result is complete.
> syntacticMonoid :: (Ord e, Ord n) =>
>                    FSA n e -> FSA ([Maybe n], [Symbol e]) e
> syntacticMonoid m = FSA { sigma = alphabet m
>                         , transitions = t
>                         , initials = i
>                         , finals = f
>                         , isDeterministic = True
>                         }
>     where i   =  singleton . fmap (flip (,) []) . mapM (fmap Just) $ s
>           s   =  Set.toList (initials m) ++
>                  Set.toList (difference (states m) $ initials m)
>           n   =  size (initials m)
>           i'  =  if intersection (finals m) (initials m) /= empty
>                  then i
>                  else empty
>           (t,_,f,_)
>               = syntacticMonoid' m n (empty, i, i', i)

> syntacticMonoid' :: (Ord e, Ord n) => FSA n e -> Int ->
>                     ( Set (Transition ([Maybe n], [Symbol e]) e)
>                     , Set (State ([Maybe n], [Symbol e]))
>                     , Set (State ([Maybe n], [Symbol e]))
>                     , Set (State ([Maybe n], [Symbol e]))
>                     ) ->
>                     ( Set (Transition ([Maybe n], [Symbol e]) e)
>                     , Set (State ([Maybe n], [Symbol e]))
>                     , Set (State ([Maybe n], [Symbol e]))
>                     , Set (State ([Maybe n], [Symbol e]))
>                     )
> syntacticMonoid' f n former@(ot, os, ofi, s)
>     | isEmpty s  =  former
>     | otherwise  =  syntacticMonoid' f n next
>     where next      =  ( nt `union` ot
>                        , ns `union` os
>                        , nf `union` ofi
>                        , ns
>                        )
>           alpha     =  alphabet f
>           move a q  =  replaceDestinationFromMap (s `union` os) $
>                        Transition
>                        { edgeLabel = Symbol a
>                        , source = q
>                        , destination = move' (Symbol a) q
>                        }
>           move' a
>               = fmap
>                 (bimap
>                  (tmap (maybe Nothing
>                         $ pull . delta f a . singleton . State))
>                  (++ [a]))
>           pull xs   =  if xs == empty
>                        then Nothing
>                        else nodeLabel $ fmap Just (chooseOne xs)
>           nt        =  mergeByDestFst $
>                        collapse (union . nt') empty alpha
>           nt' a     =  tmap (move a) s
>           ns        =  keep (isNotIn os' . fmap fst)
>                        $ tmap destination nt
>           nf        =  keep hasFinal ns
>           os'       =  tmap (fmap fst) os
>           fins      =  nodeLabel . mapM (fmap Just)
>                        . Set.toList $ finals f
>           hasFinal  =  not . isEmpty . intersection fins
>                        . take n . fst . nodeLabel

> replaceDestinationFromMap ::
>     (Container (c (State (a, b))) (State (a, b)), Collapsible c, Eq a) =>
>     c (State (a, b)) -> Transition (a, b) e -> Transition (a, b) e
> replaceDestinationFromMap m t
>     | isEmpty m' =  t
>     | otherwise  =  t {destination = chooseOne m'}
>     where m'  =  keep ((==) (fn $ destination t) . fn) m
>           fn  =  fst . nodeLabel

> mergeByDestFst ::
>     ( Container (c (Transition (n, n') e)) (Transition (n, n') e)
>     , Collapsible c, Ord n, Ord n', Ord e
>     ) => c (Transition (n, n') e) -> c (Transition (n, n') e)
> mergeByDestFst = mergeByDestFst' empty

> mergeByDestFst' ::
>     ( Container (c (Transition (n, n') e)) (Transition (n, n') e)
>     , Collapsible c, Ord n, Ord n', Ord e
>     ) =>
>     c (Transition (n, n') e) -> c (Transition (n, n') e) ->
>     c (Transition (n, n') e)
> mergeByDestFst' p l
>     | isEmpty l = p
>     | otherwise
>           = mergeByDestFst'
>             (union p   .
>              insert x  $
>              tmap (set_dest (destination x)) sds
>             ) $ difference xs sds
>     where (x, xs)       =  choose l
>           fnd           =  fst . nodeLabel . destination
>           sds           =  keep ((==) (fnd x) . fnd) xs
>           set_dest d t  =  t {destination = d}


Alphabet Manipulation
=====================

> -- |Add missing symbols to the alphabet of an automaton.
> -- The result is an automaton with at least the provided alphabet
> -- that licenses exactly the same set of strings as the input.
> extendAlphabetTo :: (Ord a, Ord b) => Set b -> FSA a b ->
>                     FSA (Maybe Integer, Maybe a) b
> extendAlphabetTo syms = autUnion $ emptyWithAlphabet syms

A "semantic automaton" is one in which a constraint is realized for
a universal alphabet.  This is achieved by using edges labelled by
'Nothing' to represent symbols not already included in the alphabet
and an extend function that takes these edges into account.

For example, consider the local and piecewise constraints:
* No A immediately follows another A, and
* No A follows another A.
As automata with alphabet {A} these constraints appear identical,
each licensing only the empty string and "A" itself.  But if the
alphabet were instead {A,B}, then they would instead license:
* B*A?(BA?)*, and
* B*A?B*, respectively.
Since the source automata for these constraints are identical,
no algorithm can know which variant to extend the alphabet to.
Encoding the universal alphabet in the transition graph with
semantic automata can prevent this issue by explicitly stating
which alternative is correct.

One caveat with the use of semantic automata is that before any
operation combines two or more automata, the inputs must have their
alphabets unified.

> -- |Add missing symbols to the alphabet of an automaton.
> -- As the symbol 'Nothing' is taken to represent
> -- any symbol not currently in the alphabet,
> -- new edges are added in parallel to existing edges labelled by 'Nothing'.
> semanticallyExtendAlphabetTo ::
>     (Ord a, Ord b) => Set b -> FSA a (Maybe b) -> FSA a (Maybe b)
> semanticallyExtendAlphabetTo syms fsa
>     = fsa { sigma       = as `union` new
>           , transitions = ts `union` ts'
>           }
>     where as   =  alphabet fsa
>           new  =  difference (Set.mapMonotonic Just syms) as
>           ts   =  transitions fsa
>           f e  =  union (Set.mapMonotonic
>                          (\x -> e {edgeLabel = Symbol x}) new)
>           ts'  =  collapse f empty $
>                   extractMonotonic edgeLabel (Symbol Nothing) ts

> -- |Remove the semantic 'Nothing' edges from an automaton and reflect this
> -- change in the type.
> desemantify :: (Ord a, Ord b) => FSA a (Maybe b) -> FSA a b
> desemantify fsa = renameSymbolsByMonotonic (fromMaybe undefined)
>                   $ contractAlphabetTo
>                     (Set.delete Nothing (alphabet fsa))
>                     fsa

> -- |Add self-loops on all symbols to all edges to compute
> -- an upward closure.
> loopify :: (Ord a, Ord b) => FSA a b -> FSA a b
> loopify fsa = fsa { transitions = Set.union (transitions fsa) trs
>                   , isDeterministic = False
>                   }
>     where as = Set.toList $ alphabet fsa
>           qs = Set.toList $ states fsa
>           trs = Set.fromList $ concatMap sigmatr as
>           sigmatr x = map (\q -> Transition
>                                  { edgeLabel = Symbol x
>                                  ,  source = q
>                                  , destination = q
>                                  }) qs

Tierify:
* Ensure that all of T is accounted for in the input
* Remove symbols from the input that are not in T
* Insert self-loops on all symbols not in T, including:
  * the other symbols from the input's alphabet
  * the Nothing placeholder

> -- |Convert a semantic automaton that represents a Local constraint
> -- into a new one that represents the same constraint in the associated
> -- Tier-Local class.
> tierify :: (Ord a, Ord b) => Set b -> FSA a (Maybe b) -> FSA a (Maybe b)
> tierify t fsa = semanticallyExtendAlphabetTo as f''
>     where f'   =  contractAlphabetTo (tmap Just t) $
>                   semanticallyExtendAlphabetTo t fsa
>           f''  =  f'
>                   { sigma       = insert Nothing $ alphabet f'
>                   , transitions = union (transitions f') .
>                                   Set.mapMonotonic l $ states f'
>                   }
>           l q  =  Transition
>                   { edgeLabel    =  Symbol Nothing
>                   , source       =  q
>                   , destination  =  q
>                   }
>           as   =  collapse (maybe id insert) empty $ alphabet fsa

> -- |Allow a given set of symbols to be freely inserted or deleted.
> -- In other words, make those symbols neutral.
> neutralize :: (Ord a, Ord b) => Set b -> FSA a b -> FSA a b
> neutralize t fsa = fsa
>                    { sigma = Set.union t $ alphabet fsa
>                    , transitions = transitions fsa
>                                    `union` loops
>                                    `union` omissions
>                    , isDeterministic = False
>                    }
>     where tsym      =  map Symbol $ Set.toList t
>           x p       =  p { edgeLabel = Epsilon }
>           c s       =  Set.mapMonotonic (m s) (states fsa)
>           m s q     =  Transition
>                        { edgeLabel    =  s
>                        , source       =  q
>                        , destination  =  q
>                        }
>           loops     =  unionAll $ map c tsym
>           omissions =  tmap x . keep (isIn tsym . edgeLabel)
>                        $ transitions fsa

> -- |Remove symbols from the alphabet of an automaton.
> contractAlphabetTo :: (Ord a, Ord b) => Set b -> FSA a b -> FSA a b
> contractAlphabetTo syms fsa = trimUnreachables $
>                               fsa
>                               { sigma       = syms
>                               , transitions = trans
>                               }
>     where trans = keep
>                   (isIn
>                    (insert Epsilon $ Set.mapMonotonic Symbol syms) .
>                    edgeLabel
>                   ) $ transitions fsa

> -- |Ignore the alphabet of an automaton and use a given alphabet instead.
> forceAlphabetTo :: (Ord a, Ord b) =>
>                    Set b -> FSA a b -> FSA (Maybe Integer, Maybe a) b
> forceAlphabetTo syms = contractAlphabetTo syms . extendAlphabetTo syms


Miscellaneous Functions
=======================

After several operations, the nodeLabel type of an FSA becomes a deep
mixture of pairs, maybes, and sets.  We can smash these into a smaller
type to improve memory usage and processing speed.

> -- |Equivalent to 'renameStatesBy' \(f\),
> -- where \(f\) is an arbitrary injective function.
> renameStates :: (Ord e, Ord n, Ord n1, Enum n1) => FSA n e -> FSA n1 e
> renameStates fsa = renameStatesByMonotonic
>                    (flip (Map.findWithDefault (toEnum 0)) m)
>                    fsa
>     where m = Map.fromDistinctAscList . flip zip (enumFrom $ toEnum 1) .
>               map nodeLabel . Set.toAscList $ states fsa
> {-# INLINE[1] renameStates #-}
> {-# RULES
>   "renameStates/identity" renameStates = id
>   #-}

> -- |Transform the node labels of an automaton using a given function.
> -- If this function is not injective, the resulting FSA may not be
> -- deterministic even if the original was.
> renameStatesBy :: (Ord e, Ord n, Ord n1) =>
>                   (n -> n1) -> FSA n e -> FSA n1 e
> renameStatesBy f a
>     = a { transitions      =  tmap (transition . fmap f . Noitisnart)
>                               (transitions a)
>         , initials         =  tmap (fmap f) (initials a)
>         , finals           =  tmap (fmap f) (finals a)
>         , isDeterministic  =  isDeterministic a &&
>                               isize ns == isize (states a)
>         }
>     where ns = tmap (fmap f) (states a)

> -- |Transform the node labels of an automaton using a given function.
> -- The precondition (that for all states x < y, f x < f y) is not checked.
> renameStatesByMonotonic :: (Ord e, Ord n, Ord n1) =>
>                            (n -> n1) -> FSA n e -> FSA n1 e
> renameStatesByMonotonic f a
>     = a { transitions  =  Set.mapMonotonic
>                           (transition . fmap f . Noitisnart) $
>                           transitions a
>         , initials     =  Set.mapMonotonic (fmap f) $ initials a
>         , finals       =  Set.mapMonotonic (fmap f) $ finals a
>         }

> -- |Transform the edge labels of an automaton using a given function.
> -- If this function is not injective, the resulting FSA may not be
> -- deterministic even if the original was.
> renameSymbolsBy :: (Ord e, Ord e1, Ord n) =>
>                    (e -> e1) -> FSA n e -> FSA n e1
> renameSymbolsBy f a = a { sigma            =  alpha
>                         , transitions      =  tmap (fmap f) $ transitions a
>                         , isDeterministic  =  isDeterministic a && samea
>                         }
>     where alpha  =  tmap f (alphabet a)
>           samea  =  isize alpha == isize (alphabet a)

> -- |Transform the edge labels of an automaton using a given function.
> -- The precondition (that for all symbols x < y, f x < f y) is not checked.
> renameSymbolsByMonotonic :: (Ord e, Ord e1, Ord n) =>
>                             (e -> e1) -> FSA n e -> FSA n e1
> renameSymbolsByMonotonic f a
>     = a { sigma        =  alpha
>         , transitions  =  Set.mapMonotonic (fmap f) (transitions a)
>         }
>     where alpha  =  Set.mapMonotonic f (alphabet a)

Mapping on tuples:

> bimap :: (a -> c) -> (b -> d) -> (a, b) -> (c, d)
> bimap f g (a, b) = (f a, g b)

A parallel fold implementation based on a tree.  The accumulating
function must be both associative and commutative, as the tree is
built in such a way that order of elements is not preserved.

> data Tree a = Leaf a | Tree (Tree a) (Tree a)
>               deriving (Eq, Ord, Read, Show)

> treeFromList :: [a] -> Tree a
> treeFromList []   =  error "No elements"
> treeFromList [x]  =  Leaf x
> treeFromList xs   =  ls' `par` rs' `pseq` Tree ls' rs'
>     where (ls, rs)    =  evenOdds xs
>           (ls', rs')  =  (treeFromList ls, treeFromList rs)

> instance NFData a => NFData (Tree a)
>     where rnf (Leaf a)    =  rnf a
>           rnf (Tree l r)  =  rnf l `seq` rnf r

> treeFold :: (a -> a -> a) -> Tree a -> a
> treeFold _ (Leaf x) = x
> treeFold op (Tree l r) = l' `par` r' `pseq` (l' `op` r')
>     where l'  =  treeFold op l
>           r'  =  treeFold op r

Split a linked list into two smaller lists by taking the even and odd
elements.  This does not require computing the list's length, thus it
can be more efficient than splitting at the middle element.

The implementation of evenOdds given here will even work on an
infinite stream because it guarantees that elements are output
as soon as they are obtained.

> evenOdds :: [a] -> ([a],[a])
> evenOdds []        =  ([], [])
> evenOdds [a]       =  ([a], [])
> evenOdds (a:b:xs)  =  let (e, o) = evenOdds xs in (a:e, b:o)
