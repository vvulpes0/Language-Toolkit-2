> {-# OPTIONS_HADDOCK show-extensions #-}
> {-# Language
>   FlexibleContexts,
>   FlexibleInstances,
>   MultiParamTypeClasses,
>   Trustworthy
>   #-}
> {-|
> Module    : FSA
> Copyright : (c) 2014-2018 Dakotah Lambert
> License   : BSD-style, see LICENSE

> The purpose of this module is to define an interface to a generic,
> reusable impementation of finite-state automata (FSAs).  The primary
> motivation for this is to allow for efficient analysis of stringsets
> in a linguistic context, although the nature of the project should 
> allow more general use.
> -}
> module FSA ( FSA(..)
>            , states
>            , isNull
>            -- * Constructing simple automata
>            , totalWithAlphabet
>            , emptyWithAlphabet
>            , emptyLanguage
>            , singletonWithAlphabet
>            , singletonLanguage
>            -- * Derived automata
>            , powersetGraph
>            , syntacticMonoid
>            , residue
>            , coresidue
>            -- * Transformations
>            , flatIntersection
>            , flatUnion
>            , FSA.reverse
>            , complement
>            , complementDeterministic
>            , determinize
>            -- ** Minimization
>            , minimize
>            , minimizeDeterministic
>            , normalize
>            -- *** Equivalence Classes
>            , minimizeOver
>            , nerode
>            , jEquivalence
>            -- ** Alphabetic Transformations
>            , extendAlphabetTo
>            , contractAlphabetTo
>            , forceAlphabetTo
>            , renameSymbolsBy
>            -- ** Transformations of 'State' labels
>            , renameStatesBy
>            , renameStates
>            -- * Miscellaneous
>            , State(..)
>            , Symbol(..)
>            , unsymbols
>            , Transition(..)
>            , module Containers
>            ) where

> import Data.Set (Set)
> import qualified Data.Set as Set
> import Containers
> import Control.DeepSeq (NFData, rnf)
> import Control.Parallel (par, pseq)

> import Control.Applicative (Applicative(..))
> import Data.Semigroup (Semigroup(..))
> import Data.Monoid (Monoid(..))


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
> data FSA n e = FSA { alphabet         ::  Set e
>                    , transitions      ::  Set (Transition n e)
>                    , initials         ::  Set (State n)
>                    , finals           ::  Set (State n)
>                    , isDeterministic  ::  Bool
>                    }
>     deriving (Show, Read)

> -- |The collection of all states in an FSA.
> states :: (Ord e, Ord n) => FSA n e -> Set (State n)
> states f = unionAll [initials f, finals f, others]
>    where others           = unionAll $ tmap extractStates ts
>          extractStates t  = doubleton (source t) (destination t)
>          doubleton a b    = insert b (singleton a)
>          ts               = transitions f

> -- |An automaton accepting every string over a given alphabet.
> totalWithAlphabet :: (Ord e, Enum n, Ord n) => Set e -> FSA n e
> totalWithAlphabet as = FSA as trans (singleton q) (singleton q) True
>     where trans  = tmap (flip (flip Transition q) q . Symbol) as
>           q      = State $ toEnum 0

> -- |An automaton accepting no strings over a given alphabet.
> emptyWithAlphabet :: (Ord e, Enum n, Ord n) => Set e -> FSA n e
> emptyWithAlphabet as = FSA as trans (singleton q) empty True
>     where trans  = tmap (flip (flip Transition q) q . Symbol) as
>           q      = State $ toEnum 0

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
> singletonWithAlphabet as str = FSA as (trans str) begins finals True
>     where trans xs = union (trans' xs (toEnum 1)) failTransitions
>           trans' [] n = tmap (\a -> Transition (Symbol a) (State n) fail) as
>           trans' (x:xs) n = let m = succ n in
>                             (union (trans' xs m) $
>                              tmap (\y -> Transition (Symbol y) (State n)
>                                          $ (if (x == y)
>                                             then State m
>                                             else fail))
>                              as)
>           fail = State $ toEnum 0
>           failTransitions = tmap (\a -> Transition (Symbol a) fail fail) as
>           begins = singleton (State $ toEnum 1)
>           last = (+ 1) . fromIntegral . length $ str
>           finals = singleton (State $ toEnum last)

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
> data Symbol e = Epsilon  -- ^The edge may be taken without consuming any input.
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
> unsymbols :: (Collapsible s, Eq (s e), Container (s e) e, Monoid (s e)) =>
>              s (Symbol e) -> s e
> unsymbols = mconcat . collapse (insert . f) empty
>     where f (Symbol x) = singleton x
>           f _          = empty

States
------

> -- |A vertex of the graph representation of an 'FSA' is a 'State',
> -- which can be labelled with any arbitrary value, so long as every
> -- vertex of a single automaton is labelled with a distinct value
> -- of the same type.
> data State n = State {nodeLabel :: n} deriving (Eq, Ord, Read, Show)

Transitions
-----------

If a state is the vertex of a graph, then a transition is its edge.
Since an FSA is represented by a directed graph, there are three
components to a transition: an edge label, and two states.  If a
computation in the first state encounters a symbol matching the
transition's edge label, then it moves to the second state.

> -- |The edges of an 'FSA'.
> data Transition n e = Transition { edgeLabel   :: (Symbol e)
>                                  , source      :: (State n)
>                                  , destination ::(State n)
>                                  }
>                     deriving (Eq, Ord, Show, Read)


Class Instances
===============

Here we define class instances for FSAs and their component types.


Symbol
------

> instance Functor Symbol where
>     fmap _ Epsilon     =  Epsilon
>     fmap f (Symbol e)  =  Symbol (f e)

> instance (NFData e) => NFData (Symbol e) where
>     rnf Epsilon = ()
>     rnf (Symbol e) = rnf e


State
-----

> instance Functor State where
>     fmap f = State . f . nodeLabel

> instance Applicative State where
>     pure   =  State
>     (<*>)  =  fmap . nodeLabel

> instance Monad State where
>     return   =  pure
>     a >>= f  =  f $ nodeLabel a

> instance (Semigroup n) => Semigroup (State n) where
>     (<>) = fmap . nodeLabel . fmap (<>)

> instance (Monoid n) => Monoid (State n) where
>     mempty   =  State mempty
>     mappend  =  (<>)

> instance (NFData n) => NFData (State n) where
>     rnf (State n) = rnf n


Transition
----------

> instance (NFData n, NFData e) => NFData (Transition n e) where
>     rnf t = rnf (edgeLabel t) `seq`
>             rnf (source t)    `seq`
>             rnf (destination t)

> newtype Noitisnart e n = Noitisnart { transition :: Transition n e }

> instance Functor (Transition n) where
>     fmap f t = t { edgeLabel = fmap f (edgeLabel t) }

> instance Functor (Noitisnart e) where
>     fmap f = Noitisnart . fmap' . transition
>         where fmap' t = t { source       =  fmap f (source t)
>                           , destination  =  fmap f (destination t)
>                           }


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

> instance (Ord e, Ord n) => Eq (FSA n e) where
>     a == b = isomorphic (normalize a) (normalize b)

Calls to `isomorphic` should work for NFAs as well as DFAs, but in the
current implementation, in general, will not.  This is because
multiple start states are combined with the cartesian product to
create c, rather than mapped from a to their counterparts in b, a much
harder problem.

> isomorphic :: (Ord e, Ord n1, Ord n2) => FSA n1 e -> FSA n2 e -> Bool
> isomorphic a b = (alphabet a        == alphabet b)         &&
>                  (size (initials a) == size (initials b))  &&
>                  (size (finals a)   == size (finals b))    &&
>                  (size (states a)   == size (states b))    &&
>                  (size (initials a) == size (initials c))  &&
>                  (size (finals a)   == size (finals c))    &&
>                  (size (states a)   == s)
>     where c  = autUnion a b
>           s  = size . keep ((/=) (State (Nothing, Nothing))) $ states c

> instance (Enum n, Ord n, Ord e) => Container (FSA n e) [e] where
>     isEmpty              =  isNull
>     isIn                 =  accepts
>     union                =  apply autUnion
>     intersection         =  apply autIntersection
>     difference           =  apply autDifference
>     symmetricDifference  =  apply autSymmetricDifference
>     empty                =  emptyLanguage
>     singleton            =  singletonLanguage

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
> flatUnion [] = emptyLanguage
> flatUnion xs = pfold u xs
>     where u a b = let x = renameStates . minimize $ autUnion a b
>                   in rnf x `seq` x

> instance (NFData n, NFData e) => NFData (FSA n e) where
>     rnf (FSA a t i f d) = rnf a `seq` rnf t `seq` rnf i `seq`
>                           rnf f `seq` rnf d


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

> epsilonClosure :: (Ord e, Ord n) => FSA n e -> State n -> Set (State n)
> epsilonClosure fsa q
>     | isDeterministic fsa  = singleton q
>     | otherwise            = epsilonClosure' fsa (singleton q)
>     where epsilons = keep ((== Epsilon) . edgeLabel) (transitions fsa)
>           epsilonClosure' fsa seen
>               | numNew == 0  = seen
>               | otherwise    = epsilonClosure' fsa closure
>               where seens = keep ((isIn seen) . source) epsilons
>                     closure = union seen $ tmap destination seens
>                     numNew = size closure - size seen

> step :: (Ord e, Ord n) => FSA n e -> Set (ID n e) -> Set (ID n e)
> step fsa ids
>     | filteredIDs == empty  = empty
>     | otherwise             = unionAll $ tmap next filteredIDs
>     where ts = transitions fsa
>           filterID id = ID (state id) (keep (/= Epsilon) (string id))
>           filteredIDs = tmap filterID ids
>           next i
>               | null s     = tmap (flip ID []) closure
>               | otherwise  = tmap (flip ID (tail s)) outStates
>               where s = string i
>                     closure = epsilonClosure fsa (state i)
>                     sameSource = keep ((isIn closure) . source) ts
>                     sameLabel   = keep ((== head s) . edgeLabel) sameSource
>                     outStates  = (unionAll $
>                                   tmap
>                                   (epsilonClosure fsa . destination)
>                                   sameLabel)

We should not have to produce IDs ourselves.  We can define the transition
function `delta` from an FSA, a symbol, and a state to a set of states:

> delta :: (Ord e, Ord n) =>
>          FSA n e -> Symbol e -> Set (State n) -> Set (State n)
> delta f x = tmap state . step f . tmap ((flip ID) [x])

> compute :: (Ord e, Ord n) => FSA n e -> [Symbol e] -> Set (ID n e)
> compute fsa str = until (allS (null . string)) (step fsa) initialIDs
>     where initialIDs = tmap (flip ID str) (initials fsa)

> accepts :: (Ord e, Ord n) => FSA n e -> [e] -> Bool
> accepts fsa = anyS (isIn (finals fsa)) . tmap state .
>               compute fsa . tmap Symbol


Logical Operators
=================

> combine :: State a -> State b -> State (a, b)
> combine (State a) (State b) = State (a, b)

> makePairs :: (Ord a, Ord b) => Set a -> Set b -> Set (a, b)
> makePairs xs ys = unionAll $ tmap (\x -> tmap ((,) x) ys) xs

> makeJustPairs :: (Ord a, Ord b) =>
>                  Set (State a) -> Set (State b) ->
>                  Set (State (Maybe a), State (Maybe b))
> makeJustPairs xs ys = makePairs (justify xs) (justify ys)
>     where justify :: Ord c => Set (State c) -> Set (State (Maybe c))
>           justify = tmap (\(State z) -> State (Just z))

> combineAlphabets :: Ord e => FSA n e -> FSA n1 e -> Set e
> combineAlphabets f1 f2 = union (alphabet f1) (alphabet f2)

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

> combineTransitions :: (Ord e, Ord n, Ord n1) => FSA n e -> FSA n1 e ->
>                       Set (Transition (Maybe n, Maybe n1) e)
> combineTransitions f1 f2 = trans
>     where bigalpha = combineAlphabets f1 f2
>           mDestinations x f q
>               | extensions == empty  = singleton (State Nothing)
>               | otherwise            = tmap
>                                        (State . Just . nodeLabel)
>                                        extensions
>               where extensions = delta f x (singleton q)
>           nexts x f = maybe
>                       (singleton (State Nothing))
>                       (mDestinations x f . State) .
>                       nodeLabel
>           nextPairs x qp = unionAll $
>                            tmap (\a -> tmap (stateFromPair . (,) a) n2) n1
>               where n1 = nexts x f1 $ fmap fst qp
>                     n2 = nexts x f2 $ fmap snd qp
>           stateFromPair (q1, q2) = (,) <$> q1 <*> q2
>           extensionsOnSymbol qp x = tmap (Transition x qp) $
>                                     nextPairs x qp
>           extensions qp = unionAll $ tmap (extensionsOnSymbol qp) $
>                           tmap Symbol bigalpha
>           initialset = tmap stateFromPair $
>                        makeJustPairs (initials f1) (initials f2)
>           (_, _, trans) = until
>                           (\(new, _, _) -> new == empty)
>                           (\(new, prev, partial) ->
>                            let exts   = unionAll $ tmap extensions new
>                                seen   = union new prev
>                                dests  = tmap destination exts
>                            in (difference dests seen,
>                                seen,
>                                union exts partial))
>                           (initialset, empty, empty)

> autIntersection :: (Ord e, Ord n1, Ord n2) => FSA n1 e -> FSA n2 e ->
>                    FSA (Maybe n1, Maybe n2) e
> autIntersection f1 f2 = FSA bigalpha trans init fin det
>     where bigalpha = combineAlphabets f1 f2
>           cs = tmap (\(x, y) -> combine x y)
>           init = cs $ makeJustPairs (initials f1) (initials f2)
>           fin  = (intersection sts
>                   (cs (makeJustPairs (finals f1) (finals f2))))
>           trans = combineTransitions f1 f2
>           sts = union (tmap source trans) (tmap destination trans)
>           det = isDeterministic f1 && isDeterministic f2

> autUnion :: (Ord e, Ord n1, Ord n2) => FSA n1 e -> FSA n2 e ->
>             FSA (Maybe n1, Maybe n2) e
> autUnion f1 f2 = FSA bigalpha trans init fin det
>     where bigalpha = combineAlphabets f1 f2
>           cs = tmap (\(x, y) -> combine x y)
>           init = cs $ makeJustPairs (initials f1) (initials f2)
>           fin1 = finals f1
>           fin2 = finals f2
>           fin1With2 = makeJustPairs fin1 (states f2)
>           fin2With1 = makeJustPairs (states f1) fin2
>           fin1WithN = tmap (flip (,) (State Nothing) . fmap Just) fin1
>           fin2WithN = tmap ((,) (State Nothing) . fmap Just) fin2
>           fin = (intersection sts
>                  (cs
>                   (unionAll [fin1WithN, fin2WithN, fin1With2, fin2With1])))
>           trans = combineTransitions f1 f2
>           sts = union (tmap source trans) (tmap destination trans)
>           det = isDeterministic f1 && isDeterministic f2

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
>     = autDifference (autUnion f1 f2) (autIntersection f1 f2)

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
> coresidue a b = renameStates . minimize $
>                 union (renameStates $ complement a) b


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
> minimizeDeterministic = minimizeOver nerode

> -- |Returns a deterministic 'FSA' minimized over a given relation.
> -- The precondition that the input is deterministic
> -- is not checked.
> minimizeOver :: (Ord e, Ord n) =>
>                 (FSA n e -> Set (Set (State n))) -> FSA n e -> FSA (Set n) e
> minimizeOver r fsa = trimUnreachables newfsa
>     where classes = r fsa
>           classOf x = (State . tmap nodeLabel . unionAll)
>                       (keep (contains x) classes)
>           init = tmap classOf (initials fsa)
>           fin = tmap classOf (finals fsa)
>           trans = (tmap
>                    (\(Transition a p q) ->
>                     Transition a (classOf p) (classOf q))
>                    (transitions fsa))
>           newfsa = FSA (alphabet fsa) trans init fin True

> -- |Two strings \(u\) and \(v\) are equivalent iff
> -- for all strings \(w\), \(uw\) and \(vw\) lead to
> -- states in the same equivalence class.
> nerode :: (Ord e, Ord n) => FSA n e -> Set (Set (State n))
> nerode fsa = tmap eqClass sts
>     where sts = states fsa
>           i = union i' $ tmap (\x -> (x, x)) sts
>           i' = difference (pairs sts) $ distinguishedPairs fsa
>           eqClass x = (unionAll
>                        [singleton x,
>                         (tmap snd . keep ((== x) . fst)) i,
>                         (tmap fst . keep ((== x) . snd)) i])

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
>           initiallyDistinguished = unionAll $
>                                    tmap (pairs' (finals fsa))
>                                    (difference (states fsa) $ finals fsa)
>           f d (a, b) = areDistinguishedByOneStep fsa d a b
>           result = (until
>                     (\(x, y) -> size x == size y)
>                     (\(x, _) -> (union x $
>                                  keep (f x) (difference allPairs x),
>                                  x))
>                     (initiallyDistinguished, empty))

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
>           newPairs' a = unionAll $
>                         tmap (pairs' (destinations q a))
>                         (destinations p a)
>           newPairs = unionAll $ tmap newPairs' (alphabet fsa)

We only need to check each pair of states once: (1, 2) and (2, 1) are
equivalent in this sense.  Since they are not equivalent in Haskell,
we define a function to ensure that each pair is only built in one
direction.

> makePair :: (Ord a) => a -> a -> (a, a)
> makePair a b = (min a b, max a b)

> pairs :: (Ord a) => Set a -> Set (a, a)
> pairs xs = unionAll $ tmap (\x -> pairs' (keep (> x) xs) x) xs

> pairs' :: (Ord a) => Set a -> a -> Set (a, a)
> pairs' xs x = tmap (\y -> makePair x y) xs

An FSA is certainly not minimal if there are states that cannot be
reached by any path from the initial state.  We can trim those.

> trimUnreachables :: (Ord e, Ord n) => FSA n e -> FSA n e
> trimUnreachables fsa = FSA alpha trans init fin (isDeterministic fsa)
>     where alpha = alphabet fsa
>           init = initials fsa
>           fin = intersection reachables (finals fsa)
>           trans = keep ((isIn reachables) . source) (transitions fsa)
>           reachables = reachables' init
>           reachables' qs
>               | newqs == qs  = qs
>               | otherwise    = reachables' newqs
>               where initialIDs a = tmap (flip ID (a : [])) qs
>                     next = (unionAll
>                             (tmap
>                              (tmap state . step fsa . initialIDs . Symbol)
>                              alpha))
>                     newqs = union next qs

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
>     where reverseTransition (Transition x s d) = Transition x d s
>           reverseTransitions = tmap reverseTransition . transitions

> trimFailStates :: (Ord e, Ord n) => FSA n e -> FSA n e
> trimFailStates = FSA.reverse . trimUnreachables . FSA.reverse

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
> -- two strings \(u\) and \(v\) are equivalent if
> -- \(MuM=MvM\)
> jEquivalence :: (Ord e, Ord n) =>
>                 FSA ([Maybe n], [Symbol e]) e ->
>                 Set (Set (State ([Maybe n], [Symbol e])))
> jEquivalence f = splitJEqClass f $
>                  Set.fromList [finals f, difference (states f) (finals f)]

> splitJEqClass :: (Ord e, Ord n) =>
>                  FSA ([Maybe n], [Symbol e]) e ->
>                  Set (Set (State ([Maybe n], [Symbol e]))) ->
>                  Set (Set (State ([Maybe n], [Symbol e])))
> splitJEqClass f xi
>     | size new == size xi  = xi
>     | otherwise            = splitJEqClass f new
>     where new = unionAll $ tmap (splitJEqClass' f xi) xi

> splitJEqClass' :: (Ord e, Ord n) =>
>                   FSA ([Maybe n], [Symbol e]) e ->
>                   Set (Set (State ([Maybe n], [Symbol e]))) ->
>                   Set (State ([Maybe n], [Symbol e])) ->
>                   Set (Set (State ([Maybe n], [Symbol e])))
> splitJEqClass' f xi s
>     | size s == 0  = empty
>     | otherwise    = insert (insert x ys) (splitJEqClass' f xi ys')
>     where (x, xs)  = choose s
>           ys       = keep ((==) (p2 f x) . p2 f) xs
>           ys'      = difference xs ys

The primitive left-ideal of an element x of the syntactic monoid is
the set of elements {ax} for all elements a:

> pl :: (Ord n, Ord e) => FSA (n, [Symbol e]) e ->
>       State (n, [Symbol e]) -> Set (State (n, [Symbol e]))
> pl f x = unmaybe $ tmap (d x) (states f)
>     where d a q    = pull                                   .
>                      until (allS (null . string)) (step f)  .
>                      singleton . ID q . snd $ nodeLabel a
>           pull cs  = if size cs == 0
>                      then Nothing
>                      else Just . state $ chooseOne cs
>           unmaybe cs
>               | size cs == 0  = empty
>               | otherwise     = case y of
>                                   Just a  -> insert a (unmaybe ys)
>                                   _       -> unmaybe ys
>               where (y, ys) = choose cs

> pr :: (Ord n, Ord e) => FSA n e -> State n -> Set (State n)
> pr f x = snd $ until
>          ((==) 0 . size . fst)
>          (\(a,b) -> let p = pr' a
>                     in (difference p b, union p b))
>          (singleton x, singleton x)
>     where pr'     = tmap state . unionAll . tmap pr''
>           pr'' x  = step f $ tmap (ID x . singleton . Symbol) (alphabet f)

> p2 :: (Ord n, Ord e) => FSA (n, [Symbol e]) e ->
>       State (n, [Symbol e]) -> Set (State (n, [Symbol e]))
> p2 f = unionAll . tmap (pr f) . pl f


Determinization
================

Converting a non-deterministic FSA to a deterministic one (DFA) can
improve the speed of determining whether the language represented by
the FSA contains a string.  Further, both complexity-classification
and minimization require DFAs as input.

> metaFlip :: Ord n => Set (State n) -> State (Set n)
> metaFlip = State . tmap nodeLabel

> powersetConstruction :: (Ord e, Ord n) =>
>                         FSA n e ->
>                         Set (State n) ->
>                         (Set (State n) -> Bool) ->
>                         FSA (Set n) e
> powersetConstruction f start isFinal = FSA (alphabet f) trans init fin True
>     where init = singleton (metaFlip start)
>           buildTransition a q = (a, q, delta f (Symbol a) q)
>           buildTransitions' q = tmap (\a -> buildTransition a q)
>                                 (alphabet f)
>           buildTransitions = unionAll . tmap buildTransitions'
>           trans'' = until
>                      (\(a, b, c) -> size b == size c)
>                      (\(a, b, c) ->
>                       let d = buildTransitions (difference c b) in
>                       (union a d, c, union c $ tmap (\(_, _, z) -> z) d))
>                      (empty, empty, singleton start)
>           makeRealTransition (a, b, c) = Transition (Symbol a)
>                                          (metaFlip b)
>                                          (metaFlip c)
>           trans' = let (a, _, _) = trans'' in a
>           trans = tmap makeRealTransition trans'
>           fin = tmap metaFlip
>                 (keep
>                  isFinal
>                  (tmap (\(_, x, _) -> x) trans'))

> -- |Returns a deterministic automaton representing the same
> -- stringset as the potentially nondeterministic input.
> determinize :: (Ord e, Ord n) => FSA n e -> FSA (Set n) e
> determinize f
>     | isDeterministic f = renameStatesBy singleton f
>     | otherwise = powersetConstruction f (initials f) isFinal
>     where isFinal = not . Set.null . intersection (finals f) .
>                     unionAll . tmap (epsilonClosure f)


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
> powersetGraph f = powersetGraph' f hasAccept
>     where hasAccept qs  = intersection (finals f) qs /= empty

> powersetGraph' :: (Ord e, Ord n) =>
>                           FSA n e ->
>                           (Set (State n) -> Bool) ->
>                           FSA (Set n) e
> powersetGraph' f isFinal = powersetConstruction f
>                            (states f)
>                            isFinal


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
> syntacticMonoid m = FSA (alphabet m) t i f True
>     where i          = singleton . fmap (flip (,) [])  .
>                        sequence . map (fmap Just) $ s
>           s          = Set.toList (initials m) ++
>                        Set.toList (difference (states m) (initials m))
>           n          = size (initials m)
>           i'         = if (intersection (finals m) (initials m) /= empty)
>                        then i
>                        else empty
>           (t,_,f,_)  = syntacticMonoid' m n (empty, i, i', i)

> syntacticMonoid' :: (Ord e, Ord n) => FSA n e -> Int ->
>                     (Set (Transition ([Maybe n], [Symbol e]) e),
>                      Set (State ([Maybe n], [Symbol e])),
>                      Set (State ([Maybe n], [Symbol e])),
>                      Set (State ([Maybe n], [Symbol e]))) ->
>                    (Set (Transition ([Maybe n], [Symbol e]) e),
>                     Set (State ([Maybe n], [Symbol e])),
>                     Set (State ([Maybe n], [Symbol e])),
>                     Set (State ([Maybe n], [Symbol e])))
> syntacticMonoid' f n former@(ot, os, ofi, s)
>     | size s == 0   = former
>     | otherwise     = syntacticMonoid' f n next
>     where next      = (union nt ot, union ns os, union nf ofi, ns)
>           alpha     = alphabet f
>           step a q  = replaceDestinationFromMap (union s os) $
>                       Transition (Symbol a) q (step' (Symbol a) q)
>           step' a   = fmap (mapsnd (++ [a])) .
>                       fmap (mapfst $
>                             tmap (maybe Nothing
>                                   (flip (curry (pull .
>                                                 uncurry (flip (delta f) .
>                                                          singleton .
>                                                          State)))
>                                    a)))
>           pull xs   = if xs == empty
>                       then Nothing
>                       else nodeLabel $ fmap Just (chooseOne xs)
>           nt        = mergeByDestFst . unionAll $ tmap nt' alpha
>           nt' a     = tmap (step a) s
>           ns        = keep (isNotIn os' . fmap fst) (tmap destination nt)
>           nf        = keep hasFinal ns
>           os'       = tmap (fmap fst) os
>           fins      = nodeLabel . sequence . map (fmap Just) .
>                       Set.toList $ finals f
>           hasFinal  = not . (==0) . size . intersection fins .
>                       take n . fst . nodeLabel

> replaceDestinationFromMap :: (Container (c (State (a, b))) (State (a, b)),
>                               Collapsible c, Eq a) =>
>                              c (State (a, b)) -> Transition (a, b) e ->
>                              Transition (a, b) e
> replaceDestinationFromMap m t
>     | size m' == 0  = t
>     | otherwise     = Transition (edgeLabel t) (source t) (chooseOne m')
>     where m'  = keep ((==) (fn $ destination t) . fn) m
>           fn  = fst . nodeLabel

> mergeByDestFst :: (Container (c (Transition (n, n') e))
>                    (Transition (n, n') e),
>                    Collapsible c, Ord n, Ord n', Ord e) =>
>                   c (Transition (n, n') e) -> c (Transition (n, n') e)
> mergeByDestFst l = mergeByDestFst' empty l

> mergeByDestFst' :: (Container (c (Transition (n, n') e))
>                     (Transition (n, n') e),
>                     Collapsible c, Ord n, Ord n', Ord e) =>
>                    c (Transition (n, n') e) -> c (Transition (n, n') e) ->
>                    c (Transition (n, n') e)
> mergeByDestFst' p l
>     | size l == 0  = p
>     | otherwise    = mergeByDestFst'
>                      (union p   .
>                       insert x  $
>                       tmap (set_dest (destination x)) sds)
>                      (difference xs sds)
>     where (x, xs)       = choose l
>           fnd           = fst . nodeLabel . destination
>           sds           = keep ((==) (fnd x) . fnd) xs
>           set_dest d t  = Transition (edgeLabel t) (source t) d


Alphabet Manipulation
=====================

> -- |Add missing symbols to the alphabet of an automaton.
> extendAlphabetTo :: (Ord a, Ord b) => Set b -> FSA a b ->
>                   FSA (Maybe Integer, Maybe a) b
> extendAlphabetTo syms = autUnion (emptyWithAlphabet syms)

> -- |Remove symbols from the alphabet of an automaton.
> contractAlphabetTo :: (Ord a, Ord b) => Set b -> FSA a b ->
>                       FSA a b
> contractAlphabetTo syms fsa = trimUnreachables $
>                               FSA syms trans
>                               (initials fsa)
>                               (finals fsa)
>                               (isDeterministic fsa)
>     where trans = keep
>                   (isIn (insert Epsilon $ tmap Symbol syms)
>                    . edgeLabel) $
>                   transitions fsa

> -- |Ignore the alphabet of an automaton and use a given alphabet instead.
> forceAlphabetTo :: (Ord a, Ord b) => Set b -> FSA a b ->
>                    FSA (Maybe Integer, Maybe a) b
> forceAlphabetTo syms = contractAlphabetTo syms . extendAlphabetTo syms


Miscellaneous Functions
=======================

After several operations, the nodeLabel type of an FSA becomes a deep
mixture of pairs, maybes, and sets.  We can smash these into a smaller
type to improve memory usage and processing speed.

> -- |Equivalent to 'renameStatesBy' \(f\),
> -- where \(f\) is an arbitrary injective function.
> renameStates :: (Ord e, Ord n, Ord n1, Enum n1) => FSA n e -> FSA n1 e
> renameStates fsa = renameStatesBy
>                    (toEnum . size . fst . flip Set.split sts)
>                    fsa
>     where sts = tmap nodeLabel $ states fsa
> {-# INLINE[1] renameStates #-}
> {-# RULES
>   "renameStates/identity" renameStates = id
>   #-}

> -- |Transform the node labels of an automaton using a given function.
> -- If this function is not injective, the resulting FSA may not be
> -- deterministic even if the original was.
> renameStatesBy :: (Ord e, Ord n, Ord n1) =>
>                   (n -> n1) -> FSA n e -> FSA n1 e
> renameStatesBy f a = a { transitions      =  tmap
>                                              (transition . fmap f . Noitisnart)
>                                              (transitions a)
>                        , initials         =  tmap (fmap f) (initials a)
>                        , finals           =  tmap (fmap f) (finals a)
>                        , isDeterministic  =  isDeterministic a &&
>                                              size ns == size (states a)
>                        }
>     where ns = tmap (fmap f) (states a)

> -- |Transform the edge labels of an automaton using a given function.
> -- If this function is not injective, the resulting FSA may not be
> -- deterministic even if the original was.
> renameSymbolsBy :: (Ord e, Ord e1, Ord n) =>
>                    (e -> e1) -> FSA n e -> FSA n e1
> renameSymbolsBy f a = a { alphabet         =  alpha
>                         , transitions      =  tmap (fmap f) (transitions a)
>                         , isDeterministic  =  isDeterministic a &&
>                                               size alpha == size (alphabet a)
>                         }
>     where alpha  =  tmap f (alphabet a)

Mapping on tuples:

> mapfst :: (a -> b) -> (a, c) -> (b, c)
> mapfst f (a, b) = (f a, b)

> mapsnd :: (b -> c) -> (a, b) -> (a, c)
> mapsnd f (a, b) = (a, f b)

A parallel fold implementation based on a tree.  The accumulating
function must be both associative and commutative, as the tree is
built in such a way that order of elements is not preserved.

> data Tree a = Leaf a | Tree (Tree a) (Tree a)
>               deriving (Eq, Ord, Read, Show)
> treeFromList :: [a] -> Tree a
> treeFromList [] = error "No elements"
> treeFromList (x:[]) = Leaf x
> treeFromList xs = ls' `par` rs' `pseq` Tree ls' rs'
>     where (ls, rs) = rEvenOdds xs
>           (ls', rs') = (treeFromList ls, treeFromList rs)
> listFromTree :: Tree a -> [a]
> listFromTree (Leaf x) = [x]
> listFromTree (Tree l r) = listFromTree l ++ listFromTree r

> instance NFData a => NFData (Tree a) where
>     rnf (Leaf a) = rnf a
>     rnf (Tree l r) = rnf l `seq` rnf r

> treeFold :: (a -> a -> a) -> Tree a -> a
> treeFold _ (Leaf x) = x
> treeFold mappend (Tree l r) = l' `par` r' `pseq` (l' `mappend` r')
>     where l' = treeFold mappend l
>           r' = treeFold mappend r

Split a linked list into two smaller lists by taking the even and odd
elements.  This does not require computing the list's length, thus it
can be more efficient than splitting at the middle element.

> rEvenOdds :: [a] -> ([a],[a])
> rEvenOdds = rEvenOdds' ([],[])
>     where rEvenOdds' p      []        =  p
>           rEvenOdds' (a,b)  (x:[])    =  (x:a, b)
>           rEvenOdds' (a,b)  (x:y:xs)  =  rEvenOdds' (x:a, y:b) xs
