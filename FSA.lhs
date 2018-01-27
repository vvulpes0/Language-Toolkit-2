> {-# Language
>   ExistentialQuantification,
>   FlexibleContexts,
>   FlexibleInstances,
>   MultiParamTypeClasses
>   #-}
> module FSA where

> import Data.Set (Set)
> import qualified Data.Set as Set
> import LogicClasses
> import Control.DeepSeq
> import Control.Parallel.Strategies

Introduction
============

The purpose of this module is to define an interface to a generic,
reusable implementation of finite-state automata (FSAs).  The primary
motivation for this is to allow for an efficient analysis yielding
provable results regarding sub-regular languages, although the nature
of the project should allow more general use.

In this case, finite-state automata are represented mathematically as
directional graphs with edges labelled by formal symbols.


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

> data FSA n e = FSA (Set (Symbol e))
>     (Set (Transition n e))
>     (Set (State n))
>     (Set (State n))
>     (Bool)
>     deriving (Show, Read)

FSAs represent languages, so it makes sense to use equivalence of the
represented languages as the criterion for equivalence of the FSAs
themselves.  First, an FSA represents the empty language if it has
no reachable accepting states:

> isNull :: (Ord e, Ord n) => FSA n e -> Bool
> isNull = (== empty) . finals . trimUnreachables

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

> instance (Ord e, Ord n) => Eq (FSA n e) where
>     (==) = isomorphic

> instance (Enum n, Ord n, Ord e) => Container (FSA n e) [Symbol e] where
>     isIn = accepts
>     union = curry (renameStates . uncurry autUnion)
>     intersection = curry (renameStates . uncurry autIntersection)
>     difference = curry (renameStates . uncurry autDifference)
>     empty = emptyLanguage
>     singleton = (\a -> renameStates a `asTypeOf` a) . singletonLanguage

> rEvenOdds :: [a] -> ([a],[a])
> rEvenOdds = rEvenOdds' ([],[])
>     where rEvenOdds' p      []        =  p
>           rEvenOdds' (a,b)  (x:[])    =  (x:a, b)
>           rEvenOdds' (a,b)  (x:y:xs)  =  rEvenOdds' (x:a, y:b) xs

> flatIntersection :: (Enum n, Ord n, NFData n, Ord e, NFData e) =>
>                     [FSA n e] -> FSA n e
> flatIntersection [] = error "Cannot take a nullary intersection"
> flatIntersection (x:[]) = x `using` rdeepseq
> flatIntersection xs = s (intersection a b) `using` rdeepseq
>     where a = flatIntersection a'
>           b = flatIntersection b'
>           s f = (renameStates . minimize) f `asTypeOf` f
>           (a',b') = rEvenOdds xs

> flatUnion :: (Enum n, Ord n, NFData n, Ord e, NFData e) =>
>              [FSA n e] -> FSA n e
> flatUnion [] = error "Cannot take a nullary union"
> flatUnion (x:[]) = x `using` rdeepseq
> flatUnion xs = s (union a b) `using` rdeepseq
>     where a = flatIntersection a'
>           b = flatIntersection b'
>           s f = (renameStates . minimize) f `asTypeOf` f
>           (a',b') = rEvenOdds xs

> instance (NFData n, NFData e) => NFData (FSA n e) where
>     rnf (FSA a t i f d) = rnf a `seq` rnf t `seq` rnf i `seq`
>                           rnf f `seq` rnf d

Here we define some accessor functions for the members of FSA, not
because pattern matching against constructors is inherently wrong, but
because there are two arguments of the same type with no completely
intuitive order.  Being able to export the type completely abstractly
is only a side benefit.

> alphabet :: FSA n e -> Set (Symbol e)
> alphabet (FSA a _ _ _ _) = a

> transitions :: FSA n e -> Set (Transition n e)
> transitions (FSA _ t _ _ _) = t

> initials :: FSA n e -> Set (State n)
> initials (FSA _ _ i _ _) = i

> finals :: FSA n e -> Set (State n)
> finals (FSA _ _ _ f _) = f

> states :: (Ord e, Ord n) => FSA n e -> Set (State n)
> states f = unionAll [initials f, finals f, others]
>    where others           = unionAll $ tmap extractStates ts
>          extractStates t  = doubleton (source t) (destination t)
>          doubleton a b    = insert b (singleton a)
>          ts               = transitions f

> isDeterministic :: FSA n e -> Bool
> isDeterministic (FSA _ _ _ _ d) = d

A singleton FSA is one that accepts exactly one (possibly-empty)
string.  The number of states in such an FSA is equal to the length of
the string plus two.

> totalWithAlphabet :: (Ord e, Enum n, Ord n) => Set (Symbol e) -> FSA n e
> totalWithAlphabet as = FSA as trans (singleton q) (singleton q) True
>     where trans  = tmap (flip (flip Transition q) q) as
>           q      = State $ toEnum 0

> emptyWithAlphabet :: (Ord e, Enum n, Ord n) => Set (Symbol e) -> FSA n e
> emptyWithAlphabet as = FSA as trans (singleton q) empty True
>     where trans  = tmap (flip (flip Transition q) q) as
>           q      = State $ toEnum 0

> emptyLanguage :: (Ord e, Ord n, Enum n) => FSA n e
> emptyLanguage = emptyWithAlphabet empty

> singletonWithAlphabet :: (Ord e, Enum n, Ord n) =>
>                          Set (Symbol e) -> [Symbol e] -> FSA n e
> singletonWithAlphabet as syms = FSA as (trans str) begins finals True
>     where str = keep (/= Epsilon) syms
>           trans xs = union (trans' xs (toEnum 1)) failTransitions
>           trans' [] n = tmap (\a -> Transition a (State n) fail) as
>           trans' (x:xs) n = let m = succ n in
>                             (union (trans' xs m) $
>                              tmap (\y -> Transition y (State n)
>                                          $ (if (x == y)
>                                             then State m
>                                             else fail))
>                              as)
>           fail = State $ toEnum 0
>           failTransitions = tmap (\a -> Transition a fail fail) as
>           begins = singleton (State $ toEnum 1)
>           last = (+ 1) . fromIntegral . length $ str
>           finals = singleton (State $ toEnum last)

> singletonLanguage :: (Ord e, Enum n, Ord n) => [Symbol e] -> FSA n e
> singletonLanguage s = singletonWithAlphabet (Set.fromList s) s


Formal Symbols
--------------

The edges of an FSA are labelled by either a formal symbol or the
pseudo-symbol Epsilon.  Specifically, an edge labelled by Epsilon
represents a transition that may occur without consuming any further
input.

> data Symbol e = Epsilon
>               | Symbol e
>               deriving (Eq, Ord, Read, Show)

> instance Functor Symbol where
>     fmap _ Epsilon     =  Epsilon
>     fmap f (Symbol e)  =  Symbol (f e)

> instance (NFData e) => NFData (Symbol e) where
>     rnf Epsilon = ()
>     rnf (Symbol e) = rnf e

States
------

The vertices of the graph representation of an FSA are states, which
can be labelled with any arbitrary values, so long as every state of
a single automaton is labelled with an element of the same type.

> data State n = State n deriving (Eq, Ord, Read, Show)

> nodeLabel :: State n -> n
> nodeLabel (State a) = a

> instance Functor State where
>     fmap f (State a) = State (f a)

> instance (NFData n) => NFData (State n) where
>     rnf (State n) = rnf n

Transitions
-----------

If a state is the vertex of a graph, then a transition is its edge.
Since an FSA is represented by a directed graph, there are three
components to a transition: an edge label, and two states.  If a
computation in the first state encounters a symbol matching the
transition's edge label, then it moves to the second state.

> data Transition n e = Transition (Symbol e) (State n) (State n)
>                     deriving (Eq, Ord, Show, Read)

> edgeLabel :: Transition n e -> Symbol e
> edgeLabel (Transition a _ _) = a

> source :: Transition n e -> State n
> source (Transition _ b _) = b

> destination :: Transition n e -> State n
> destination (Transition _ _ c) = c

> instance (NFData n, NFData e) => NFData (Transition n e) where
>     rnf (Transition x q1 q2) = rnf x `seq` rnf q1 `seq` rnf q2

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

> accepts :: (Ord e, Ord n) => FSA n e -> [Symbol e] -> Bool
> accepts fsa = anyS (isIn (finals fsa)) . tmap state . compute fsa


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

> combineAlphabets :: Ord e => FSA n e -> FSA n1 e -> Set (Symbol e)
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
>               where n1 = nexts x f1 . State . fst $ nodeLabel qp
>                     n2 = nexts x f2 . State . snd $ nodeLabel qp
>           stateFromPair (q1, q2) = State (nodeLabel q1, nodeLabel q2)
>           extensionsOnSymbol qp x = tmap (Transition x qp) $
>                                     nextPairs x qp
>           extensions qp = unionAll $ tmap (extensionsOnSymbol qp) bigalpha
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

> autDifference :: (Ord e, Ord n1, Ord n2) => FSA n1 e -> FSA n2 e ->
>                  FSA (Maybe n1, Maybe n2) e
> autDifference f1 f2 = FSA bigalpha trans init fin det
>     where bigalpha = combineAlphabets f1 f2
>           cs = tmap (\(x, y) -> combine x y)
>           init = cs $ makeJustPairs (initials f1) (initials f2)
>           fin1 = finals f1
>           fin1WithNonFin2 = makeJustPairs fin1
>                             (difference (states f2) (finals f2))
>           fin1WithN = tmap (flip (,) (State Nothing) . fmap Just) fin1
>           fin = (intersection sts
>                  (cs
>                   (unionAll [fin1WithNonFin2, fin1WithN])))
>           trans = combineTransitions f1 f2
>           sts = union (tmap source trans) (tmap destination trans)
>           det = isDeterministic f1 && isDeterministic f2

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

> complement :: (Ord e, Ord n) => FSA n e -> FSA (Set n) e
> complement f = FSA (alphabet d) (transitions d) (initials d) fins True
>     where d = determinize f
>           fins = difference (states d) (finals d)

> complementDeterminized :: (Ord e, Ord n) => FSA n e -> FSA n e
> complementDeterminized f
>     | not (isDeterministic f)  = undefined
>     | otherwise                = FSA (alphabet f)
>                                  (transitions f)
>                                  (initials f)
>                                  (difference (states f) (finals f))
>                                  True


Minimization
============

In general, operations on FSAs have run time proportional to some
(increasing) function of how many states the FSA has.  With this in
mind, we provide a function to make an FSA as small as possible
without loss of information.

We begin by constructing the set of Myhill-Nerode equivalence classes
for the states of the input FSA, then simply replace each state by its
equivalence class.

> minimize :: (Ord e, Ord n) => FSA n e -> FSA (Set (Set n)) e
> minimize = minimizeOver nerode . determinize

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
>     where destinations s x = delta fsa x (singleton s)
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
>                              (tmap state . step fsa . initialIDs)
>                              alpha))
>                     newqs = union next qs

An FSA will often contain states from which no path at all leads to an
accepting state.  These represent failure to match a pattern, which
can be represented equally well by explicit lack of a transition.
Thus we can safely remove them.  Given that we already have a function
to remove states that cannot be reached, the simplest way to remove
these fail-states is to trim the unreachable states in the reversal of
the FSA.

> reverse :: (Ord e, Ord n) => FSA n e -> FSA n e
> reverse f = (FSA (alphabet f)
>              (reverseTransitions f)
>              (finals f) (initials f) False)
>     where reverseTransition (Transition x s d) = Transition x d s
>           reverseTransitions = tmap reverseTransition . transitions

> trimFailStates :: (Ord e, Ord n) => FSA n e -> FSA n e
> trimFailStates = FSA.reverse . trimUnreachables . FSA.reverse

An FSA is in normal form if it has been both minimized and trimmed.

> normalize :: (Ord e, Ord n) => FSA n e -> FSA Int e
> normalize = renameStates . trimFailStates . minimize . trimUnreachables


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
>           pr'' x  = step f $ tmap (ID x . singleton) (alphabet f)

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
>           buildTransition a q = (a, q, delta f a q)
>           buildTransitions' q = tmap (\a -> buildTransition a q)
>                                 (alphabet f)
>           buildTransitions = unionAll . tmap buildTransitions'
>           trans'' = until
>                      (\(a, b, c) -> size b == size c)
>                      (\(a, b, c) ->
>                       let d = buildTransitions (difference c b) in
>                       (union a d, c, union c $ tmap (\(_, _, z) -> z) d))
>                      (empty, empty, singleton start)
>           makeRealTransition (a, b, c) = Transition a
>                                          (metaFlip b)
>                                          (metaFlip c)
>           trans' = let (a, _, _) = trans'' in a
>           trans = tmap makeRealTransition trans'
>           fin = tmap metaFlip
>                 (keep
>                  isFinal
>                  (tmap (\(_, x, _) -> x) trans'))


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

> generatePowerSetGraph :: (Ord e, Ord n) => FSA n e -> FSA (Set Int) e
> generatePowerSetGraph f = generatePowerSetGraph' d hasAccept
>     where d             = normalize f
>           hasAccept qs  = intersection (finals d) qs /= empty

> generatePowerSetGraph' :: (Ord e, Ord n) =>
>                           FSA n e ->
>                           (Set (State n) -> Bool) ->
>                           FSA (Set n) e
> generatePowerSetGraph' f isFinal = powersetConstruction f
>                                    (states f)
>                                    isFinal


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

> extractState :: [State x] -> State [x]
> extractState = State . map nodeLabel

> generateSyntacticMonoid :: (Ord e, Ord n) =>
>                            FSA n e -> FSA ([Maybe n], [Symbol e]) e
> generateSyntacticMonoid m = FSA (alphabet m) t i f True
>     where i          = singleton . fmap (flip (,) [])  .
>                        extractState . map (fmap Just) $ s
>           s          = Set.toList (initials m) ++
>                        Set.toList (difference (states m) (initials m))
>           n          = size (initials m)
>           i'         = if (intersection (finals m) (initials m) /= empty)
>                        then i
>                        else empty
>           (t,_,f,_)  = generateSyntacticMonoid' m n (empty, i, i', i)

> generateSyntacticMonoid' :: (Ord e, Ord n) => FSA n e -> Int ->
>                             (Set (Transition ([Maybe n], [Symbol e]) e),
>                              Set (State ([Maybe n], [Symbol e])),
>                              Set (State ([Maybe n], [Symbol e])),
>                              Set (State ([Maybe n], [Symbol e]))) ->
>                             (Set (Transition ([Maybe n], [Symbol e]) e),
>                              Set (State ([Maybe n], [Symbol e])),
>                              Set (State ([Maybe n], [Symbol e])),
>                              Set (State ([Maybe n], [Symbol e])))
> generateSyntacticMonoid' f n former@(ot, os, ofi, s)
>     | size s == 0   = former
>     | otherwise     = generateSyntacticMonoid' f n next
>     where next      = (union nt ot, union ns os, union nf ofi, ns)
>           alpha     = alphabet f
>           step a q  = replaceDestinationFromMap (union s os) $
>                       Transition a q (step' a q)
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
>           fins      = nodeLabel . extractState . map (fmap Just) .
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


Miscellaneous Functions
=======================

After several operations, the nodeLabel type of an FSA becomes a deep
mixture of pairs, maybes, and sets.  We can smash these into a smaller
type to improve memory usage and processing speed.

> renameStates :: (Ord e, Ord n, Ord n1, Enum n1) => FSA n e -> FSA n1 e
> renameStates fsa = renameStatesBy f fsa
>     where sts      = Set.fromList $
>                      zip (Set.toList . tmap nodeLabel $ states fsa)
>                      [1..]
>           f x      = pull $ keep ((== x) . fst) sts
>           pull xs  = if xs == empty
>                      then toEnum 0
>                      else toEnum . snd $ chooseOne xs

> renameStatesBy :: (Ord e, Ord n, Ord n1) =>
>                   (n -> n1) -> FSA n e -> FSA n1 e
> renameStatesBy f a = FSA (alphabet a) trans init fin (isDeterministic a)
>     where sts    = states a
>           rnt t  = Transition
>                    (edgeLabel t)
>                    (rns (source t))
>                    (rns (destination t))
>           rns    = fmap f
>           trans  = tmap rnt (transitions a)
>           init   = tmap rns (initials a)
>           fin    = tmap rns (finals a)

The renameStates function had been using Set.findIndex, but I have
been made aware that this does not exist in older versions of the
Haskell platform.  So we emulate it here:

> findIndexInSet :: (Ord a) => a -> Set a -> Int
> findIndexInSet x s
>     | found = size l
>     | otherwise = error "element is not in the set"
>     where (l, found, _) = Set.splitMember x s

Mapping on tuples:

> mapfst :: (a -> b) -> (a, c) -> (b, c)
> mapfst f (a, b) = (f a, b)

> mapsnd :: (b -> c) -> (a, b) -> (a, c)
> mapsnd f (a, b) = (a, f b)
