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


Introduction
============

The purpose of this module is to define an interface to a generic,
reusable implementation of finite-state automata (FSAs).  The primary
motivation for this is to allow for an efficient analysis yielding
provable results regarding sub-regular languages, although the nature
of the project should allow more general use.

In this case, finite-state automata are represented mathematically as
directional graphs with edges labelled by formal symbols.

> instance (Ord a) => Container (FSA a) [Symbol a] where
>     isIn            = accepts
>     union           = funion
>     intersection    = fintersection
>     difference a b  = intersection a (complement b)
>     empty           = emptyWithAlphabet empty
>     singleton s     = singletonWithAlphabet s (Set.fromList s)


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

> data FSA a = FSA (Set (Symbol a))
>     (Set (Transition a))
>     (Set State)
>     (Set State)
>     (Bool)
>     deriving (Show, Read)

FSAs represent languages, so it makes sense to use equivalence of the
represented languages as the criterion for equivalence of the FSAs
themselves.  First, an FSA represents the empty language if it has
no accepting states:

> isNull :: (Ord a) => FSA a -> Bool
> isNull = (== empty) . finals . trimUnreachables

> instance (Ord a) => Eq (FSA a) where
>     a == b = (alphabet a == alphabet b) &&
>              isNull (difference a b) &&
>              isNull (difference b a)

Here we define some accessor functions for the members of FSA, not
because pattern matching against constructors is inherently wrong, but
because there are two arguments of the same type with no completely
intuitive order.  Being able to export the type completely abstractly
is only a side benefit.

> alphabet :: FSA a -> Set (Symbol a)
> alphabet (FSA a _ _ _ _) = a

> transitions :: FSA a -> Set (Transition a)
> transitions (FSA _ t _ _ _) = t

> initials :: FSA a -> Set State
> initials (FSA _ _ i _ _) = i

> finals :: FSA a -> Set State
> finals (FSA _ _ _ f _) = f

> states :: (Ord a) => FSA a -> Set State
> states f = unionAll [initials f, finals f, others]
>    where others           = unionAll $ tmap extractStates ts
>          extractStates t  = doubleton (source t) (destination t)
>          doubleton a b    = insert b (singleton a)
>          ts               = transitions f

> isDeterministic :: FSA a -> Bool
> isDeterministic (FSA _ _ _ _ d) = d

A singleton FSA is one that accepts exactly one (possibly-empty)
string.  The number of states in such an FSA is equal to the length of
the string plus two.

> emptyWithAlphabet :: (Ord a) => Set (Symbol a) -> FSA a
> emptyWithAlphabet as = FSA as empty (singleton (State 0)) empty True

> singletonWithAlphabet :: (Ord a) => [Symbol a] -> Set (Symbol a) -> FSA a
> singletonWithAlphabet syms as = FSA as (trans str) begins finals True
>     where str = keep (/= Epsilon) syms
>           trans xs = union (trans' xs 1) failTransitions
>           trans' [] n = tmap (\a -> Transition a (State n) fail) as
>           trans' (x:xs) n = let m = succ n in
>                             (union (trans' xs m) $
>                              tmap (\y -> Transition y (State n)
>                                          $ (if (x == y)
>                                             then State m
>                                             else fail))
>                              as)
>           fail = State 0
>           failTransitions = tmap (\a -> Transition a fail fail) as
>           begins = singleton (State 1)
>           last = (+ 1) . fromIntegral . length $ str
>           finals = singleton (State last)


Formal Symbols
--------------

The edges of an FSA are labelled by either a formal symbol or the
pseudo-symbol ε.  Specifically, an edge labelled by ε represents a
transition that may occur without consuming any further input.

> data Symbol a = Epsilon
>               | Symbol a
>               deriving (Eq, Ord, Read, Show)


States
------

The vertices of the graph representation of an FSA are states, which
can be labelled with any arbitrary values.  Typically these values are
integers for ease of representation, but often it is useful to use
complete strings here.  This implementation allows any value whose
type is an instance of Ord to operate as the labels of an FSA's
states.  The restriction to Ord types is due to Data.Set requiring it
for efficient implementation of sets.

> data State = forall a. (Ord a, Show a, Read a) => State a

> nodeLabel :: State -> String
> nodeLabel (State a) = show a

> instance Show State where
>     showsPrec p (State s) = showParen (p > app_prec) $
>                             showString "State " .
>                             showsPrec (app_prec + 1) (show s)
>                     where app_prec = 10

> instance Read State where
>     readsPrec d r = readParen (d > app_prec)
>                     (\r -> [(State m, t) |
>                            ("State", s) <- lex r,
>                            (m, t) <- (readsPrec :: Int -> ReadS String) (app_prec + 1) s]) r
>         where app_prec = 10

> instance Eq State where
>     a == b = nodeLabel a == nodeLabel b

> instance Ord State where
>     compare a b = compare (nodeLabel a) (nodeLabel b)


Transitions
-----------

If a state is the vertex of a graph, then a transition is its edge.
Since an FSA is represented by a directed graph, there are three
components to a transition: an edge label, and two states.  If a computation
in the first state encounters a symbol matching the transition's
edge label, then it moves to the second state.

> data Transition a = Transition (Symbol a) State State
>                     deriving (Eq, Ord, Show, Read)

> edgeLabel :: Transition a -> Symbol a
> edgeLabel (Transition a _ _) = a

> source :: Transition a -> State
> source (Transition _ b _) = b

> destination :: Transition a -> State
> destination (Transition _ _ c) = c

To determine whether an FSA accepts a string of Symbols, there must
exist a mechanism to determine which State to enter upon consuming a
Symbol.  The set of Transitions describes the map, and we will use
that to define the transition function.

> data ID a = ID State [Symbol a] deriving (Eq, Ord, Show)

> state :: ID a -> State
> state (ID a _) = a

> string :: ID a -> [Symbol a]
> string (ID _ xs) = xs

> epsilonClosure :: (Ord a) => FSA a -> State -> Set State
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

> step :: (Ord a) => FSA a -> Set (ID a) -> Set (ID a)
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

> delta :: (Ord a) => FSA a -> Symbol a -> Set State -> Set State
> delta f x = tmap state . step f . tmap ((flip ID) [x])

> compute :: (Ord a) => FSA a -> [Symbol a] -> Set (ID a)
> compute fsa str = until (allS (null . string)) (step fsa) initialIDs
>     where initialIDs = tmap (flip ID str) (initials fsa)

> accepts :: (Ord a) => FSA a -> [Symbol a] -> Bool
> accepts fsa = anyS (isIn (finals fsa)) . tmap state . compute fsa


Logical Operators
=================

> combine :: State -> State -> State
> combine (State a) (State b) = State (a, b)

> makePairs :: Set State -> Set State -> Set (State, State)
> makePairs xs ys = unionAll $ tmap (\x -> tmap (\y -> (x, y)) ys) xs

> makeJustPairs :: Set State -> Set State -> Set (State, State)
> makeJustPairs xs ys = makePairs (justify xs) (justify ys)
>     where justify :: Set State -> Set State
>           justify = tmap (\(State z) -> State (Just z))

> combineAlphabets :: (Ord a) => FSA a -> FSA a -> Set (Symbol a)
> combineAlphabets f1 f2 = union (alphabet f1) (alphabet f2)

> combineTransitions :: (Ord a) => FSA a -> FSA a -> Set (Transition a)
> combineTransitions f1 f2 = trans
>     where bigalpha = combineAlphabets f1 f2
>           delta' :: (Ord a) => FSA a -> Symbol a -> State -> Set (Maybe State)
>           delta' f a q
>               | oneStep == empty  = singleton (Nothing)
>               | otherwise         = tmap Just oneStep
>               where oneStep = delta f a (singleton q)
>           js (State c) = State (Just c)
>           jt (Transition a b c) = Transition a (js b) (js c)
>           jf (FSA a t i f d) = FSA a (tmap jt t) (tmap js i) (tmap js f) d
>           j1 = jf f1
>           j2 = jf f2
>           m Nothing = State (Nothing :: Maybe Int)
>           m (Just (State c)) = State c
>           trans = (trans' empty empty
>                    (makeJustPairs (initials f1) (initials f2)))
>           trans' trs seen ps
>               | size newseen == size seen = newtrs
>               | otherwise = trans' newtrs newseen newps
>               where newtrs' = unionAll $ tmap newtrs'' bigalpha
>                     newtrs'' a = unionAll $ tmap (newtrs''' a) ps
>                     newtrs''' a (l, r) = (unionAll
>                                           (tmap
>                                            (\x -> tmap
>                                                   (\y -> (a,
>                                                           (l, r),
>                                                           (m x, m y)))
>                                                   (delta' j2 a r))
>                                            (delta' j1 a l)))
>                     newtrs = (union trs
>                               (tmap
>                                (\(a, (x1, x2), (y1, y2))
>                                     -> (Transition a
>                                         (combine x1 x2)
>                                         (combine y1 y2)))
>                                newtrs'))
>                     newseen = (union
>                                (tmap (\(_, x, _) -> x) newtrs')
>                                (tmap (\(_, _, y) -> y) newtrs'))
>                     newps   = difference newseen seen

> fintersection :: (Ord a) => FSA a -> FSA a -> FSA a
> fintersection f1 f2 = FSA bigalpha trans init fin det
>     where bigalpha = combineAlphabets f1 f2
>           cs = tmap (\(x, y) -> combine x y)
>           init = cs $ makeJustPairs (initials f1) (initials f2)
>           fin  = (intersection sts
>                   (cs (makeJustPairs (finals f1) (finals f2))))
>           trans = combineTransitions f1 f2
>           sts = union (tmap source trans) (tmap destination trans)
>           det = isDeterministic f1 && isDeterministic f2

> funion :: (Ord a) => FSA a -> FSA a -> FSA a
> funion f1 f2 = FSA bigalpha trans init fin det
>     where bigalpha = combineAlphabets f1 f2
>           cs = tmap (\(x, y) -> combine x y)
>           init = cs $ makeJustPairs (initials f1) (initials f2)
>           fin1 = finals f1
>           fin2 = finals f2
>           n = State (Nothing :: Maybe Int)
>           fin1With2 = makeJustPairs fin1 (states f2)
>           fin2With1 = makeJustPairs (states f1) fin2
>           fin1WithN = tmap (\(x, _) -> (x, n)) fin1With2
>           fin2WithN = tmap (\(_, y) -> (n, y)) fin2With1
>           fin = (intersection sts
>                  (cs
>                   (unionAll [fin1WithN, fin2WithN, fin1With2, fin2With1])))
>           trans = combineTransitions f1 f2
>           sts = union (tmap source trans) (tmap destination trans)
>           det = isDeterministic f1 && isDeterministic f2

> renameStates :: (Ord a) => FSA a -> FSA a
> renameStates fsa = FSA (alphabet fsa) trans init fin (isDeterministic fsa)
>     where sts = states fsa
>           index x xs = fromIntegral (x `findIndexInSet` xs)
>           renameTransition t = Transition (edgeLabel t) a b
>               where a = renameState (source t)
>                     b = renameState (destination t)
>           renameState q = State (q `index` sts)
>           trans = tmap renameTransition (transitions fsa)
>           init = tmap renameState (initials fsa)
>           fin = tmap renameState (finals fsa)

The renameStates function had been using Set.findIndex, but I have
been made aware that this does not exist in older versions of the
Haskell platform.  So we emulate it here:

> findIndexInSet :: (Ord a) => a -> Set a -> Int
> findIndexInSet x s
>     | found = size l
>     | otherwise = error "element is not in the set"
>     where (l, found, _) = Set.splitMember x s

> complement :: (Ord a) => FSA a -> FSA a
> complement f = FSA (alphabet d) (transitions d) (initials d) fins True
>     where d = determinize f
>           fins = difference (states d) (finals d)

> trimUnreachables :: (Ord a) => FSA a -> FSA a
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


Minimization
============

In general, operations on FSAs have run time proportional to some
(increasing) function of how many states the FSA has.  With this in
mind, we provide a function to make an FSA as small as possible
without loss of information.

We begin by constructing the set of Myhill-Nerode equivalence classes
for the states of the input FSA, then simply replace each state by its
equivalence class.

> minimize :: (Ord a) => FSA a -> FSA a
> minimize fsa = trimUnreachables newfsa
>     where dfa = determinize fsa
>           classes = equivalenceClasses dfa
>           classOf x = (State . tmap nodeLabel . unionAll)
>                       (keep (contains x) classes)
>           init = tmap classOf (initials dfa)
>           fin = tmap classOf (finals dfa)
>           trans = (tmap
>                    (\(Transition a p q) ->
>                     Transition a (classOf p) (classOf q))
>                    (transitions dfa))
>           newfsa = FSA (alphabet dfa) trans init fin True

> equivalenceClasses :: (Ord a) => FSA a -> Set (Set State)
> equivalenceClasses fsa = tmap eqClass sts
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

> distinguishedPairs :: (Ord a) => FSA a -> Set (State, State)
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

> areDistinguishedByOneStep :: (Ord a) => FSA a -> Set (State, State) -> State -> State -> Bool
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
> pairs xs = unionAll $ tmap (\x -> pairs' (keep (>x) xs) x) xs

> pairs' :: (Ord a) => Set a -> a -> Set (a, a)
> pairs' xs x = tmap (\y -> makePair x y) xs

An FSA will often contain states from which no path at all leads to an
accepting state.  These represent failure to match a pattern, which
can be represented equally well by explicit lack of a transition.
Thus we can safely remove them.  Given that we already have a function
to remove states that cannot be reached, the simplest way to remove
these fail-states is to trim the unreachable states in the reversal of
the FSA.

> reverse :: (Ord a) => FSA a -> FSA a
> reverse f = (FSA (alphabet f)
>              (reverseTransitions f)
>              (finals f) (initials f) False)
>     where reverseTransition (Transition x s d) = Transition x d s
>           reverseTransitions = tmap reverseTransition . transitions

> trimFailStates :: (Ord a) => FSA a -> FSA a
> trimFailStates = FSA.reverse . trimUnreachables . FSA.reverse

An FSA is in normal form if it has been both minimized and trimmed.

> normalize :: (Ord a) => FSA a -> FSA a
> normalize = renameStates . trimFailStates . minimize . trimUnreachables


Determinization
================

Converting a non-deterministic FSA to a deterministic one (DFA) can
improve the speed of determining whether the language represented by
the FSA contains a string.  Further, both complexity-classification
and minimization require DFAs as input.

> metaFlip :: Set (State) -> State
> metaFlip = State . tmap nodeLabel

> powersetConstruction :: (Ord a) => FSA a -> Set State -> (Set State -> Bool) -> FSA a
> powersetConstruction f start isFinal = FSA (alphabet f) trans inits fins True
>     where inits = singleton (metaFlip start)
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
>           fins = tmap metaFlip
>                  (keep
>                   isFinal
>                   (tmap (\(_, x, _) -> x) trans'))


> determinize :: (Ord a) => FSA a -> FSA a
> determinize f
>     | isDeterministic f = f
>     | otherwise = powersetConstruction f
>                   (initials f)
>                   (\s -> intersection s (finals f) /= empty)


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

> generatePowerSetGraph :: (Ord a) => FSA a -> FSA a
> generatePowerSetGraph f = generatePowerSetGraph' d hasAccept
>     where d             = normalize f
>           hasAccept qs  = intersection (finals d) qs /= empty

> generatePowerSetGraph' :: (Ord a) => FSA a -> (Set State -> Bool) -> FSA a
> generatePowerSetGraph' f isFinal = powersetConstruction f
>                                    (states f)
>                                    isFinal
