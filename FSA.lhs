> {-# Language UnicodeSyntax #-}
> module FSA where

> import qualified Data.Set as Set


Introduction
============

The purpose of this module is to define an interface to a generic,
reusable implementation of finite-state automata (FSAs).  The primary
motivation for this is to allow for an efficient analysis yielding
provable results regarding sub-regular languages, although the nature
of the project should allow more general use.

In this case, finite-state automata are represented mathematically as
directional graphs with edges labelled by formal symbols.


Set Theory and its Symbols
==========================

The standard mathematical symbols for set operations will be used
throughout this module.  The exception to this is that ∅ (empty set)
is parenthesized to comply with Haskell's naming rules.  In addition,
I define a function `unionAll` that collapses a set of sets of (a)
into a single set of (a), using the union operation.  `unionAll` is
also written as the N-ARY UNION symbol, ⋃.  Note that Haskell requires
symbolic operators to be parenthesized when used in prefix notation.

> infixl 7 ∩
> (∩) ∷ Ord a ⇒ Set.Set a → Set.Set a → Set.Set a
> (∩) = Set.intersection

> infixl 6 ∪
> (∪) ∷ Ord a ⇒ Set.Set a → Set.Set a → Set.Set a
> (∪) = Set.union

> infixl 6 ∖
> (∖) ∷ Ord a ⇒ Set.Set a → Set.Set a → Set.Set a
> (∖) = (Set.\\)

> infixl 8 ∈
> (∈) ∷ Ord a ⇒ a → Set.Set a → Bool
> (∈) = Set.member

> infixl 8 ∉
> (∉) ∷ Ord a ⇒ a → Set.Set a → Bool
> (∉) = Set.notMember

> (∅) ∷ Set.Set a
> (∅) = Set.empty

> unionAll ∷ Ord a ⇒ Set.Set (Set.Set a) → Set.Set a
> unionAll = Set.fold (∪) (∅)

> (⋃) ∷ Ord a ⇒ Set.Set (Set.Set a) → Set.Set a
> (⋃) = unionAll

Older versions of Haskell (pre 7.?) don't have the Foldable typeclass,
but we want to be able to use the `all` and `any` constructions over
sets.  I recreate them here with allS and anyS.

> allS ∷ Ord a ⇒ (a → Bool) → Set.Set a → Bool
> allS f xs = all f (Set.toList xs)

> anyS ∷ Ord a ⇒ (a → Bool) → Set.Set a → Bool
> anyS f xs = any f (Set.toList xs)


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

> data FSA a b = FSA (Set.Set (Symbol a))
>     (Set.Set (Transition a b))
>     (Set.Set (State b))
>     (Set.Set (State b))
>     (Bool)
>     deriving (Read, Show)

Here we define some accessor functions for the members of FSA, not
because pattern matching against constructors is inherently wrong, but
because there are two arguments of the same type with no completely
intuitive order.  Being able to export the type completely abstractly
is only a side benefit.

> alphabet ∷ FSA a b → Set.Set (Symbol a)
> alphabet (FSA a _ _ _ _) = a

> transitions ∷ FSA a b → Set.Set (Transition a b)
> transitions (FSA _ t _ _ _) = t

> initials ∷ FSA a b → Set.Set (State b)
> initials (FSA _ _ i _ _) = i

> finals ∷ FSA a b → Set.Set (State b)
> finals (FSA _ _ _ f _) = f

> states ∷ (Ord a, Ord b) ⇒ FSA a b → Set.Set (State b)
> states f = initials f ∪ finals f ∪ others
>     where others          = (⋃) (Set.map extractStates ts)
>           extractStates t = doubleton (source t) (destination t)
>           doubleton a b   = Set.insert b (Set.singleton a)
>           ts              = transitions f

> isDeterministic ∷ FSA a b → Bool
> isDeterministic (FSA _ _ _ _ d) = d

The empty FSA has a single state and accepts no strings, not even the
empty string.

> empty ∷ Integral b ⇒ FSA a b
> empty = emptyWithAlphabet (∅)

A singleton FSA is one that accepts exactly one (possibly-empty)
string.  The number of states in such an FSA is equal to the length of
the string plus two.

> singleton ∷ (Ord a, Integral b, Ord b) ⇒ [Symbol a] → FSA a b
> singleton syms = FSA alphabet (trans str) begins finals True
>     where str = filter (/= Epsilon) syms
>           alphabet = (Set.fromList str)
>           trans xs = trans' xs 1 ∪ failTransitions
>           trans' [] n = Set.map (\a → Transition a (State n) fail) alphabet
>           trans' (x:xs) n = let m = succ n in
>                                 (Set.map (\y → Transition y (State n)
>                                                $ (if (x == y)
>                                                   then State m
>                                                   else fail))
>                                  alphabet) ∪ trans' xs m
>           fail = State 0
>           failTransitions = Set.map (\a → Transition a fail fail) alphabet
>           begins = Set.singleton (State 1)
>           last   = (+ 1) . fromIntegral . length $ str
>           finals = Set.singleton (State last)

> emptyWithAlphabet ∷ Integral b ⇒ Set.Set (Symbol a) → FSA a b
> emptyWithAlphabet as = FSA as (∅) (Set.singleton (State 0)) (∅) True

> singletonWithAlphabet ∷ (Ord a, Integral b, Ord b) ⇒ [Symbol a] → Set.Set (Symbol a) → FSA a (Maybe b, Maybe b)
> singletonWithAlphabet str as = singleton str ∨ emptyWithAlphabet as


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

> data State a = State a deriving (Eq, Ord, Read, Show)

> label ∷ State a → a
> label (State a) = a


Transitions
-----------

If a state is the vertex of a graph, then a transition is its edge.
Since an FSA is represented by a directed graph, there are three
components to a transition: a label, and two states.  If a computation
in the first state encounters a symbol matching the transition's
label, then it moves to the second state.

Normally, the label of a transition would be referred to as such, but
in this case that would result in a namespace clash.  Thus, this
module refers to this edge label as a path.

> data Transition a b = Transition (Symbol a) (State b) (State b)
>                       deriving (Eq, Read, Show)

> path ∷ Transition a b → Symbol a
> path (Transition a _ _) = a

> source ∷ Transition a b → State b
> source (Transition _ b _) = b

> destination ∷ Transition a b → State b
> destination (Transition _ _ c) = c

> instance (Ord a, Ord b) ⇒ Ord (Transition a b) where
>     t1 <= t2
>         | s1 /= s2  = s1 < s2
>         | p1 /= p2  = p1 < p2
>         | otherwise = d1 <= d2
>         where (s1, p1, d1) = (source t1, path t1, destination t1)
>               (s2, p2, d2) = (source t2, path t2, destination t2)

To determine whether an FSA accepts a string of Symbols, there must
exist a mechanism to determine which State to enter upon consuming a
Symbol.  The set of Transitions describes the map, and we will use
that to define the transition function.

> data ID a b = ID (State b) [Symbol a] deriving (Eq, Ord, Read, Show)

> state ∷ ID a b → State b
> state (ID a _) = a

> string ∷ ID a b → [Symbol a]
> string (ID _ xs) = xs

> epsilonClosure ∷ (Ord a, Ord b) ⇒ FSA a b → State b → Set.Set (State b)
> epsilonClosure fsa q
>     | isDeterministic fsa = Set.singleton q
>     | otherwise           = epsilonClosure' fsa (Set.singleton q)
>     where epsilons = Set.filter ((== Epsilon) . path) (transitions fsa)
>           epsilonClosure' fsa seen
>               | numNew == 0 = seen
>               | otherwise   = epsilonClosure' fsa closure
>               where seens = Set.filter ((∈ seen) . source) epsilons
>                     closure = seen ∪ Set.map destination seens
>                     numNew = Set.size closure - Set.size seen

> step ∷ (Ord a, Ord b) ⇒ FSA a b → Set.Set (ID a b) → Set.Set (ID a b)
> step fsa ids
>     | Set.null filteredIDs = (∅)
>     | otherwise = (⋃) (Set.map next filteredIDs)
>     where ts = transitions fsa
>           filterID id = ID (state id) (filter (/= Epsilon) (string id))
>           filteredIDs = Set.map filterID ids
>           next i
>               | null s    = Set.map (flip ID []) closure
>               | otherwise = Set.map (flip ID (tail s)) outStates
>               where s = string i
>                     closure = epsilonClosure fsa (state i)
>                     sameSource = Set.filter ((∈ closure) . source) ts
>                     samePath   = Set.filter ((== head s) . path) sameSource
>                     outStates  = ((⋃)
>                                   (Set.map
>                                    (epsilonClosure fsa . destination)
>                                    samePath))

We should not have to produce IDs ourselves.  We can define the transition
function δ from an FSA, a symbol, and a state to a set of states:

> δ ∷ (Ord a, Ord b) ⇒ FSA a b → Symbol a → Set.Set (State b) → Set.Set (State b)
> δ f x = Set.map state . step f . Set.map ((flip ID) [x])

> compute ∷ (Ord a, Ord b) ⇒ FSA a b → [Symbol a] → Set.Set (ID a b)
> compute fsa str = until (allS (null . string)) (step fsa) initialIDs
>     where initialIDs = Set.map (flip ID str) (initials fsa)

> accepts ∷ (Ord a, Ord b) ⇒ FSA a b → [Symbol a] → Bool
> accepts fsa = anyS (`Set.member` finals fsa) . Set.map state . compute fsa


Logical Operators
=================

> combine ∷ State a → State b → State (a, b)
> combine a b = State (label a, label b)

> makePairs ∷ (Ord a, Ord b) ⇒ Set.Set (State a) → Set.Set (State b) → Set.Set (State (a, b))
> makePairs xs ys = (⋃) (Set.map (\x → Set.map (\y → combine x y) ys) xs)

> makeJustPairs ∷ (Ord a, Ord b) ⇒ Set.Set (State a) → Set.Set (State b) → Set.Set (State (Maybe a, Maybe b))
> makeJustPairs xs ys = makePairs (justify xs) (justify ys)
>     where justify ∷ (Ord c) ⇒ Set.Set (State c) → Set.Set (State (Maybe c))
>           justify = Set.map (State . Just . label)

> combineAlphabets ∷ Ord a ⇒ FSA a b → FSA a c → Set.Set (Symbol a)
> combineAlphabets f1 f2 = alphabet f1 ∪ alphabet f2

> combineTransitions ∷ (Ord a, Ord b, Ord c) ⇒ FSA a b → FSA a c → Set.Set (Transition a (Maybe b, Maybe c))
> combineTransitions f1 f2 = trans
>     where bigalpha = combineAlphabets f1 f2
>           delta f a q
>               | label q == Nothing = Set.singleton (State Nothing)
>               | Set.null oneStep   = Set.singleton (State Nothing)
>               | otherwise          = Set.map (State . Just . label) oneStep
>               where oneStep = Set.map state (step f ids)
>                     (State (Just q')) = q
>                     ids = Set.singleton (ID (State q') [a])
>           unpair p = (l, r)
>               where l = (State . fst . label) p
>                     r = (State . snd . label) p
>           pair l r = State (label l, label r)
>           trans = trans' (∅) (∅) (makeJustPairs (initials f1) (initials f2))
>           trans' trs seen ps
>               | Set.size newseen == Set.size seen = newtrs
>               | otherwise = trans' newtrs newseen newps
>               where newtrs = trs ∪ ((⋃) (Set.map newtrs' bigalpha))
>                     newtrs' a = (⋃) (Set.map (newtrs'' a) ps)
>                     newtrs'' a p = ((⋃)
>                                     (Set.map
>                                      (\x → Set.map
>                                       (\y → Transition a p (pair x y))
>                                       (delta f2 a r))
>                                      (delta f1 a l)))
>                         where  (l, r) = unpair p
>                     newseen = Set.map source newtrs
>                               ∪ Set.map destination newtrs
>                     newps   = newseen ∖ seen

> infixl 7 ∧
> (∧) ∷ (Ord a, Ord b, Ord c) ⇒ FSA a b → FSA a c → FSA a (Maybe b, Maybe c)
> (∧) = intersection

> intersection ∷ (Ord a, Ord b, Ord c) ⇒ FSA a b → FSA a c → FSA a (Maybe b, Maybe c)
> intersection f1 f2 = FSA bigalpha trans init fin det
>     where bigalpha = combineAlphabets f1 f2
>           init = makeJustPairs (initials f1) (initials f2)
>           fin  = (makeJustPairs (finals f1) (finals f2)) ∩ sts
>           trans = combineTransitions f1 f2
>           sts = Set.map source trans ∪ Set.map destination trans
>           det = isDeterministic f1 && isDeterministic f2

> infixl 6 ∨
> (∨) ∷ (Ord a, Ord b, Ord c) ⇒ FSA a b → FSA a c → FSA a (Maybe b, Maybe c)
> (∨) = union

> union ∷ (Ord a, Ord b, Ord c) ⇒ FSA a b → FSA a c → FSA a (Maybe b, Maybe c)
> union f1 f2 = FSA bigalpha trans init fin det
>     where bigalpha = combineAlphabets f1 f2
>           init = makeJustPairs (initials f1) (initials f2)
>           fin1 = finals f1
>           fin2 = finals f2
>           fin1With2 = makeJustPairs fin1 (states f2)
>           fin2With1 = makeJustPairs (states f1) fin2
>           fin1WithN = Set.map (\x → State (Just (label x), Nothing)) fin1
>           fin2WithN = Set.map (\x → State (Nothing, Just (label x))) fin2
>           fin = sts ∩ (fin1WithN ∪ fin2WithN ∪ fin1With2 ∪ fin2With1)
>           trans = combineTransitions f1 f2
>           sts = Set.map source trans ∪ Set.map destination trans
>           det = isDeterministic f1 && isDeterministic f2

> renameStates ∷ (Ord a, Ord b, Integral c) ⇒ FSA a b → FSA a c
> renameStates fsa = FSA (alphabet fsa) trans init fin (isDeterministic fsa)
>     where sts = states fsa
>           index x xs = fromIntegral (x `findIndexInSet` xs)
>           renameTransition t = Transition (path t) a b
>               where a = renameState (source t)
>                     b = renameState (destination t)
>           renameState q = State (q `index` sts)
>           trans = Set.map renameTransition (transitions fsa)
>           init = Set.map renameState (initials fsa)
>           fin = Set.map renameState (finals fsa)

The renameStates function had been using Set.findIndex, but I have
been made aware that this does not exist in older versions of the
Haskell platform.  So we emulate it here:

> findIndexInSet ∷ (Ord a) ⇒ a → Set.Set a → Int
> findIndexInSet x s
>     | found = Set.size l
>     | otherwise = error "element is not in the set"
>     where (l, found, _) = Set.splitMember x s

> (¬) ∷ (Ord a, Ord b) ⇒ FSA a b → FSA a (Set.Set b)
> (¬) = complement

> complement ∷ (Ord a, Ord b) ⇒ FSA a b → FSA a (Set.Set b)
> complement f = FSA (alphabet d) (transitions d) (initials d) fins True
>     where d = determinize f
>           fins = states d ∖ finals d

> difference ∷ (Ord a, Ord b, Ord c) ⇒ FSA a b → FSA a c → FSA a (Maybe b, Maybe (Set.Set c))
> difference x y = x ∧ (¬) y

> trimUnreachables ∷ (Ord a, Ord b) ⇒ FSA a b → FSA a b
> trimUnreachables fsa = FSA alpha trans init fin (isDeterministic fsa)
>     where alpha = alphabet fsa
>           init = initials fsa
>           fin = finals fsa ∩ reachables
>           trans = Set.filter ((∈ reachables) . source) (transitions fsa)
>           reachables = reachables' init
>           reachables' qs
>               | newqs == qs = qs
>               | otherwise   = reachables' newqs
>               where initialIDs a = Set.map (flip ID (a : [])) qs
>                     next = ((⋃)
>                             (Set.map
>                              (Set.map state . step fsa . initialIDs)
>                              alpha))
>                     newqs = next ∪ qs


Minimization
============

In general, operations on FSAs have run time proportional to some
(increasing) function of how many states the FSA has.  With this in
mind, we provide a function to make an FSA as small as possible
without loss of information.

We begin by constructing the set of Myhill-Nerode equivalence classes
for the states of the input FSA, then simply replace each state by its
equivalence class.

> minimize ∷ (Ord a, Ord b) ⇒ FSA a b → FSA a (Set.Set (Set.Set b))
> minimize fsa = trimUnreachables newfsa
>     where dfa = determinize fsa
>           classes = equivalenceClasses dfa
>           classOf x = State ((⋃) (Set.map
>                                   (Set.map label)
>                                   (Set.filter (x ∈) classes)))
>           init = Set.map classOf (initials dfa)
>           fin = Set.map classOf (finals dfa)
>           trans = (Set.map
>                    (\(Transition a p q) →
>                     Transition a (classOf p) (classOf q))
>                    (transitions dfa))
>           newfsa = FSA (alphabet dfa) trans init fin True

> equivalenceClasses ∷ (Ord a, Ord b) ⇒ FSA a b → Set.Set (Set.Set (State b))
> equivalenceClasses fsa = Set.map eqClass sts
>     where sts = states fsa
>           i = i' ∪ Set.map (\x → (x, x)) sts
>           i' = pairs sts ∖ distinguishedPairs fsa
>           eqClass x = (Set.singleton x
>                        ∪ (Set.map snd . Set.filter ((== x) . fst)) i
>                        ∪ (Set.map fst . Set.filter ((== x) . snd)) i)

The easiest way to construct the equivalence classes is to iteratively
build a set of known-distinct pairs.  In the beginning we know that
any accepting state is distinct from any non-accepting state.  At each
further iteration, two states p and q are distinct if there exists
some symbol σ such that δ<sub>σ</sub>(p) is distinct from
δ<sub>σ</sub>(q).

When an iteration completes without updating the set of known-distinct
pairs, the algorithm is finished; all possible distinctions have been
discovered.  The Myhill-Nerode equivalence class of a state p, then,
is the set of states not distinct from p.

> distinguishedPairs ∷ (Ord a, Ord b) ⇒ FSA a b → Set.Set (State b, State b)
> distinguishedPairs fsa = fst result
>     where allPairs = pairs (states fsa)
>           initiallyDistinguished = ((⋃)
>                                     (Set.map
>                                      (pairs' (finals fsa))
>                                      (states fsa ∖ finals fsa)))
>           f d (a, b) = areDistinguishedByOneStep fsa d a b
>           result = (until
>                     (\(x, y) → Set.size x == Set.size y)
>                     (\(x, _) → (x ∪ Set.filter (f x) (allPairs ∖ x), x))
>                     (initiallyDistinguished, (∅)))

> areDistinguishedByOneStep ∷ (Ord a, Ord b) ⇒ FSA a b → Set.Set (State b, State b) → State b → State b → Bool
> areDistinguishedByOneStep fsa knownDistinct p q
>     | makePair p q ∈ knownDistinct = True
>     | otherwise = anyS (∈ knownDistinct) newPairs
>     where destinations s x = (Set.map state
>                              . step fsa
>                              . Set.singleton
>                              . ID s) [x]
>           newPairs' a = (⋃) (Set.map
>                              (pairs' (destinations q a))
>                              (destinations p a))
>           newPairs = (⋃) (Set.map newPairs' (alphabet fsa))

We only need to check each pair of states once: (1, 2) and (2, 1) are
equivalent in this sense.  Since they are not equivalent in Haskell,
we define a function to ensure that each pair is only built in one
direction.

> makePair ∷ (Ord a) ⇒ a → a → (a, a)
> makePair a b = (min a b, max a b)

> pairs ∷ (Ord a) ⇒ Set.Set a → Set.Set (a, a)
> pairs xs = (⋃) (Set.map (\x → pairs' (Set.filter (>x) xs) x) xs)

> pairs' ∷ (Ord a) ⇒ Set.Set a → a → Set.Set (a, a)
> pairs' xs x = Set.map (\y → makePair x y) xs

An FSA will often contain states from which no path leads to an
accepting state.  These represent failure to match a pattern, which
can be represented equally well by explicit lack of a transition.
Thus we can safely remove them.  Given that we already have a function
to remove states that cannot be reached, the simplest way to remove
these fail-states is to trim the unreachable states in the reversal of
the FSA.

> reverse ∷ (Ord a, Ord b) ⇒ FSA a b → FSA a b
> reverse f = (FSA (alphabet f)
>              (reverseTransitions f)
>              (finals f) (initials f) False)
>     where reverseTransition (Transition x s d) = Transition x d s
>           reverseTransitions = Set.map reverseTransition . transitions

> trimFailStates ∷ (Ord a, Ord b) ⇒ FSA a b → FSA a b
> trimFailStates = FSA.reverse . trimUnreachables . FSA.reverse

An FSA is in normal form if it has been both minimized and trimmed.

> normalize ∷ (Ord a, Ord b, Integral c) ⇒ FSA a b → FSA a c
> normalize = renameStates . trimFailStates . minimize . trimUnreachables


Determinization
================

Converting a non-deterministic FSA to a deterministic one (DFA) can
improve the speed of determining whether the language represented by
the FSA contains a string.  Further, both complexity-classification
and minimization require DFAs as input.

> metaFlip ∷ (Ord a) ⇒ Set.Set (State a) → State (Set.Set a)
> metaFlip = State . Set.map label

> determinize ∷ (Ord a, Ord b) ⇒ FSA a b → FSA a (Set.Set b)
> determinize f
>     | isDeterministic f = FSA (alphabet f)
>                           (wrapStates (transitions f))
>                           (wrap (initials f)) (wrap (finals f))
>                           True
>     | otherwise = FSA (alphabet f) trans inits fins True
>     where inits = Set.singleton (metaFlip (initials f))
>           buildTransition a q = Transition a
>                                 (State q) (State (δ f a q))
>           buildTransitions' q = Set.map (\a → buildTransition a q)
>                                 (alphabet f)
>           buildTransitions = (⋃) . Set.map buildTransitions'
>           trans' = until
>                    (\(a, b, c) → Set.size b == Set.size c)
>                    (\(a, b, c) →
>                     let d = buildTransitions (c ∖ b) in
>                     (a ∪ d, c, c ∪ Set.map (label . destination) d))
>                    ((∅), (∅), Set.singleton (initials f))
>           fixTransition t = Transition (path t)
>                             ((metaFlip . label) (source t))
>                             ((metaFlip . label) (destination t))
>           trans = let (a, _, _) = trans' in Set.map fixTransition a
>           fins = Set.filter
>                  (\s → label s ∩ Set.map label (finals f) /= (∅))
>                  (Set.map source trans ∪ Set.map destination trans)
>           wrapStates' (Transition x s d) = Transition x (wrap' s) (wrap' d)
>           wrapStates = Set.map wrapStates'
>           wrap' = State . Set.singleton . label
>           wrap = Set.map wrap'


Syntactic Monoids
=================

I'll describe what these are later.  Suffice it to say for now that
they are a thing that is useful in determining whether or not a
language is SL, and further allow us to determine what the minimal
disallowed substrings are.

Let D be a DFA with set of states Q and alphabet Σ, and let δ
represent the transition function of D.  Further, let δ<sub>σ</sub>
denote the transition function whose symbol argument is given as σ.
From this, we can derive a new DFA whose states are members of P(Q)
with the following conditions:

* The initial state is Q
* For all S ∈ P(Q) and σ ∈ Σ, there exists an edge from S on σ to
  δ<sub>σ</sub>(S)
* No other edges exist
* Accepting states are those with strictly fewer than 2 elements

This DFA is the syntactic monoid of the original.

> generateSyntacticMonoid ∷ (Ord a, Ord b, Integral c) ⇒ FSA a b → FSA a (Set.Set c)
> generateSyntacticMonoid f = newfsa
>     where fsa = normalize f
>           partial = FSA alpha (∅) (Set.singleton q) (∅) True
>           alpha = alphabet fsa
>           init = states fsa
>           q = metaFlip (states fsa)
>           newfsa = generateSyntacticMonoid' fsa partial (Set.singleton q)

> generateSyntacticMonoid' ∷ (Ord a, Ord b) ⇒ FSA a b → FSA a (Set.Set b) → (Set.Set (State (Set.Set b))) → FSA a (Set.Set b)
> generateSyntacticMonoid' fsa partial toTry
>     | states partial == states newfsa = newfsa
>     | otherwise = generateSyntacticMonoid' fsa newfsa nextToTry
>     where newfsa = FSA alpha newTrans init fin True
>           alpha = alphabet fsa
>           init = initials partial
>           nt a = Set.map (\q →
>                           Transition a
>                                      q
>                                      ((metaFlip .
>                                        δ fsa a .
>                                        Set.map (State) .
>                                        label)
>                                       q)
>                  ) toTry
>           newTrans = (⋃) (Set.map nt alpha) ∪ transitions partial
>           tStates = states $ FSA (∅) newTrans (∅) (∅) True
>           nextToTry = tStates ∖ states partial
>           fin = Set.filter ((<2) . Set.size . label) tStates ∪ finals partial

From there, it is easy to discern whether a language is SL<sub>k</sub>
or not by simply enumerating all strings of length (k-1) and
determining if they are accepted.  If one is not, then it is not
SL<sub>k</sub>.

(Note: we should check for non-trivial loops!)

> wordsOfLength ∷ (Ord a, Integral b) ⇒ b → Set.Set (Symbol a) → Set.Set [Symbol a]
> wordsOfLength n xs
>     | n <= 0 = (∅)
>     | n == 1 = Set.map (:[]) xs
>     | otherwise = (⋃) (Set.map (\x → Set.map (x:) smaller) xs)
>     where smaller = wordsOfLength (n - 1) xs

isSLk wants a Syntactic Monoid as an argument.  It's also a terrible
algorithm, but we'll ignore that for now.

> isSLk ∷ (Ord a, Ord b, Integral c) ⇒ FSA a b → c → Bool
> isSLk fsa k
>     | k > 1 = (allS id .
>                Set.map (accepts fsa) .
>                wordsOfLength (k-1) .
>                alphabet) fsa
>     | otherwise = False

kCheck returns the smallest k for which a given FSA is SL, giving up
after 12 for no particular reason.  Or, there is a reason, and it is
that I don't do loop tests yet.

> kCheck ∷ (Ord a, Ord b, Integral c) ⇒ FSA a b → c
> kCheck fsa = kCheck' sm 1
>     where sm = generateSyntacticMonoid fsa

> kCheck' ∷ (Ord a, Ord b, Integral c) ⇒ FSA a b → c → c
> kCheck' sm k
>     | k > 12 = -1
>     | isSLk sm k = k
>     | otherwise = kCheck' sm (k+1)

We also want to be able to see what factors are disallowed.  In order
to take only the minimal forbidden factors, we need a substring test.

> isSublistOf ∷ (Eq a) ⇒ [a] → [a] → Bool
> isSublistOf xs [] = False
> isSublistOf xs ys
>     | xs `isPrefixOf` ys = True
>     | xs `isSublistOf` (tail ys) = True
>     | otherwise = False

> isPrefixOf ∷ (Eq a) ⇒ [a] → [a] → Bool
> isPrefixOf [] ys = True
> isPrefixOf xs [] = False
> isPrefixOf (x:xs) (y:ys)
>     | x == y = xs `isPrefixOf` ys
>     | otherwise = False

Then we can construct a (somewhat inefficient) test to see what
factors are necessarily excluded.  We'll start by searching for
factors that are disallowed *everywhere*, because that is the simplest
of the tests.

> disallowedFactors ∷ (Ord a, Ord b) ⇒ FSA a b → Set.Set [Symbol a]
> disallowedFactors f = disallowedFactors' f'' (∅) (kCheck f) 1
>     where f' = generateSyntacticMonoid f
>           f'' = FSA (alphabet f') (transitions f') (initials f')
>                 (Set.filter (not . Set.null . label) (states f'))
>                 (isDeterministic f')

We will define a convenience function that takes as input a syntactic
monoid with initial and final states modified to reflect our current
search, which returns a list of disallowed factors.  This is reusable
in our search for anchored factors.

> disallowedFactors' ∷ (Ord a, Ord b, Integral c) ⇒ FSA a b → Set.Set [Symbol a] → c → c → Set.Set [Symbol a]
> disallowedFactors' f ws k x
>     | k < 1 = Set.fromList []
>     | x > k = ws
>     | otherwise = disallowedFactors' f (ws ∪ newws'') k (x + 1)
>     where newws = wordsOfLength x (alphabet f)
>           newws' = Set.filter
>                    (\w → (not . anyS (\x → x `isSublistOf` w)) ws)
>                    newws
>           newws'' = Set.filter (not . accepts f) newws'


Showing Data
============

Most of these will be replaced with derived instances later.  For now,
I'm using these to force GHCi to output things in a (non-standard) way
that I can read more easily.

< instance (Show a, Show b) ⇒ Show (FSA a b) where
<     show a = "< Σ=" ++ showSet (alphabet a)
<              ++ " T=" ++ showSet (transitions a)
<              ++ " I=" ++ showSet (initials a)
<              ++ " F=" ++ showSet (finals a) ++ " >"
<         where showSet ∷ (Show x) ⇒ Set.Set x → String
<               showSet = (++ "}") . ('{' :) . showList . Set.toList
<               showList [] = ""
<               showList (x:[]) = show x
<               showList (x:xs) = show x ++ ", " ++ showList xs

< instance Show a ⇒ Show (Symbol a) where
<     show Epsilon    = "ε"
<     show (Symbol a) = show a

< instance Show a ⇒ Show (State a) where
<     show a = show (label a)

< instance (Show a, Show b) ⇒ Show (Transition a b) where
<     show t = show (source t)
<              ++ " (" ++ show (path t)
<              ++ ") → " ++ show (destination t)
