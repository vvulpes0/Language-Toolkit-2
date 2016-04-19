> {-# Language UnicodeSyntax #-}
> module FSA where

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

> instance (Ord a) ⇒ Container (FSA a) [Symbol a] where
>     (∈) = flip accepts
>     (∪) = union
>     (∩) = intersection
>     a ∖ b = a ∩ (¬) b
>     (∅) = empty


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

> data FSA a = FSA (Set.Set (Symbol a))
>     (Set.Set (Transition a))
>     (Set.Set State)
>     (Set.Set State)
>     (Bool)
>     deriving (Show)

Here we define some accessor functions for the members of FSA, not
because pattern matching against constructors is inherently wrong, but
because there are two arguments of the same type with no completely
intuitive order.  Being able to export the type completely abstractly
is only a side benefit.

> alphabet ∷ FSA a → Set.Set (Symbol a)
> alphabet (FSA a _ _ _ _) = a

> transitions ∷ FSA a → Set.Set (Transition a)
> transitions (FSA _ t _ _ _) = t

> initials ∷ FSA a → Set.Set State
> initials (FSA _ _ i _ _) = i

> finals ∷ FSA a → Set.Set State
> finals (FSA _ _ _ f _) = f

> states ∷ (Ord a) ⇒ FSA a → Set.Set State
> states f = initials f ∪ finals f ∪ others
>    where others          = (⋃) (Set.map extractStates ts)
>          extractStates t = doubleton (source t) (destination t)
>          doubleton a b   = Set.insert b (Set.singleton a)
>          ts              = transitions f

> isDeterministic ∷ FSA a → Bool
> isDeterministic (FSA _ _ _ _ d) = d

The empty FSA has a single state and accepts no strings, not even the
empty string.

> empty ∷ (Ord a) ⇒ FSA a
> empty = emptyWithAlphabet (∅)

A singleton FSA is one that accepts exactly one (possibly-empty)
string.  The number of states in such an FSA is equal to the length of
the string plus two.

> singleton ∷ (Ord a) ⇒ [Symbol a] → FSA a
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

> emptyWithAlphabet ∷ (Ord a) ⇒ Set.Set (Symbol a) → FSA a
> emptyWithAlphabet as = FSA as (∅) (Set.singleton (State 0)) (∅) True

> singletonWithAlphabet ∷ (Ord a) ⇒ [Symbol a] → Set.Set (Symbol a) → FSA a
> singletonWithAlphabet str as = singleton str ∩ emptyWithAlphabet as


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

> data State = forall a. (Ord a, Show a, Read a) ⇒ State a -- deriving (Eq, Ord, Read, Show)

> label ∷ State → String
> label (State a) = show a

> instance Show State where
>     show s = "(State " ++ label s ++ ")"

> instance Eq State where
>     a == b = label a == label b

> instance Ord State where
>     compare a b = label a `compare` label b


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

> data Transition a = Transition (Symbol a) State State
>                     deriving (Eq, Show)

> path ∷ Transition a → Symbol a
> path (Transition a _ _) = a

> source ∷ Transition a → State
> source (Transition _ b _) = b

> destination ∷ Transition a → State
> destination (Transition _ _ c) = c

> instance (Ord a) ⇒ Ord (Transition a) where
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

> data ID a = ID State [Symbol a] deriving (Eq, Ord, Show)

> state ∷ ID a → State
> state (ID a _) = a

> string ∷ ID a → [Symbol a]
> string (ID _ xs) = xs

> epsilonClosure ∷ (Ord a) ⇒ FSA a → State → Set.Set State
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

> step ∷ (Ord a) ⇒ FSA a → Set.Set (ID a) → Set.Set (ID a)
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

> δ ∷ (Ord a) ⇒ FSA a → Symbol a → Set.Set State → Set.Set State
> δ f x = Set.map state . step f . Set.map ((flip ID) [x])

> delta ∷ (Ord a) ⇒ FSA a → Symbol a → Set.Set State → Set.Set State
> delta = δ

> compute ∷ (Ord a) ⇒ FSA a → [Symbol a] → Set.Set (ID a)
> compute fsa str = until (allS (null . string)) (step fsa) initialIDs
>     where initialIDs = Set.map (flip ID str) (initials fsa)

> accepts ∷ (Ord a) ⇒ FSA a → [Symbol a] → Bool
> accepts fsa = anyS (∈ finals fsa) . Set.map state . compute fsa


Logical Operators
=================

> combine ∷ State → State → State
> combine (State a) (State b) = State (a, b)

> makePairs ∷ Set.Set State → Set.Set State → Set.Set (State, State)
> makePairs xs ys = (⋃) (Set.map (\x → Set.map (\y → (x, y)) ys) xs)

> makeJustPairs ∷ Set.Set State → Set.Set State → Set.Set (State, State)
> makeJustPairs xs ys = makePairs (justify xs) (justify ys)
>     where justify ∷ Set.Set State → Set.Set State
>           justify = Set.map (\(State z) → State (Just z))

> combineAlphabets ∷ (Ord a) ⇒ FSA a → FSA a → Set.Set (Symbol a)
> combineAlphabets f1 f2 = alphabet f1 ∪ alphabet f2

> combineTransitions ∷ (Ord a) ⇒ FSA a → FSA a → Set.Set (Transition a)
> combineTransitions f1 f2 = trans
>     where bigalpha = combineAlphabets f1 f2
>           delta ∷ (Ord a) ⇒ FSA a → Symbol a → State → Set.Set (Maybe State)
>           delta f a q
>               | Set.null oneStep = Set.singleton (Nothing)
>               | otherwise        = Set.map Just oneStep
>               where oneStep = δ f a (Set.singleton q)
>           js (State c) = State (Just c)
>           jt (Transition a b c) = Transition a (js b) (js c)
>           jf (FSA a t i f d) = FSA a (Set.map jt t) (Set.map js i) (Set.map js f) d
>           j1 = jf f1
>           j2 = jf f2
>           m Nothing = State (Nothing ∷ Maybe Int)
>           m (Just (State c)) = State c
>           trans = trans' (∅) (∅) (makeJustPairs (initials f1) (initials f2))
>           trans' trs seen ps
>               | Set.size newseen == Set.size seen = newtrs
>               | otherwise = trans' newtrs newseen newps
>               where newtrs' = ((⋃) (Set.map newtrs'' bigalpha))
>                     newtrs'' a = (⋃) (Set.map (newtrs''' a) ps)
>                     newtrs''' a (l, r) = ((⋃)
>                                      (Set.map
>                                       (\x → Set.map
>                                        (\y → (a,
>                                              (l, r),
>                                              (m x, m y)))
>                                        (delta j2 a r))
>                                       (delta j1 a l)))
>                     newtrs = trs ∪ (Set.map
>                                     (\(a, (x1, x2), (y1, y2))
>                                     → Transition a
>                                      (combine x1 x2)
>                                      (combine y1 y2))
>                                     newtrs')
>                     newseen = Set.map (\(_, x, _) → x) newtrs'
>                               ∪ Set.map (\(_, _, y) → y) newtrs'
>                     newps   = newseen ∖ seen

> intersection ∷ (Ord a) ⇒ FSA a → FSA a → FSA a
> intersection f1 f2 = FSA bigalpha trans init fin det
>     where bigalpha = combineAlphabets f1 f2
>           cs = Set.map (\(x, y) → combine x y)
>           init = cs $ makeJustPairs (initials f1) (initials f2)
>           fin  = cs (makeJustPairs (finals f1) (finals f2)) ∩ sts
>           trans = combineTransitions f1 f2
>           sts = Set.map source trans ∪ Set.map destination trans
>           det = isDeterministic f1 && isDeterministic f2

> union ∷ (Ord a) ⇒ FSA a → FSA a → FSA a
> union f1 f2 = FSA bigalpha trans init fin det
>     where bigalpha = combineAlphabets f1 f2
>           cs = Set.map (\(x, y) → combine x y)
>           init = cs $ makeJustPairs (initials f1) (initials f2)
>           fin1 = finals f1
>           fin2 = finals f2
>           n = State (Nothing ∷ Maybe Int)
>           fin1With2 = makeJustPairs fin1 (states f2)
>           fin2With1 = makeJustPairs (states f1) fin2
>           fin1WithN = Set.map (\(x, _) → (x, n)) fin1With2
>           fin2WithN = Set.map (\(_, y) → (n, y)) fin2With1
>           fin = sts ∩ cs (fin1WithN ∪ fin2WithN ∪ fin1With2 ∪ fin2With1)
>           trans = combineTransitions f1 f2
>           sts = Set.map source trans ∪ Set.map destination trans
>           det = isDeterministic f1 && isDeterministic f2

> renameStates ∷ (Ord a) ⇒ FSA a → FSA a
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

> (¬) ∷ (Ord a) ⇒ FSA a → FSA a
> (¬) = complement

> complement ∷ (Ord a) ⇒ FSA a → FSA a
> complement f = FSA (alphabet d) (transitions d) (initials d) fins True
>     where d = determinize f
>           fins = states d ∖ finals d

> trimUnreachables ∷ (Ord a) ⇒ FSA a → FSA a
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

> minimize ∷ (Ord a) ⇒ FSA a → FSA a
> minimize fsa = trimUnreachables newfsa
>     where dfa = determinize fsa
>           classes = equivalenceClasses dfa
>           classOf x = (State . Set.map label . (⋃))
>                       (Set.filter (x ∈) classes)
>           init = Set.map classOf (initials dfa)
>           fin = Set.map classOf (finals dfa)
>           trans = (Set.map
>                    (\(Transition a p q) →
>                     Transition a (classOf p) (classOf q))
>                    (transitions dfa))
>           newfsa = FSA (alphabet dfa) trans init fin True

> equivalenceClasses ∷ (Ord a) ⇒ FSA a → Set.Set (Set.Set State)
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

> distinguishedPairs ∷ (Ord a) ⇒ FSA a → Set.Set (State, State)
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

> areDistinguishedByOneStep ∷ (Ord a) ⇒ FSA a → Set.Set (State, State) → State → State → Bool
> areDistinguishedByOneStep fsa knownDistinct p q
>     | makePair p q ∈ knownDistinct = True
>     | otherwise = anyS (∈ knownDistinct) newPairs
>     where destinations s x = δ fsa x (Set.singleton s)
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

> reverse ∷ (Ord a) ⇒ FSA a → FSA a
> reverse f = (FSA (alphabet f)
>              (reverseTransitions f)
>              (finals f) (initials f) False)
>     where reverseTransition (Transition x s d) = Transition x d s
>           reverseTransitions = Set.map reverseTransition . transitions

> trimFailStates ∷ (Ord a) ⇒ FSA a → FSA a
> trimFailStates = FSA.reverse . trimUnreachables . FSA.reverse

An FSA is in normal form if it has been both minimized and trimmed.

> normalize ∷ (Ord a) ⇒ FSA a → FSA a
> normalize = renameStates . trimFailStates . minimize . trimUnreachables


Determinization
================

Converting a non-deterministic FSA to a deterministic one (DFA) can
improve the speed of determining whether the language represented by
the FSA contains a string.  Further, both complexity-classification
and minimization require DFAs as input.

> metaFlip ∷ Set.Set (State) → State
> metaFlip = State . Set.map label

> powersetConstruction ∷ (Ord a) ⇒ FSA a → Set.Set State → (Set.Set State → Bool) → FSA a
> powersetConstruction f start isFinal = FSA (alphabet f) trans inits fins True
>     where inits = Set.singleton (metaFlip start)
>           buildTransition a q = (a, q, δ f a q)
>           buildTransitions' q = Set.map (\a → buildTransition a q)
>                                 (alphabet f)
>           buildTransitions = (⋃) . Set.map buildTransitions'
>           trans'' = until
>                      (\(a, b, c) → Set.size b == Set.size c)
>                      (\(a, b, c) →
>                       let d = buildTransitions (c ∖ b) in
>                       (a ∪ d, c, c ∪ Set.map (\(_, _, z) → z) d))
>                      ((∅), (∅), Set.singleton (start))
>           makeRealTransition (a, b, c) = Transition a
>                                          (metaFlip b)
>                                          (metaFlip c)
>           trans' = let (a, _, _) = trans'' in a
>           trans = Set.map makeRealTransition trans'
>           fins = Set.map metaFlip
>                  (Set.filter
>                   isFinal
>                   (Set.map (\(_, x, _) → x) trans'))


> determinize ∷ (Ord a) ⇒ FSA a → FSA a
> determinize f
>     | isDeterministic f = f
>     | otherwise = powersetConstruction f
>                   (initials f)
>                   (\s → s ∩ finals f /= (∅))


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

> generateSyntacticMonoid ∷ (Ord a) ⇒ FSA a → FSA a
> generateSyntacticMonoid d = generateSyntacticMonoid' d ((< 2) . Set.size)

> generateSyntacticMonoid' ∷ (Ord a) ⇒ FSA a → (Set.Set State → Bool) → FSA a
> generateSyntacticMonoid' d isFinal = powersetConstruction f
>                                (states f)
>                                isFinal
>     where f = normalize d

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

> isSLk ∷ (Ord a, Integral c) ⇒ FSA a → c → Bool
> isSLk synmon k
>     | k > 1 = allS (∈ synmon) (wordsOfLength (k-1) (alphabet synmon))
>     | otherwise = False

kCheck returns the smallest k for which a given FSA is SL, giving up
after 12 for no particular reason.  Or, there is a reason, and it is
that I don't do loop tests yet.

> kCheck ∷ (Ord a, Integral c) ⇒ FSA a → c
> kCheck fsa = kCheck' sm 1
>     where sm = generateSyntacticMonoid fsa

> kCheck' ∷ (Ord a, Integral c) ⇒ FSA a → c → c
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

> disallowedFactors ∷ (Ord a) ⇒ FSA a → Set.Set [Symbol a]
> disallowedFactors f = disallowedFactors' f' (∅) (kCheck f) 1
>     where f' = generateSyntacticMonoid' f (not . (== (∅)))

We will define a convenience function that takes as input a syntactic
monoid with initial and final states modified to reflect our current
search, which returns a list of disallowed factors.  This is reusable
in our search for anchored factors.

> disallowedFactors' ∷ (Ord a, Integral c) ⇒ FSA a → Set.Set [Symbol a] → c → c → Set.Set [Symbol a]
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
