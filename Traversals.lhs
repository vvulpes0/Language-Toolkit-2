> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : Traversals
> Copyright : (c) 2017-2018 Jim Rogers and Dakotah Lambert
> License   : BSD-style, see LICENSE
>
> Find paths through an automaton.
> -}
> module Traversals ( Path(..)
>                   , word
>                   , initialsPaths
>                   , initialsNDPath
>                   , rejectingPaths
>                   , acyclicPaths
>                   , extensions
>                   , boundedCycleExtensions
>                   , nondeterministicAcyclicExtensions
>                   ) where

> import FSA
> import Data.Monoid (Monoid(..))
> import Data.Set (Set)
> import qualified Data.Set as Set

A Path is
* a sequence of labels in inverse order of edges in the path
* the terminal state of the path
 --- This is a Maybe (State n) allowing for an adjoined identity (empty path)
     making Path a monoid wrt concatenation (append).
* the multiset of states along the path
 --- this allows us to determine how many times a state has been entered on
     the path, which is exactly the number of times a cycle starting and
     ending at that state has been traversed.
* the length of the path (depth of the terminal state)

> -- |A path through an 'FSA'.
> data Path n e = Path { -- |Edge labels are gathered in reverse order,
>                        -- so 'labels' is a reversed string.
>                        labels        :: [Symbol e]
>                        -- |Current 'State', if any.
>                      , endstate      :: (Maybe (State n))
>                        -- |States seen so far, with multiplicity.
>                      , stateMultiset :: (Multiset (State n))
>                        -- |The number of edges taken so far.
>                      , depth         :: Integer
>                      }
>               deriving (Eq, Show)
> -- |The reversal of the 'labels' of the 'Path'.
> word :: Path n e -> [Symbol e]
> word = Prelude.reverse . labels

In order to have a Multiset of Path, Path must be Ord:

> instance (Ord e, Ord n) => Ord (Path n e) where
>     p1 <= p2
>        | d1 /= d2   = d1 < d2
>        | l1 /= l2   = l1 < l2
>        | otherwise  = e1 <= e2
>        -- if l1 == l2 and e1 == e2 then state multisets are equal as well
>        where (e1, l1, d1) =
>                  (endstate p1, labels p1, depth p1)
>              (e2, l2, d2) =
>                  (endstate p2, labels p2, depth p2)

> instance (Ord n) => Monoid (Path n e) where
>     mempty = Path [] Nothing empty 0
>     mappend (Path xs1 q1 qs1 d1) (Path xs2 q2 qs2 d2)
>         = Path
>           (xs1 ++ xs2)
>           (maybe id (const . Just) q1 q2)
>           (qs1 `union` qs2)
>           (d1 + d2)

The extensions of a path p are paths extending p by a single edge

> extend :: (Ord e, Ord n) =>
>           Path n e -> Set (Transition n e) -> Set (Path n e)
> extend p = tmap (\t ->
>                      Path
>                      (edgeLabel t : labels p)
>                      (Just (destination t))
>                      (insert (destination t) (stateMultiset p))
>                      (depth p + 1))

The nondeterministic extensions of a path p are paths extending p
by a single edge nondeterminstically.  That is, the states of the
path are sets.

> nondeterministicExtend :: (Ord e, Ord n) =>
>                           Path (Set n) e -> Set (Transition n e)
>                        -> Set (Path (Set n) e)
> nondeterministicExtend p ts
>     | isEmpty ts  = singleton p
>     | otherwise   = tmap (\xs ->
>                           let label     =  chooseOne (tmap edgeLabel xs)
>                               newState  =  State .
>                                            tmap (nodeLabel . destination) $
>                                            keep (maybe
>                                                  (const False)
>                                                  (isIn . nodeLabel)
>                                                  (endstate p) .
>                                                  nodeLabel .
>                                                  source) xs
>                           in p {
>                             labels = chooseOne (tmap edgeLabel xs) : labels p
>                           , endstate = Just newState
>                           , stateMultiset = insert newState (stateMultiset p)
>                           , depth = depth p + 1
>                           }) tgroups
>     where tgroups = groupBy edgeLabel ts

> -- |Paths extending a given path by a single edge.
> extensions :: (Ord e, Ord n) =>
>               FSA n e -> Path n e -> Set (Path n e)
> extensions fsa p = extend p $
>                    keep ((== endstate p) . Just . source) (transitions fsa)

The non-trivial extensions of a path are extensions other than self-loops

> ntExtensions :: (Ord e, Ord n) =>
>                 FSA n e -> Path n e -> Set (Path n e)
> ntExtensions fsa p = extend p
>                      (keep (\t ->
>                             (Just (source t) == endstate p) &&
>                             (Just (destination t) /= endstate p)) $
>                       transitions fsa)

Acyclic extensions of a path are extensions other than back-edges

> acyclicExtensions       :: (Ord e, Ord n) =>
>                            FSA n e -> Path n e -> Set (Path n e)
> acyclicExtensions fsa p = extend p
>                           (keep (\t ->
>                                  (Just (source t) == endstate p) &&
>                                  (doesNotContain (destination t)
>                                   (stateMultiset p))) $
>                            transitions fsa)

> nondeterministicAcyclicExtensions :: (Ord e, Ord n) =>
>                                      FSA n e -> Path (Set n) e
>                                   -> Set (Path (Set n) e)
> nondeterministicAcyclicExtensions fsa p =
>     keep (\a ->
>           maybe True
>           ((<= 1) . multiplicity (stateMultiset a))
>           (endstate a)
>          ) $
>     nondeterministicExtend p (transitions fsa)

boundedCycExtensions are extensions other than back-edges to a state that
has been visted more than bound times.  This gives traversals that will
follow cycles at most bound times.  Note that the qualification is that
the multiplicity of the state is $\leq$ bound; states that have not been
visited have multiplicity 0.

> -- |Extensions other than back-edges to a state that has been visited
> -- more than a given number of times.
> boundedCycleExtensions       :: (Ord e, Ord n) =>
>                            FSA n e -> Integer -> Path n e -> Set (Path n e)
> boundedCycleExtensions fsa b p = extend p
>                                (keep (\t ->
>                                       (Just (source t) == endstate p) &&
>                                       (b >= (multiplicity
>                                             (stateMultiset p)
>                                             (destination t)))) $
>                                 transitions fsa)

Augmented acyclic extensions are extensions other than back-edges and
those that follow transitions that satisfy the predicate of the second
argument.  This is primarily for finding extensions that are acyclic
except for self-edges on singleton states, as is needed in traversing
the powerset graph in finding free forbidden factors.

> augAcExtensions :: (Ord e, Ord n) =>
>                    FSA n e ->
>                    (Transition n e -> Bool) ->
>                    Path n e ->
>                    Set (Path n e)
> augAcExtensions fsa q p = extend p
>                           (keep (\t ->
>                                  (q t) ||
>                                  ((Just (source t) == endstate p) &&
>                                   (doesNotContain (destination t)
>                                    (stateMultiset p)))) $
>                            transitions fsa)

> -- |Initial open list for traversal from initial states.
> initialsPaths :: (Ord e, Ord n) => FSA n e -> Set (Path n e)
> initialsPaths = tmap iPath . initials
>     where iPath s = Path [] (Just s) (singleton s) 0

> initialsNDPath :: (Ord e, Ord n) => FSA n e -> Path (Set n) e
> initialsNDPath fsa = Path {
>                        labels = empty
>                      , endstate = Just istate
>                      , stateMultiset = singleton istate
>                      , depth = 0
>                      }
>     where istate = State $ tmap nodeLabel (initials fsa)

> truth :: a -> b -> Bool
> truth = const (const True)

traversalQDFS:
* First argument is a predicate that is used to filter paths before
  adding them to the closed list
* Remaining args are the FSA, a depth bound, the open list, and
  the closed list
* Paths are not added to the open list unless their depth is <= bound

> traversalQDFS :: (Ord e, Ord n) =>
>                  (FSA n e -> Path n e -> Bool) ->
>                  FSA n e ->
>                  Integer ->
>                  Set (Path n e) ->
>                  Set (Path n e) ->
>                  Set (Path n e)
> traversalQDFS qf fsa bound open closed
>     | open == empty     = closed
>     | depth p >= bound  = traversalQDFS qf fsa bound ps addIf
>     | otherwise         = traversalQDFS qf fsa bound
>                           (union ps $ extensions fsa p)
>                           addIf
>     where (p, ps) = choose open
>           addIf
>               | qf fsa p   = insert p closed
>               | otherwise  = closed

traversalDFS fsa bound open closed
= closed plus all (possibly trivial) extensions of paths in open
  that are of length <= bound

> traversalDFS :: (Ord e, Ord n) => FSA n e -> Integer ->
>                 Set (Path n e) -> Set (Path n e) -> Set (Path n e)
> traversalDFS = traversalQDFS truth

traversal fsa bound
initialsPaths plus all their extensions that are of length <= bound

> traversal :: (Ord e, Ord n) => FSA n e -> Integer -> Set (Path n e)
> traversal fsa bound = traversalDFS fsa bound (initialsPaths fsa) empty

acyclicPathsQ
all paths from the initial open list that are acyclic / and are restricted to
nodes that satisfy the given predicate

> acyclicPathsQ :: (Ord e, Ord n) =>
>                  (FSA n e -> Path n e -> Bool) ->  -- predicate
>                  FSA n e ->                        -- graph
>                  Set (Path n e) ->                 -- open
>                  Set (Path n e) ->                 -- closed
>                  Set (Path n e)
> acyclicPathsQ qf fsa open closed
>     | open == empty  = closed
>     | otherwise      = acyclicPathsQ qf fsa
>                        (union ps $ acyclicExtensions fsa p)
>                        addIf
>     where (p, ps) = choose open
>           addIf
>               | qf fsa p   = insert p closed
>               | otherwise  = closed

> -- |All paths from 'initialsPaths'
> -- that do not contain cycles.
> acyclicPaths :: (Ord e, Ord n) => FSA n e -> Set (Path n e)
> acyclicPaths fsa = acyclicPathsQ truth fsa (initialsPaths fsa) empty

> nondeterministicAcyclicPathsQ :: (Ord e, Ord n) =>
>                                  (FSA n e -> Path (Set n) e -> Bool) -- predicate
>                               -> FSA n e              -- graph
>                               -> Set (Path (Set n) e) -- open
>                               -> Set (Path (Set n) e) -- closed
>                               -> Set (Path (Set n) e)
> nondeterministicAcyclicPathsQ qf fsa open closed
>     | isEmpty open = closed
>     | otherwise    = nondeterministicAcyclicPathsQ qf fsa
>                      (union ps $ nondeterministicAcyclicExtensions fsa p)
>                      addIf
>     where (p, ps) = choose open
>           addIf
>               | qf fsa p   =  insert p closed
>               | otherwise  =  closed

> nondeterministicAcyclicPaths :: (Ord e, Ord n) =>
>                                 FSA n e -> Set (Path (Set n) e)
> nondeterministicAcyclicPaths fsa = nondeterministicAcyclicPathsQ truth fsa
>                                    (singleton (initialsNDPath fsa)) empty

boundedCyclePaths
initialsPaths plus all paths that take no cycle more than bound times

boundedCyclePathsQ
all paths that take no cycle more than bound times/and are restricted to nodes
that satisfy the given predicate

> boundedCyclePathsQ :: (Ord e, Ord n) =>
>                  (FSA n e -> Path n e -> Bool) ->  -- predicate
>                  FSA n e ->                        -- graph
>                  Integer ->                        -- Bound
>                  Set (Path n e) ->                 -- open
>                  Set (Path n e) ->                 -- closed
>                  Set (Path n e)
> boundedCyclePathsQ qf fsa bnd open closed
>     | open == empty  = closed
>     | otherwise      = boundedCyclePathsQ qf fsa bnd
>                        (union ps $ boundedCycleExtensions fsa bnd p)
>                        addIf
>     where (p, ps) = choose open
>           addIf
>               | qf fsa p   = insert p closed
>               | otherwise  = closed

> boundedCyclePaths :: (Ord e, Ord n) => FSA n e -> Integer -> Set (Path n e)
> boundedCyclePaths fsa bnd =
>     boundedCyclePathsQ truth fsa bnd (initialsPaths fsa) empty

rejectingPaths fsa bound
= all rejecting Paths of length <= bound

> -- |All paths of length less than or equal to a given bound
> -- that do not end in an accepting state.
> rejectingPaths :: (Ord e, Ord n) => FSA n e -> Integer -> Set (Path n e)
> rejectingPaths fsa bound = traversalQDFS rejecting
>                            fsa bound (initialsPaths fsa) empty
>     where rejecting fsa p = doesNotContain (endstate p) . tmap Just $ finals fsa

Jim thinks this does not work correctly, at least with non-total FSAs.
He is not doing anything about that now.

> traversalRejects :: Ord n => FSA n String -> Integer ->
>                     Set (Path n String) -> Set (Path n String) ->
>                     Set (Path n String)
> traversalRejects fsa bound open closed
>     | open == empty     = closed
>     | exts == empty     = traversalRejects fsa bound ps addDead
>     | depth p >= bound  = traversalRejects fsa bound ps addLive
>     | otherwise         = traversalRejects fsa bound
>                           (union ps exts) addLive
>     where (p, ps) = choose open
>           exts = extensions fsa p
>           rejecting = doesNotContain (endstate p) . tmap Just $ finals fsa
>           addDead
>               | rejecting  = insert
>                              (Path
>                               (Symbol "*" : labels p)
>                               (endstate p)
>                               (stateMultiset p)
>                               (depth p + 1))
>                              closed
>               | otherwise  = insert
>                              (Path
>                               (Symbol "+" : labels p)
>                               (endstate p)
>                               (stateMultiset p)
>                               (depth p + 1))
>                              closed
>           addLive
>               | rejecting = insert p closed
>               | otherwise = closed
