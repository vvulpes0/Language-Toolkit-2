> {-# OPTIONS_HADDOCK show-extensions #-}
> {-# Language CPP #-}

#if !defined(MIN_VERSION_base)
# define MIN_VERSION_base(a,b,c) 0
#endif

> {-|
> Module    : Traversals
> Copyright : (c) 2017-2019 Jim Rogers and Dakotah Lambert
> License   : MIT
>
> Find paths through an automaton.
> -}
> module LTK.Traversals ( Path(..)
>                       , word
>                       , initialsPaths
>                       , initialsNDPath
>                       , rejectingPaths
>                       , acyclicPaths
>                       , extensions
>                       , boundedCycleExtensions
>                       , nondeterministicAcyclicExtensions
>                       ) where

> import LTK.FSA

#if MIN_VERSION_base(4,9,0)
The base-4.9 library from GHC 8.x added Semigroup to complement Monoid.

> import Data.Semigroup (Semigroup, (<>))

#endif

> import Data.Monoid (Monoid, mempty, mappend, mconcat)
> import Data.Set (Set)

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
>                      , endstate      :: Maybe (State n)
>                        -- |States seen so far, with multiplicity.
>                      , stateMultiset :: Multiset (State n)
>                        -- |The number of edges taken so far.
>                      , depth         :: Integer
>                      }
>               deriving (Eq, Show)

> -- |The reversal of the 'labels' of the 'Path'.
> word :: Path n e -> [Symbol e]
> word = Prelude.reverse . labels

In order to have a Multiset of Path, Path must be Ord:

> instance (Ord e, Ord n) => Ord (Path n e) where
>     compare p1 p2 = mconcat [compare d1 d2, compare l1 l2, compare e1 e2]
>        where (e1, l1, d1)  =  (endstate p1, labels p1, depth p1)
>              (e2, l2, d2)  =  (endstate p2, labels p2, depth p2)

#if MIN_VERSION_base(4,9,0)
Semigroup instance to satisfy base-4.9

> instance (Ord n) => Semigroup (Path n e) where
>     (<>) = mappend

#endif

> instance (Ord n) => Monoid (Path n e) where
>     mempty = Path [] Nothing empty 0
>     mappend (Path xs1 q1 qs1 d1) (Path xs2 q2 qs2 d2)
>         = Path { labels         =  xs1 ++ xs2
>                , endstate       =  maybe id (const . Just) q1 q2
>                , stateMultiset  =  qs1 `union` qs2
>                , depth          =  d1 + d2
>                }

The extensions of a path p are paths extending p by a single edge

> extend :: (Ord e, Ord n) =>
>           Path n e -> Set (Transition n e) -> Set (Path n e)
> extend p = tmap (\t -> Path { labels    =  (edgeLabel t : labels p)
>                             , endstate  =  (Just (destination t))
>                             , stateMultiset
>                                 = (insert (destination t) (stateMultiset p))
>                             , depth     = (depth p + 1)
>                             })

The nondeterministic extensions of a path p are paths extending p
by a single edge nondeterminstically.  That is, the states of the
path are sets.

> nondeterministicExtend :: (Ord e, Ord n) =>
>                           Path (Set n) e -> Set (Transition n e) ->
>                           Set (Path (Set n) e)
> nondeterministicExtend p ts
>     | isEmpty ts = singleton p
>     | otherwise
>         = tmap (\xs ->
>                 let newState  =  State $ collapse f empty xs
>                 in p { labels         =  chooseOne (tmap edgeLabel xs) :
>                                          labels p
>                      , endstate       =  Just newState
>                      , stateMultiset  =  insert newState (stateMultiset p)
>                      , depth          =  depth p + 1
>                      }) tgroups
>     where tgroups      =  partitionBy edgeLabel ts
>           connectable  =  maybe (const False) (isIn . nodeLabel) (endstate p)
>           f x          =  if connectable . nodeLabel $ source x
>                           then insert (nodeLabel $ destination x)
>                           else id

> -- |Paths extending a given path by a single edge.
> extensions :: (Ord e, Ord n) =>
>               FSA n e -> Path n e -> Set (Path n e)
> extensions fsa p = extend p .
>                    keep ((== endstate p) . Just . source) $ transitions fsa

Acyclic extensions of a path are extensions other than back-edges

> acyclicExtensions :: (Ord e, Ord n) => FSA n e -> Path n e -> Set (Path n e)
> acyclicExtensions fsa p = extend p .
>                           keep (both
>                                 (isNotIn (stateMultiset p) . destination)
>                                 ((== endstate p) . Just . source)) $
>                           transitions fsa

> -- |The extensions of a non-deterministic path other than back-edges
> nondeterministicAcyclicExtensions :: (Ord e, Ord n) =>
>                                      FSA n e -> Path (Set n) e ->
>                                      Set (Path (Set n) e)
> nondeterministicAcyclicExtensions fsa
>     = keep
>       (\a ->
>        maybe True ((<= 1) . multiplicity (stateMultiset a)) (endstate a)
>       ) . flip nondeterministicExtend (transitions fsa)

boundedCycExtensions are extensions other than back-edges to a state that
has been visted more than bound times.  This gives traversals that will
follow cycles at most bound times.  Note that the qualification is that
the multiplicity of the state is $\leq$ bound; states that have not been
visited have multiplicity 0.

> -- |Extensions other than back-edges to a state that has been visited
> -- more than a given number of times.
> boundedCycleExtensions :: (Ord e, Ord n) =>
>                           FSA n e -> Integer -> Path n e -> Set (Path n e)
> boundedCycleExtensions fsa b p
>     = extend p .
>       keep (both
>             ((== endstate p) . Just . source)
>             ((<= b) . multiplicity (stateMultiset p) . destination)) $
>       transitions fsa

> -- |Initial open list for traversal from initial states.
> initialsPaths :: (Ord e, Ord n) => FSA n e -> Set (Path n e)
> initialsPaths = tmap iPath . initials
>     where iPath s = Path [] (Just s) (singleton s) 0

> -- |Initial open list for non-deterministic traversal from initial states.
> initialsNDPath :: (Ord e, Ord n) => FSA n e -> Path (Set n) e
> initialsNDPath fsa = Path { labels = empty
>                           , endstate = Just istate
>                           , stateMultiset = singleton istate
>                           , depth = 0
>                           }
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
>     | isEmpty open     =  closed
>     | depth p > bound  =  traversalQDFS qf fsa bound ps addIf
>     | otherwise        =  traversalQDFS qf fsa bound
>                           (union ps $ extensions fsa p)
>                           addIf
>     where (p, ps) = choose open
>           addIf
>               | qf fsa p   =  insert p closed
>               | otherwise  =  closed

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
>     | open == empty  =  closed
>     | otherwise      =  acyclicPathsQ qf fsa
>                         (union ps $ acyclicExtensions fsa p)
>                         addIf
>     where (p, ps) = choose open
>           addIf
>               | qf fsa p   =  insert p closed
>               | otherwise  =  closed

> -- |All paths from 'initialsPaths' that do not contain cycles.
> acyclicPaths :: (Ord e, Ord n) => FSA n e -> Set (Path n e)
> acyclicPaths fsa = acyclicPathsQ truth fsa (initialsPaths fsa) empty

rejectingPaths fsa bound
= all rejecting Paths of length <= bound

> -- |All paths of length less than or equal to a given bound
> -- that do not end in an accepting state.
> rejectingPaths :: (Ord e, Ord n) => FSA n e -> Integer -> Set (Path n e)
> rejectingPaths fsa bound = traversalQDFS rejecting
>                            fsa bound (initialsPaths fsa) empty
>     where rejecting f p = doesNotContain (endstate p) . tmap Just $ finals f
