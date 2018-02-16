> module Traversals where
> 
> import FSA
> import Containers
> import Data.Set (Set)
> import qualified Data.Set as Set
> 

A Path is
* a sequence of labels in inverse order of edges in the path
* the terminal state of the path
* the set of states along the path
* the length of the path (depth of the terminal state)


> data Path n e = Path [Symbol e] (Maybe (State n)) (Multiset (State n)) Int
>               deriving (Eq, Show)
> 
> endstate :: Path n e -> Maybe (State n)
> endstate (Path _ s _ _ ) = s
> 
> stateMultiset :: Path n e -> Multiset (State n)
> stateMultiset (Path _ _ ms _) = ms
> 
> labels :: Path n e -> [Symbol e]
> labels (Path ls _ _ _) = ls
> 
> word :: Path n e -> [Symbol e]
> word = Prelude.reverse . labels
> 
> depth :: Path n e -> Int
> depth (Path _ _ _ d) = d
> 

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
>           FSA n e -> Path n e -> Set (Transition n e) -> Set (Path n e)
> extend fsa p = tmap (\t ->
>                      Path
>                      (edgeLabel t : labels p)
>                      (Just (destination t))
>                      (insert (destination t) (stateMultiset p))
>                      (depth p + 1))
> 
> extensions :: (Ord e, Ord n) =>
>               FSA n e -> Path n e -> Set (Path n e)
> extensions fsa p = extend fsa p $
>                    keep ((== endstate p) . Just . source) (transitions fsa)
> 

The non-trivial extensions of a path are extensions other than self-loops


> ntExtensions :: (Ord e, Ord n) =>
>                 FSA n e -> Path n e -> Set (Path n e)
> ntExtensions fsa p = extend fsa p
>                      (keep (\t ->
>                             (Just (source t) == endstate p) &&
>                             (Just (destination t) /= endstate p)) $
>                       transitions fsa)
> 

Acyclic extensions of a path are extensions other than back-edges


> acyclicExtensions       :: (Ord e, Ord n) =>
>                            FSA n e -> Path n e -> Set (Path n e)
> acyclicExtensions fsa p = extend fsa p
>                           (keep (\t ->
>                                  (Just (source t) == endstate p) &&
>                                  (doesNotContain (destination t)
>                                   (stateMultiset p))) $
>                            transitions fsa)
> 


boundedCycExtensions are extensions other than back-edges to a state that 
has been visted more than bound times.  This gives traversals that will
follow cycles at most bound times.  Note that the qualification is that
the multiplicity of the state is $\leq$ bound; states that have not been
visited have multiplicity 0.


> boundedCycExtensions       :: (Ord e, Ord n) =>
>                            FSA n e -> Integer -> Path n e -> Set (Path n e)
> boundedCycExtensions fsa b p = extend fsa p
>                                (keep (\t ->
>                                       (Just (source t) == endstate p) &&
>                                       (b < (multiplicity 
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
> augAcExtensions fsa q p = extend fsa p
>                           (keep (\t ->
>                                  (q t) ||
>                                  ((Just (source t) == endstate p) &&
>                                   (doesNotContain (destination t)
>                                    (stateMultiset p)))) $
>                            transitions fsa)
> 

Initial open list for traversal from initial states


> initialsPaths :: (Ord e, Ord n) => FSA n e -> Set (Path n e)
> initialsPaths = tmap iPath . initials
>     where iPath s = Path [] (Just s) (singleton s) 0
> 
> truth :: a -> b -> Bool
> truth = const (const True)
> 

traversalQDFS:
* First argument is a predicate that is used to filter paths before
  adding them to the closed list
* Remaining args are the FSA, a depth bound, the open list, and
  the closed list
* Paths are not added to the open list unless their depth is <= bound


> traversalQDFS :: (Ord e, Ord n) =>
>                  (FSA n e -> Path n e -> Bool) ->
>                  FSA n e ->
>                  Int ->
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
> 

traversalDFS fsa bound open closed
= closed plus all (possibly trivial) extensions of paths in open
  that are of length <= bound


> traversalDFS :: (Ord e, Ord n) => FSA n e -> Int ->
>                 Set (Path n e) -> Set (Path n e) -> Set (Path n e)
> traversalDFS = traversalQDFS truth
> 

traversal fsa bound
initialsPaths plus all their extensions that are of length <= bound


> traversal :: (Ord e, Ord n) => FSA n e -> Int -> Set (Path n e)
> traversal fsa bound = traversalDFS fsa bound (initialsPaths fsa) empty
> 
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
> 
> acyclicPaths :: (Ord e, Ord n) => FSA n e -> Set (Path n e)
> acyclicPaths fsa = acyclicPathsQ truth fsa (initialsPaths fsa) empty
> 

acceptsDFS fsa bound
= all accepted strings of length <= bound


> acceptsDFS :: Ord n => FSA n String -> Int -> Set String
> acceptsDFS fsa bound = tmap (displaySyms . word) $
>                        traversalQDFS accepting
>                        fsa bound (initialsPaths fsa) empty
>     where accepting fsa p = contains (endstate p) . tmap Just $ finals fsa
> 

rejectsDFS fsa bound
= all rejected strings of length <= bound
  This version includes w* when the endstate of a path over word w
  has no outedges and that endstate is not final or w+ when it has
  no outedges but is final


> rejectsDFS :: Ord n => FSA n String -> Int -> Set String
> rejectsDFS fsa bound = tmap (displaySyms . word) $
>                        traversalRejects
>                        fsa bound (initialsPaths fsa) empty
> 

rejectingPaths fsa bound
= all rejecting Paths of length <= bound


> rejectingPaths :: (Ord e, Ord n) => FSA n e -> Int -> Set (Path n e)
> rejectingPaths fsa bound = traversalQDFS rejecting
>                            fsa bound (initialsPaths fsa) empty
>     where rejecting fsa p = doesNotContain (endstate p) . tmap Just $ finals fsa


Jim thinks this does not work correctly, at least with non-total FSAs.
He is not doing anything about that now.

> traversalRejects :: Ord n => FSA n String -> Int ->
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
> 

displaySyms and friends are here for now, but not for long
JR: For longer than either you or I thought.  Still here.  Still now.

> stripQuotes :: String -> String
> stripQuotes = keep (/= '"')
> 
> displaySym :: Show a => Symbol a -> String
> displaySym (Symbol x) = stripQuotes (show x)
> 
> displaySyms :: Show a => [Symbol a] -> String
> displaySyms []      = ""
> displaySyms [x]     = displaySym x
> displaySyms (x:xs)  = displaySym x ++ " " ++ displaySyms xs

