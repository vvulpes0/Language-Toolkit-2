> module Traversals where

> import FSA
> import LogicClasses
> import Data.Set (Set)
> import qualified Data.Set as Set

A Path is
* a sequence of labels in inverse order of edges in the path
* the terminal state of the path
* the set of states along the path
* the length of the path (depth of the terminal state)

> data Path a = Path [Symbol a] State (Set State) Int
>               deriving (Eq, Show)

> endstate :: Path a -> State
> endstate (Path _ s _ _ ) = s

> stateset :: Path a -> Set State
> stateset (Path _ _ ss _) = ss

> labels :: Path a -> [Symbol a]
> labels (Path ls _ _ _) = ls

> word :: Path a -> [Symbol a]
> word = Prelude.reverse . labels

> depth :: Path a -> Int
> depth (Path _ _ _ d) = d

In order to have a Set of Path, Path must be Ord:

> instance Ord a => Ord (Path a) where
>     p1 <= p2
>        | d1 /= d2   = d1 < d2
>        | l1 /= l2   = l1 < l2
>        | otherwise  = e1 <= e2
>        -- if l1 == l2 and e1 == e2 then statesets are equal as well
>        where (e1, l1, d1) =
>                  (endstate p1, labels p1, depth p1)
>              (e2, l2, d2) =
>                  (endstate p2, labels p2, depth p2)

The extensions of a path p are paths extending p by a single edge

> extend :: Ord a => FSA a -> Path a -> Set (Transition a) -> Set (Path a)
> extend fsa p = tmap (\t ->
>                      Path
>                      (edgeLabel t : labels p)
>                      (destination t)
>                      (insert (destination t) (stateset p))
>                      (depth p + 1))

> extensions :: Ord a => FSA a -> Path a -> Set (Path a)
> extensions fsa p = extend fsa p $
>                    keep ((== endstate p) . source) (transitions fsa)

The non-trivial extensions of a path are extensions other than self-loops

> ntExtensions :: Ord a => FSA a -> Path a -> Set (Path a)
> ntExtensions fsa p = extend fsa p
>                      (keep (\t ->
>                             (source t == endstate p) &&
>                             (destination t /= endstate p)) $
>                       transitions fsa)

Acyclic extensions of a path are extensions other than back-edges

> acyclicExtensions :: Ord a => FSA a -> Path a -> Set (Path a)
> acyclicExtensions fsa p = extend fsa p
>                           (keep (\t ->
>                                  (source t == endstate p) &&
>                                  (doesNotContain (destination t)
>                                   (stateset p))) $
>                            transitions fsa)

Augmented acyclic extensions are extensions other than back-edges and
those that follow transitions that satisfy the predicate of the second
argument.  This is primarily for finding extensions that are acyclic
except for self-edges on singleton states, as is needed in traversing
the powerset graph in finding free forbidden factors.

> augAcExtensions :: Ord a =>
>                    FSA a ->
>                    (Transition a -> Bool) ->
>                    Path a ->
>                    Set (Path a)
> augAcExtensions fsa q p = extend fsa p
>                           (keep (\t ->
>                                  (q t) ||
>                                  ((source t == endstate p) &&
>                                   (doesNotContain (destination t)
>                                    (stateset p)))) $
>                            transitions fsa)

Initial open list for traversal from initial states

> initialsPaths :: Ord a => FSA a -> Set (Path a)
> initialsPaths = tmap iPath . initials
>     where iPath s = Path [] s (singleton s) 0

> truth :: a -> b -> Bool
> truth = const (const True)

traversalQDFS:
* First argument is a predicate that is used to filter paths before
  adding them to the closed list
* Remaining args are the FSA, a depth bound, the open list, and
  the closed list
* Paths are not added to the open list unless their depth is <= bound

> traversalQDFS :: Ord a =>
>                  (FSA a -> Path a -> Bool) ->
>                  FSA a ->
>                  Int ->
>                  Set (Path a) ->
>                  Set (Path a) ->
>                  Set (Path a)
> traversalQDFS qf fsa bound open closed
>     | open == empty     = closed
>     | depth p >= bound  = traversalQDFS qf fsa bound ps addIf
>     | otherwise         = traversalQDFS qf fsa bound
>                           (union ps $ extensions fsa p)
>                           addIf
>     where (p, ps) = Set.deleteFindMin open
>           addIf
>               | qf fsa p   = insert p closed
>               | otherwise  = closed

traversalDFS fsa bound open closed
= closed plus all (possibly trivial) extensions of paths in open
  that are of length <= bound

> traversalDFS :: Ord a => FSA a -> Int ->
>                 Set (Path a) -> Set (Path a) -> Set (Path a)
> traversalDFS = traversalQDFS truth

traversal fsa bound
initialsPaths plus all their extensions that are of length <= bound

> traversal :: Ord a => FSA a -> Int -> Set (Path a)
> traversal fsa bound = traversalDFS fsa bound (initialsPaths fsa) empty

> acyclicPathsQ :: Ord a =>
>                  (FSA a -> Path a -> Bool) ->  -- predicate
>                  FSA a ->                      -- graph
>                  Set (Path a) ->               -- open
>                  Set (Path a) ->               -- closed
>                  Set (Path a)
> acyclicPathsQ qf fsa open closed
>     | open == empty  = closed
>     | otherwise      = acyclicPathsQ qf fsa
>                        (union ps $ acyclicExtensions fsa p)
>                        addIf
>     where (p, ps) = Set.deleteFindMin open
>           addIf
>               | qf fsa p   = insert p closed
>               | otherwise  = closed

> acyclicPaths :: Ord a => FSA a -> Set (Path a)
> acyclicPaths fsa = acyclicPathsQ truth fsa (initialsPaths fsa) empty

acceptsDFS fsa bound
= all accepted strings of length <= bound

> acceptsDFS :: FSA String -> Int -> Set String
> acceptsDFS fsa bound = tmap (displaySyms . word) $
>                        traversalQDFS accepting
>                        fsa bound (initialsPaths fsa) empty
>     where accepting fsa p = contains (endstate p) $ finals fsa

rejectsDFS fsa bound
= all rejected strings of length <= bound
  This version includes w* when the endstate of a path over word w
  has no outedges and that endstate is not final or w+ when it has
  no outedges but is final

> rejectsDFS :: FSA String -> Int -> Set String
> rejectsDFS fsa bound = tmap (displaySyms . word) $
>                        traversalRejects
>                        fsa bound (initialsPaths fsa) empty

rejectingPaths fsa bound
= all rejecting Paths of length <= bound

> rejectingPaths :: Ord a => FSA a -> Int -> Set (Path a)
> rejectingPaths fsa bound = traversalQDFS rejecting
>                            fsa bound (initialsPaths fsa) empty
>     where rejecting fsa p = doesNotContain (endstate p) $ finals fsa

> traversalRejects :: FSA String -> Int ->
>                     Set (Path String) -> Set (Path String) ->
>                     Set (Path String)
> traversalRejects fsa bound open closed
>     | open == empty     = closed
>     | exts == empty     = traversalRejects fsa bound ps addDead
>     | depth p >= bound  = traversalRejects fsa bound ps addLive
>     | otherwise         = traversalRejects fsa bound
>                           (union ps exts) addLive
>     where (p, ps) = Set.deleteFindMin open
>           exts = extensions fsa p
>           rejecting = doesNotContain (endstate p) $ finals fsa
>           addDead
>               | rejecting  = insert
>                              (Path
>                               (Symbol "*" : labels p)
>                               (endstate p)
>                               (stateset p)
>                               (depth p + 1))
>                              closed
>               | otherwise  = insert
>                              (Path
>                               (Symbol "+" : labels p)
>                               (endstate p)
>                               (stateset p)
>                               (depth p + 1))
>                              closed
>           addLive
>               | rejecting = insert p closed
>               | otherwise = closed

displaySyms and friends are here for now, but not for long

> stripQuotes :: String -> String
> stripQuotes = keep (/= '"')

> displaySym :: Show a => Symbol a -> String
> displaySym (Symbol x) = stripQuotes (show x)

> displaySyms :: Show a => [Symbol a] -> String
> displaySyms []      = ""
> displaySyms [x]     = displaySym x
> displaySyms (x:xs)  = displaySym x ++ " " ++ displaySyms xs
