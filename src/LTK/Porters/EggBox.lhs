> {-# OPTIONS_HADDOCK hide,show-extensions #-}
> {-|
> Module    : LTK.Porters.EggBox
> Copyright : (c) 2022-2023 Dakotah Lambert
> License   : MIT
>
> This module provides a mechanism to display the egg-box representation
> for a syntactic monoid.  This is an export-only format, as information
> is lost.
> -}
> module LTK.Porters.EggBox ( exportEggBox ) where

> import Data.List (intercalate, nub)
> import Data.Maybe (mapMaybe)
> import Data.Set (Set)
> import qualified Data.Set as Set

> import LTK.FSA
> import LTK.Algebra (SynMon, idempotents)

> -- |Draw the egg-box representation of the given monoid
> -- in GraphViz @dot@ format.
> exportEggBox :: (Ord n, Ord e, Show e) => SynMon n e -> String
> exportEggBox m
>     = unlines
>       ([ "digraph {", "node [shape=plaintext]", "edge [dir=none]" ]
>       ++ sts
>       ++ map (uncurry showtr) (reduce g)
>       ++ ["}"]
>       )
>     where js = zip (map show [1::Integer ..]) . Set.toList
>                $ jEquivalence m
>           sts = map
>                 (\(x,y) -> x ++ "[label=<"
>                           ++ constructTable m y ++ ">];")
>                 js
>           ps = pairs js
>           g = mapMaybe (uncurry f) ps
>           f x y
>               | x2 `Set.isSubsetOf` y2 = Just (fst y, fst x)
>               | y2 `Set.isSubsetOf` x2 = Just (fst x, fst y)
>               | otherwise = Nothing
>               where x2 = primitiveIdeal2 m (Set.findMin $ snd x)
>                     y2 = primitiveIdeal2 m (Set.findMin $ snd y)
>           showtr x y = x ++ " -> " ++ y ++ ";"

> pairs :: [a] -> [(a,a)]
> pairs (x:xs) = map ((,) x) xs ++ pairs xs
> pairs _ = []

> constructTable :: (Ord n, Ord e, Show e) =>
>                  SynMon n e -> Set (State ([Maybe n], [Symbol e]))
>                -> String
> constructTable m j
>     = unlines ([ "<TABLE " ++ unwords attrs ++ ">"]
>               ++ concatMap (lines . constructRow m) rs
>               ++  [ "</TABLE>" ])
>     where rs = Set.toList $ partitionBy (primitiveIdealR m) j
>           attrs = [ "BORDER=\"0\""
>                   , "CELLBORDER=\"1\""
>                   , "CELLSPACING=\"0\""
>                   ]

A row is an R-class.  But a column is an L-class,
so we have to make certain that the cells are generated
in a consistent order.

> constructRow :: (Ord n, Ord e, Show e) =>
>                SynMon n e -> Set (State ([Maybe n], [Symbol e]))
>              -> String
> constructRow m r
>     = unlines (["<TR>"]
>                ++ map (constructCell m) ls
>                ++ ["</TR>"])
>     where ls = map (Set.map snd) . Set.toAscList $ partitionBy fst ls'
>           ls' = Set.map (\x -> (primitiveIdealL m x, x)) r

A cell is an H-class.  Idempotent elements are marked by a star.
The most intensive part of `constructCell` is one of design principle:
I want to visually see if identity is reachable in a star-free system.
If there is a nonsalient symbol, that symbol is used for identity.
Otherwise, we use □ symbol.

> constructCell :: (Ord n, Ord e, Show e) =>
>                SynMon n e -> Set (State ([Maybe n], [Symbol e]))
>              -> String
> constructCell m h = "<TD>" ++ intercalate "<BR/>" h' ++ "</TD>"
>     where h' = map (display . snd . nodeLabel) $ Set.toList h
>           display x
>               | not (null x) = intercalate "\x2009"
>                                (mapMaybe (toMaybe . fmap showish) x)
>                                ++ if x `Set.member` i then "*" else ""
>               | otherwise = (case t of
>                                ((Symbol n):_) -> showish n
>                                _ -> "□") ++ "*"
>               where t = map edgeLabel
>                         . filter ((/= Epsilon) . edgeLabel)
>                         . filter ((`Set.member` initials m)
>                                   . destination)
>                         . filter ((`Set.member` initials m) . source)
>                         . Set.toList $ transitions m
>                     toMaybe (Symbol a) = Just a
>                     toMaybe _ = Nothing
>           showish x = deescape . filter (/= '"') $ show x
>           i = Set.map (snd . nodeLabel)
>               (initials m `Set.union` idempotents m)

If you show a string, quotes and some other symbols get escaped.
Undo that.  A better approach would be to not use Show to begin with,
but that makes the system less generic, so we accept the burden.

> deescape :: String -> String
> deescape ('\\' : '&' : xs) = deescape xs
> deescape ('\\' : x : xs)
>     | isEmpty digits = x : deescape xs
>     | otherwise      = toEnum (read digits) : deescape others
>     where (digits, others) = span (isIn "0123456789") (x:xs)
> deescape (x:xs) = x : deescape xs
> deescape _      = []

Compute the transitive reduction of an acyclic graph
which is specified by source/destination pairs.
The precondition, that the graph be acyclic, is not checked.

> reduce :: (Eq a) => [(a,a)] -> [(a,a)]
> reduce ps = [(x,y) | x <- nodes, y <- nodes, y `elem` expand x,
>              all ((`notElem` ps) . flip (,) y) $ expand x]
>     where nodes = nub $ map fst ps ++ map snd ps
>           expand p = let n = map snd $ filter ((p ==) . fst) ps
>                      in n ++ concatMap expand n
