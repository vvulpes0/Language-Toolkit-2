> {-# OPTIONS_HADDOCK hide,show-extensions #-}
> {-|
> Module    : LTK.Porters.SyntacticOrder
> Copyright : (c) 2022 Dakotah Lambert
> License   : MIT
>
> This module provides a mechanism to display the syntactic order
> of a syntactic monoid.  This is an export-only format, as information
> is lost.
> -}
> module LTK.Porters.SyntacticOrder ( exportSyntacticOrder ) where

> import Data.List (intercalate, nub)
> import qualified Data.Set as Set

> import LTK.FSA
> import LTK.Algebra (SynMon, syntacticOrder)

> -- |Draw the Hasse diagram of the syntactic order of the given monoid
> -- in GraphViz @dot@ format.
> exportSyntacticOrder :: (Ord n, Ord e, Show e) => SynMon n e -> String
> exportSyntacticOrder m
>     = unlines
>       ([ "digraph {", "node [shape=box]", "edge [dir=none]" ]
>       ++ sts
>       ++ map (uncurry showtr) (reduce rel)
>       ++ ["}"]
>       )
>     where g = syntacticOrder m
>           qs = zip (map show [1::Integer ..]) . Set.toList $ states g
>           rel = [ (fst x, fst y)
>                 | x <- qs, y <- qs
>                 , x /= y
>                 , Transition { source = snd x
>                              , destination = snd y
>                              , edgeLabel = Symbol () }
>                   `elem` transitions g
>                 ]
>           sts = map
>                 (\(x,y) ->
>                  concat [ x
>                         , " [label=\""
>                         , intercalate "\x2009"
>                           (map showish $ nodeLabel y)
>                         , "\"];"]
>                 ) qs
>           showish = deescape . filter (/= '"') . show
>           showtr x y = x ++ " -> " ++ y ++ ";"

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
>              all (`notElem` ps) (map (flip (,) y) (expand x))]
>     where nodes = nub $ map fst ps ++ map snd ps
>           expand p = let n = map snd $ filter ((p ==) . fst) ps
>                      in n ++ concatMap expand n
