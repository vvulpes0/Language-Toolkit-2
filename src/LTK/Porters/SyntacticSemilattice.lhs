> {-# OPTIONS_HADDOCK hide,show-extensions #-}
> {-|
> Module    : LTK.Porters.SyntacticSemilattice
> Copyright : (c) 2025 Dakotah Lambert
> License   : MIT
>
> This module provides a mechanism to display the syntactic semilattice
> of a language.  This is an export-only format, as information
> is lost.
>
> @since 1.3
> -}
> module LTK.Porters.SyntacticSemilattice
>     ( exportSyntacticSemilattice )
>     where

> import Data.List (intercalate, nub)
> import Data.Map.Lazy (Map)
> import Data.Set (Set)
> import qualified Data.Map.Lazy as Map
> import qualified Data.Set as Set

> import LTK.FSA

> exportSyntacticSemilattice :: (Ord e, Show e) =>
>                               Map (Set [e]) (Set (Set [e]))
>                            -> String
> exportSyntacticSemilattice
>     = pr . reduce . filter (uncurry (/=)) . expand . Map.assocs
>     where expand ((x,s):ys) = map ((,) x) (Set.toList s) ++ expand ys
>           expand [] = []
>           pr xs = unlines
>                   ([ "digraph {", "graph [rankdir=BT]"
>                    , "node [shape=box]", "edge [dir=none]" ]
>                    ++ sts
>                    ++ map (uncurry showtr) rel
>                    ++ ["}"]
>                   )
>               where ss = zip (map show [1::Int ..]) . Set.toList
>                          $ Set.fromList (map fst xs ++ map snd xs)
>                     rel = [ (fst x, fst y)
>                           | x <- ss, y <- ss, (snd x, snd y) `elem` xs
>                           ]
>                     sts = map
>                           (\(x,y) ->
>                            concat [ x
>                                   , " [label=\""
>                                   , showset y
>                                   , "\"];"]
>                           ) ss
>                     showset ys = '{' : showcl (Set.toList ys) ++ "}"
>                     showcl = intercalate "," . map showlist
>                     showlist = intercalate "\x2009" . map showish
>                     showish = deescape . filter (/= '"') . show
>                     showtr x y = x ++ " -> " ++ y ++ ";"

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

Compute the transitive reduction of a transitively closed acyclic graph
which is specified by source/destination pairs.
The precondition, that the graph be acyclic, is not checked.

> reduce :: (Eq a) => [(a,a)] -> [(a,a)]
> reduce ps = [(x,y) | (x,y) <- ps, all (good x y) nodes]
>     where nodes = nub $ map fst ps ++ map snd ps
>           good x y z = (x,z) `notElem` ps || y == z
>                        || (z,y) `notElem` ps
