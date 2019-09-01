> {-# OPTIONS_HADDOCK hide,show-extensions #-}
> {-|
> Module    : LTK.Porters.Dot
> Copyright : (c) 2017-2019 Dakotah Lambert
> License   : MIT
> 
> This module provides methods to convert automata to the GraphViz
> Dot format.  At the moment, only export is supported.
> -}
> module LTK.Porters.Dot ( -- *Exporting
>                          exportDot
>                        , exportDotWithName
>                        -- *Miscellaneous
>                        , formatSet
>                        ) where

> import LTK.FSA
> import Data.Set (Set)
> import qualified Data.Set as Set

> nq :: String -> String
> nq = keep (/= '"')

> collectBy :: (Collapsible t,
>               Container (t a) a, Container (t (t a)) (t a), Eq b) =>
>              (a -> b) -> t a -> t (t a)
> collectBy f xs
>     | zsize xs   = empty
>     | otherwise  = insert firstKind . collectBy f $
>                       difference xs firstKind
>     where first      = chooseOne xs
>           firstKind  = keep ((==) (f first) . f) xs

> transitionClasses :: (Ord n, Ord e) => FSA n e -> Set (Set (Transition n e))
> transitionClasses = unionAll .
>                     tmap (collectBy destination) .
>                     collectBy source .
>                     transitions

> commaSeparateList :: (Collapsible c) => c String -> String
> commaSeparateList xs
>     | zsize xs       = ""
>     | isize xs == 1  = x
>     | otherwise      = x ++ ", " ++ commaSeparateList xs'
>     where (x, xs') = choose xs

> -- |Return value is in the range \([0 .. n]\),
> -- where \(n\) is the size of the input.
> -- A value of \(n\) indicates that the element was
> -- not in the input.
> shortLabelIn :: (Collapsible s, Eq n) => s n -> n -> Int
> shortLabelIn xs x
>     | zsize xs   = 0
>     | a == x     = 0
>     | otherwise  = 1 + shortLabelIn as x
>     where (a, as) = choose xs

> dotifyTransitionSet :: (Collapsible c, Eq e, Show e) =>
>                        c (Symbol e, Int, Int) -> String
> dotifyTransitionSet ts
>     | zsize ts   = ""
>     | otherwise  = (show src) ++ " -> " ++ (show dest) ++
>                       " [label=\"" ++ syms ++ "\"];"
>     where (_, src, dest)  = chooseOne ts
>           first (a,_,_)   = a
>           list            = collapse (:) [] ts
>           syms            = nq . commaSeparateList $
>                             tmap (sym . first) list
>           sym (Symbol a)  = deescape . nq $ show a
>           sym Epsilon     = "\x03b5" -- ε

> dotifyTransitions :: (Ord n, Ord e, Show n, Show e) => FSA n e -> [String]
> dotifyTransitions f = collapse (:) [] .
>                       tmap (dotifyTransitionSet .
>                             tmap (remakeTransition)) $
>                       transitionClasses f
>     where remakeTransition t  = ( edgeLabel t
>                                 , shortLabelIn sts (source t)
>                                 , shortLabelIn sts (destination t))
>           sts                  = states f

> dotifyInitial :: Int -> [String]
> dotifyInitial n = [fakeStart ++ " [style=\"invis\", width=\"0\", height=\"0\", label=\"\"];",
>                    fakeStart ++ " -> " ++ realStart ++ ";"]
>     where realStart  = show n
>           fakeStart  = '_' : realStart ++ "_"

> dotifyFinal :: Int -> [String]
> dotifyFinal = (:[]) . (++ " [peripheries=\"2\"];") . show

> dotifyInitials :: (Ord e, Ord n, Show n) => FSA n e -> [String]
> dotifyInitials f = unionAll .
>                    tmap (dotifyInitial .
>                          shortLabelIn (states f)) $
>                    initials f

> dotifyFinals :: (Ord e, Ord n, Show n) => FSA n e -> [String]
> dotifyFinals f = unionAll .
>                  tmap (dotifyFinal .
>                        shortLabelIn (states f)) $
>                  finals f

> dotifyStates :: (Ord e, Ord n, Show n) => FSA n e -> [String]
> dotifyStates f = collapse (:) [] $ tmap makeLabel sts
>     where sts          = states f
>           idOf         = shortLabelIn sts
>           makeLabel x  = show (idOf x) ++ " [label=\"" ++
>                          (deescape . nq . show $ nodeLabel x) ++ "\"];"

> -- |Convert an 'FSA' to its representation in the GraphViz @dot@ format.
> exportDot :: (Ord e, Ord n, Show e, Show n) => FSA n e -> String
> exportDot = exportDotWithName ""

> -- |Convert an 'FSA' to its representation in the GraphViz @dot@ format,
> -- with a provided name.
> exportDotWithName :: (Ord e, Ord n, Show e, Show n) =>
>                      String -> FSA n e -> String
> exportDotWithName name f =
>     unlines $ ["digraph " ++ name ++ " {",
>                "graph [rankdir=\"LR\"];",
>                "node  [fixedsize=\"false\", fontsize=\"12.0\", height=\"0.5\", width=\"0.5\"];",
>                "edge  [fontsize=\"12.0\", arrowsize=\"0.5\"];"] ++
>     dotifyInitials f     ++
>     dotifyStates f       ++
>     dotifyFinals f       ++
>     dotifyTransitions f  ++
>     ["}"]

> -- |Turn a 'Data.Set.Set' into a 'String':
> --
> -- >>> formatSet (fromList [1, 2, 3])
> -- "{1, 2, 3}"
> formatSet :: Show n => Set n -> String
> formatSet =  ((++ "}") . ('{' :) . commaSeparateList . tmap (nq . show) . Set.toAscList)

> deescape :: String -> String
> deescape ('\\' : '&' : xs) = deescape xs
> deescape ('\\' : x : xs)
>     | isEmpty digits = x : deescape xs
>     | otherwise      = toEnum (read digits) : deescape others
>     where (digits, others) = span (isIn "0123456789") (x:xs)
> deescape (x:xs) = x : deescape xs
> deescape _      = []
