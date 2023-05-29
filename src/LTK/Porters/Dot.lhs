> {-# OPTIONS_HADDOCK hide,show-extensions #-}
> {-|
> Module    : LTK.Porters.Dot
> Copyright : (c) 2017-2019,2023 Dakotah Lambert
> License   : MIT
> 
> This module provides methods to convert automata to the GraphViz
> Dot format.  At the moment, only export is supported.
> -}
> module LTK.Porters.Dot
>        ( -- *Exporting
>          exportDot
>        , exportDotWithName
>        -- *Miscellaneous
>        , formatSet
>        ) where

> import Data.List (intercalate)
> import Data.Set (Set)
> import qualified Data.Set as Set

> import LTK.FSA

> showish :: (Show a) => a -> String
> showish = filter (/= '"') . show

> transitionClasses :: (Ord n, Ord e) => FSA n e -> Set (Set (Transition n e))
> transitionClasses = refinePartitionBy destination . partitionBy source .
>                     transitions

> -- |Return value is in the range \([0 .. n]\),
> -- where \(n\) is the size of the input.
> -- A value of \(n\) indicates that the element was
> -- not in the input.
> shortLabelIn :: (Collapsible s, Eq n) => s n -> n -> Int
> shortLabelIn xs x = collapse (\y a -> if y == x then 0 else 1 + a) 0 xs

> dotifyTransitionSet :: (Collapsible c, Eq e, Show e) =>
>                        c (Symbol e, Int, Int) -> String
> dotifyTransitionSet ts
>     | zsize ts   = ""
>     | otherwise  = show src ++ " -> " ++ show dest
>                    ++ " [label=\"" ++ syms ++ "\"];"
>     where (_, src, dest)  = chooseOne ts
>           first (a,_,_)   = a
>           list            = collapse (:) [] ts
>           syms            = intercalate ", " $ map (sym . first) list
>           sym (Symbol a)  = deescape $ showish a
>           sym Epsilon     = "\x03B5" -- ε

> dotifyTransitions :: (Ord n, Ord e, Show n, Show e) => FSA n e -> [String]
> dotifyTransitions f = collapse (:) [] .
>                       tmap
>                       (dotifyTransitionSet .
>                        tmap remakeTransition
>                       ) $ transitionClasses f
>     where remakeTransition t
>               = ( edgeLabel t
>                 , shortLabelIn sts (source t)
>                 , shortLabelIn sts (destination t)
>                 )
>           sts = states f

> dotifyInitial :: Int -> [String]
> dotifyInitial n
>     = [ fakeStart ++
>         " [style=\"invis\", width=\"0\", height=\"0\", label=\"\"];"
>       , fakeStart ++ " -> " ++ realStart ++ ";"
>       ]
>     where realStart  =  show n
>           fakeStart  =  '_' : realStart ++ "_"

> dotifyFinal :: Int -> [String]
> dotifyFinal = (:[]) . (++ " [peripheries=\"2\"];") . show

> dotifyInitials :: (Ord e, Ord n, Show n) => FSA n e -> [String]
> dotifyInitials f = collapse
>                    (union . dotifyInitial . shortLabelIn (states f))
>                    empty $
>                    initials f

> dotifyFinals :: (Ord e, Ord n, Show n) => FSA n e -> [String]
> dotifyFinals f = collapse
>                  (union . dotifyFinal . shortLabelIn (states f))
>                  empty $
>                  finals f

> dotifyStates :: (Ord e, Ord n, Show n) => FSA n e -> [String]
> dotifyStates f = map makeLabel $ fromCollapsible sts
>     where sts          = states f
>           idOf         = shortLabelIn sts
>           makeLabel x  = show (idOf x) ++ " [label=\"" ++
>                          (deescape . showish $ nodeLabel x) ++ "\"];"

> -- |Convert an 'FSA' to its representation in the GraphViz @dot@ format.
> exportDot :: (Ord e, Ord n, Show e, Show n) => FSA n e -> String
> exportDot = exportDotWithName ""

> -- |Convert an 'FSA' to its representation in the GraphViz @dot@ format,
> -- with a provided name.
> exportDotWithName :: (Ord e, Ord n, Show e, Show n) =>
>                      String -> FSA n e -> String
> exportDotWithName name f
>     = unlines $
>       [ "digraph " ++ name ++ " {"
>       , "graph [rankdir=\"LR\"];"
>       , "node  [fixedsize=\"false\", fontsize=\"12.0\", " ++
>             "height=\"0.5\", width=\"0.5\"];"
>       , "edge  [fontsize=\"12.0\", arrowsize=\"0.5\"];"
>       ] ++
>       dotifyInitials f     ++
>       dotifyStates f       ++
>       dotifyFinals f       ++
>       dotifyTransitions f  ++
>       ["}"]

> -- |Turn a 'Data.Set.Set' into a 'String':
> --
> -- >>> formatSet (fromList [1, 2, 3])
> -- "{1, 2, 3}"
> formatSet :: Show n => Set n -> String
> formatSet =  (++ "}") . ('{' :) . intercalate ", " . map showish .
>              Set.toAscList

> deescape :: String -> String
> deescape ('\\' : '&' : xs) = deescape xs
> deescape ('\\' : x : xs)
>     | isEmpty digits = x : deescape xs
>     | otherwise      = toEnum (read digits) : deescape others
>     where (digits, others) = span (isIn "0123456789") (x:xs)
> deescape (x:xs) = x : deescape xs
> deescape _      = []
