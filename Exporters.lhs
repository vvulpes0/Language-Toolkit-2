> module Exporters where

> import LogicClasses
> import FSA
> import Data.Set (Set)
> import qualified Data.Set as Set

> nq :: String -> String
> nq = keep (/= '"')

> collectBy :: (Collapsible t,
>               Container (t a) a, Container (t (t a)) (t a), Eq b) =>
>              (a -> b) -> t a -> t (t a)
> collectBy f xs
>     | size xs == 0  = empty
>     | otherwise     = insert firstKind . collectBy f $
>                       difference xs firstKind
>     where first      = chooseOne xs
>           firstKind  = keep ((==) (f first) . f) xs

> transitionClasses :: (Ord n, Ord e) => FSA n e -> Set (Set (Transition n e))
> transitionClasses = unionAll .
>                     tmap (collectBy destination) .
>                     collectBy source .
>                     transitions

> commaSeparateList :: (Collapsible c, Show b) => c b -> String
> commaSeparateList xs
>     | size xs == 0  = ""
>     | size xs == 1  = show x
>     | otherwise     = show x ++ ", " ++ commaSeparateList xs'
>     where (x, xs') = choose xs

> dotifyTransitionSet :: (Collapsible c, Eq e, Show e) =>
>                        c (Symbol e, Int, Int) -> String
> dotifyTransitionSet ts
>     | size ts == 0  = ""
>     | otherwise     = (show src) ++ " -> " ++ (show dest) ++
>                       " [label=\"" ++ syms ++ "\"];"
>     where (_, src, dest)  = chooseOne ts
>           first (a,_,_)   = a
>           list            = collapse (:) [] ts
>           syms            = nq . commaSeparateList $
>                             tmap (sym . first) list
>           sym (Symbol a)  = a

> dotifyTransitions :: (Ord n, Ord e, Show n, Show e) => FSA n e -> [String]
> dotifyTransitions f = collapse (:) [] .
>                       tmap (dotifyTransitionSet .
>                             tmap (remakeTransition)) $
>                       transitionClasses f
>     where remakeTransition tr  = (edgeLabel tr,
>                                   findIndexInSet (source tr) sts,
>                                   findIndexInSet (destination tr) sts)
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
>                          flip findIndexInSet (states f)) $
>                    initials f

> dotifyFinals :: (Ord e, Ord n, Show n) => FSA n e -> [String]
> dotifyFinals f = unionAll .
>                  tmap (dotifyFinal .
>                        flip findIndexInSet (states f)) $
>                  finals f

> dotifyStates :: (Ord e, Ord n, Show n) => FSA n e -> [String]
> dotifyStates f = collapse (:) [] $ tmap makeLabel sts
>     where sts          = states f
>           idOf         = flip findIndexInSet sts
>           makeLabel x  = show (idOf x) ++ " [label=\"" ++
>                          (nq . show $ nodeLabel x) ++ "\"];"

> dotify :: (Ord e, Ord n, Show e, Show n) => FSA n e -> String
> dotify f = unlines $
>            ["digraph {",
>             "graph [rankdir=\"LR\"];",
>             "node  [fixedsize=\"false\", fontsize=\"12.0\"];",
>             "edge  [fontsize=\"12.0\", arrowsize=\"0.5\"];"] ++
>            dotifyInitials f     ++
>            dotifyStates f       ++
>            dotifyFinals f       ++
>            dotifyTransitions f  ++
>            ["}"]

> renameStatesFromSets :: (Ord e, Ord n, Show e, Show n) =>
>                         FSA (Set n) e -> FSA String e
> renameStatesFromSets f = FSA
>                          (alphabet f)
>                          (tmap remakeTransition $ transitions f)
>                          (tmap remakeState $ initials f)
>                          (tmap remakeState $ finals f)
>                          (isDeterministic f)
>     where remakeState         = State . (++ "}") . ('{':) .
>                                 commaSeparateList . nodeLabel
>           remakeTransition t  = Transition
>                                 (edgeLabel t)
>                                 (remakeState $ source t)
>                                 (remakeState $ destination t)
