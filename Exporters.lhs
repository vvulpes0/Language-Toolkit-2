> module Exporters (
>                   dotify,
>                   dotifyWithName,
>                   exportJeff,
>                   renameStatesFromSets,
>                   untransliterate,
>                   untransliterateString
>                  ) where
> 
> import Containers
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
> dotify = dotifyWithName ""

> dotifyWithName :: (Ord e, Ord n, Show e, Show n) => String -> FSA n e -> String
> dotifyWithName name f =
>     unlines $ ["digraph " ++ name ++ " {",
>                "graph [rankdir=\"LR\"];",
>                "node  [fixedsize=\"false\", fontsize=\"12.0\", height=\"0.5\", width=\"0.5\"];",
>                "edge  [fontsize=\"12.0\", arrowsize=\"0.5\"];"] ++
>     dotifyInitials f     ++
>     dotifyStates f       ++
>     dotifyFinals f       ++
>     dotifyTransitions f  ++
>     ["}"]

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

> exportJeff :: (Ord e, Ord n, Show e) => FSA n e -> String
> exportJeff f = unlines (inits : trans ++ [fins])
>     where list = filter (/= ' ') . commaSeparateList . tmap nodeLabel
>           fins = list (finals f')
>           inits = list (initials f') ++ "!"
>           trans = bangTerminate . Set.toAscList .
>                   tmap exportJeffTransition $ transitions f'
>           f' = normalize f

> bangTerminate :: [String] -> [String]
> bangTerminate [] = []
> bangTerminate (x:[]) = [x ++ "!"]
> bangTerminate (x:xs) = x : bangTerminate xs

> exportJeffTransition :: (Show e, Show n) => Transition n e -> String
> exportJeffTransition t = nl (source t) ++ "," ++
>                          nl (destination t) ++ "," ++
>                          el (edgeLabel t)
>     where nl = nq . show . nodeLabel
>           el (Symbol a) = nq $ show a
>           el Epsilon    = "\x03B5"

> untransliterate :: (Ord n) => FSA n String -> FSA n String
> untransliterate f = FSA (tmap (fmap untransliterateString) (alphabet f))
>                     (tmap untransliterateTransition (transitions f))
>                     (initials f) (finals f) (isDeterministic f)

> untransliterateTransition :: Transition n String -> Transition n String
> untransliterateTransition t = Transition
>                               (untransliterateString `fmap` edgeLabel t)
>                               (source t)
>                               (destination t)

> untransliterateString :: String -> String
> untransliterateString ('L':xs) = "w0." ++ untransliterateStress xs
> untransliterateString ('H':xs) = "w1." ++ untransliterateStress xs
> untransliterateString ('S':xs) = "w2." ++ untransliterateStress xs
> untransliterateString ('X':xs) = "w3." ++ untransliterateStress xs
> untransliterateString ('Y':xs) = "w4." ++ untransliterateStress xs
> untransliterateString xs       = xs

> untransliterateStress :: String -> String
> untransliterateStress [] = "s0"
> untransliterateStress "`" = "s1"
> untransliterateStress "'" = "s2"
> untransliterateStress xs  = xs
