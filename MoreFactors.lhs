\documentclass[12pt,twoside]{article}

\usepackage[letterpaper,margin=1in]{geometry}
\usepackage[T1]{fontenc}
\usepackage[english]{babel}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{amsthm}
\usepackage{draftnote}\draftcp
\usepackage{ec-phonology}
\usepackage{mathtools}
\usepackage{microtype}

\input litHaskellcode

\author{JRogers}
\title{MoreFactors}
\date{}

\begin{document}

\maketitle\thispagestyle{empty}
Some stuff from \texttt{Factors.hs} and \texttt{Work.hs}


> module MoreFactors where
> 
> import LogicClasses hiding (singleton)
> import FSA
> import Data.Set (Set)
> import qualified Data.Set as Set
> import qualified Data.List as List
> import Factors
> 
> l = Symbol "L" -- light
> l0 = w0s0 -- Symbol "L0" -- unstressed
> l1 = w0s1 -- Symbol "L1" -- _secondary_ stress
> l2 = w0s2 -- Symbol "L2" -- _primary_ stress
> h = Symbol "H" -- heavy
> h0 = w1s0 -- Symbol "H0" -- unstressed
> h1 = w1s1 -- Symbol "H1" -- _secondary_ stress
> h2 = w1s2 -- Symbol "H2" -- _primary_ stress
> s = Symbol "S" -- superheavy
> s0 = w2s0 -- Symbol "S0" -- unstressed
> s1 = w2s1 -- Symbol "S1" -- _secondary_ stress
> s2 = w2s2 -- Symbol "S2" -- _primary_ stress
> x0 = w3s0 -- Symbol "X0" -- weight 3 (Dutch and Piraha)
> x1 = w3s1 -- Symbol "X1" -- _secondary_ stress
> x2 = w3s2 -- Symbol "X2" -- _primary_ stress
> y0 = w4s0 -- Symbol "Y0" -- weight 4 (Piraha)
> y1 = w4s1 -- Symbol "Y1" -- _secondary_ stress
> y2 = w4s2 -- Symbol "Y2" -- _primary_ stress
> 
> -- This does not include the symbols that do not bear stress categories
> defaultAlphabet = unionAll [w0, w1, w2, w3, w4]


toWord converts a string of symbol types (i.e., set of symbol) to a set of
strings of symbol. 

> toWord :: (Ord b) => [Set (Symbol b)] -> Set [Symbol b]
> toWord [] = Set.empty
> toWord (syms:symsl)
>     | (null symsl) = Set.map (:[])  syms
>     | otherwise = nurbsingl syms (toWord symsl)
>     where
>       nurbsingl :: (Ord b) => Set (Symbol b) -> Set [Symbol b] -> Set [Symbol b]
>       nurbsingl syms wrds
>           | (null syms) = Set.empty
>           | otherwise = Set.foldr (glom wrds) Set.empty syms
>           where
>             glom :: (Ord b) => Set [(Symbol b)] -> (Symbol b) ->
>                                          Set [Symbol b] -> Set [Symbol b]
>             glom wrds sym partial = Set.union (nurb1l sym wrds) partial
>             nurb1l :: (Ord b) => (Symbol b) -> Set [Symbol b] -> Set[Symbol b]
>             nurb1l sym wrds = Set.map ((:) sym) wrds


Sigma^{*} and Sigma^{+} included here because I didn't take the time to find
          them in FSA.lhs

> allWithAlphabet :: (Ord a, Integral b) => Set.Set (Symbol a) -> FSA b a
> allWithAlphabet as = FSA as
>                      (Set.map (selfEdge) as)
>                      (Set.singleton (State 0))
>                      (Set.singleton (State 0)) True
>     where selfEdge sym = Transition sym (State 0) (State 0)
> 
> sigmaStar = allWithAlphabet defaultAlphabet
> 
> posWithAlphabet :: (Ord a, Integral b) => Set.Set (Symbol a) -> FSA b a
> posWithAlphabet as = FSA as
>                      (Set.union (Set.map (makeEdge 0 1) as)
>                                 (Set.map (makeEdge 1 1) as))
>                      (Set.singleton (State 0))
>                      (Set.singleton (State 1)) True
>     where makeEdge from to sym = Transition sym (State from) (State to)
> 
> sigmaPlus = posWithAlphabet defaultAlphabet
> 
> eps :: (Ord e, Enum n, Ord n, Num n) => FSA n e
> eps = singletonLanguage []
> 
> epsWithAlphabet :: (Ord e, Enum n, Ord n, Num n) => Set.Set (Symbol e) -> FSA n e
> epsWithAlphabet alph = singletonWithAlphabet alph []
> 
> -- temporary fix for type ambiguity issues in buildFSAs
> singIntWithAlphabet :: Set.Set(Symbol String) -> [(Symbol String)]-> FSA Int String
> singIntWithAlphabet as = singletonWithAlphabet as
> 
> singInt :: [(Symbol String)] -> FSA Int String
> singInt = singletonLanguage
> 
> -- Just trying to suit, Dakotah
> mortify :: [Symbol String] -> [Set.Set (Symbol String)]
> mortify str = List.map Set.singleton str
> 


Factors

These are currently constructed directly as singletons with \Sigma^* prepended,
appended or both.  The result is non-deterministic.  Prefferably they should
be built using a suffix function, which will yield a DFA without the
determinization step.


> factor :: [Symbol String] -> FSA Int String
> factor wrd = local True defaultAlphabet (mortify wrd)
> -- factor syms = factorWithAlphabet (Set.fromList syms) syms
> 
> factorWithAlphabet :: Set.Set (Symbol String) -> [Symbol String] -> FSA Int String
> factorWithAlphabet as wrd = local True as (mortify wrd)
> 
> -- factorWithAlphabet as syms = 
> --     FSA as trans (initials single) (finals single) False
> --         where single = singInt syms
> --               start = Set.findMin (initials single)
> --               final = Set.findMin (finals single)
> --               trans = (transitions single) `union` initialLoop `union` finalLoop
> --               initialLoop = 
> --                   Set.map (\a -> Transition a start start) as
> --               finalLoop = 
> --                   Set.map (\a -> Transition a final final) as
> 
> initialfactor :: [Symbol String] -> FSA Int String
> initialfactor wrd = initialLocal True defaultAlphabet (mortify wrd)
> -- initialfactor syms = initialfactorWithAlphabet (Set.fromList syms) syms
> 
> initialfactorWithAlphabet :: Set.Set(Symbol String) -> [Symbol String] -> FSA Int String
> initialfactorWithAlphabet as wrd = initialLocal True as (mortify wrd)
> -- initialfactorWithAlphabet as syms = 
> --     FSA as trans (initials single) (finals single) False
> --         where single = singInt syms
> --               start = Set.findMin (initials single)
> --               final = Set.findMin (finals single)
> --               trans = (transitions single) `union` finalLoop
> --               finalLoop = 
> --                   Set.map (\a -> Transition a final final) as
> 
> finalfactor :: [Symbol String] -> FSA Int String
> finalfactor wrd = finalLocal True defaultAlphabet (mortify wrd)
> -- finalfactor syms = finalfactorWithAlphabet (Set.fromList syms) syms
> 
> finalfactorWithAlphabet :: Set.Set(Symbol String) -> [Symbol String] -> FSA Int String
> finalfactorWithAlphabet as wrd = finalLocal True as (mortify wrd)
> -- finalfactorWithAlphabet as syms = 
> --     FSA as trans (initials single) (finals single) False
> --         where single = singInt syms
> --               start = Set.findMin (initials single)
> --               final = Set.findMin (finals single)
> --               trans = (transitions single) `union` initialLoop
> --               initialLoop = 
> --                   Set.map (\a -> Transition a start start) as
> 


Flat intersection (Dakotah probably already has this)

(How do invoke Container intersection for FSAs here?)

> flatIntersection :: (Ord a, Ord b, Ord c, Integral d) =>
>                        FSA b a -> FSA c a -> FSA d a
> flatIntersection f1 f2 = renameStates $! (minimize (autIntersection f1 f2))


\end{document}
