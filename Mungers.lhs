\documentclass[12pt,twoside]{article}
\input litHaskellcode

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


\author{JRogers}
\title{\texttt{Mungers}}
\date{}

\begin{document}
\maketitle\thispagestyle{empty}
Transliteration and name munging functions from \texttt{Exporters.hs}
                

> module Mungers where
> import FSA
>     
> import qualified Data.Set as Set
> import Data.Char as Char

\begin{verbatim}
transLit  -- transliterate Jeff's fsa to use {L,H,S}X{0,1,2}
  w0 --> L
  w1 --> H
  w2 --> S
  .s --> \epsilon
\end{verbatim}

> transLit :: String -> String
> transLit [] = []
> transLit ('.':'s':st:cs)
>     | st == '0' = transLit cs
>     | st == '1' = '`' : transLit cs
>     | st == '2' = ('\'') : transLit cs
>     | otherwise = st : transLit cs
> transLit ('w':n:cs) 
>     | n == '0' = 'L' : transLit cs
>     | n == '1' = 'H' : transLit cs
>     | n == '2' = 'S' : transLit cs
>     | n == '3' = 'X' : transLit cs
>     | n == '4' = 'Y' : transLit cs
>     | otherwise = n  : transLit cs   -- pass anything else through
> transLit (c:cs) = c : transLit cs
> 
> -- coerce states into Int
> mungeToInt :: (Ord a, Ord b) => FSA b a -> FSA Int a
> mungeToInt fsa = renameStates fsa
> 

\begin{verbatim}
 The next few things just reformat the FSA tokens so that they don't 
   break dot.  They are, as you might guess, almost as brittle as the
   dot syntax itself.
deFang -- strip out non-Alpha for dot graph name
\end{verbatim}

> deFang :: String -> String
> deFang [] = []
> deFang (c:cs)
>        | isAlpha c = c : (deFang cs)
>        | otherwise = deFang cs


\texttt{encodestates} flattens Set valued states in a dot-compatible way

> encodeStates :: (Ord a, Show a, Ord b, Show b) => 
>                    (FSA (Set.Set b) a) -> (FSA String a)
> encodeStates fsa = (FSA (alphabet fsa)
>                     (flattenTransitions (transitions fsa))
>                     (flattenStates (initials fsa))
>                     (flattenStates (finals fsa)) 
>                     (isDeterministic fsa) )
>     where
>       encodeSet :: String -> String
>       encodeSet [] = []
>       encodeSet (c:cs) 
>           | (c == '[') = '<':(encodeSet cs)
>           | (c == ']')  = '>':(encodeSet cs)
>           | (c == '\\') = encodeSet cs
>           | otherwise = c:(encodeSet cs)
>       
>       flattenStates :: (Ord b, Show b) =>
>                        (Set.Set (State (Set.Set b))) ->
>                            (Set.Set (State String))
>       flattenStates states = Set.map flattenState states
> 
>       flattenState :: (Ord b, Show b) => (State (Set.Set b)) -> State String
>       flattenState (State s) = (State (encodeSet (show (Set.toList s))))
>       
>       flattenTransitions :: (Ord a, Ord b, Show b) =>
>                             (Set.Set (Transition (Set.Set b) a) ) ->
>                                 (Set.Set (Transition String a) )
>       flattenTransitions ts = Set.map flattenTransition ts
> 
>       flattenTransition :: (Ord a, Ord b, Show b) =>
>                            (Transition (Set.Set b) a) ->
>                                (Transition String a)
>       flattenTransition t = (Transition (edgeLabel t) 
>                              (flattenState (source t))
>                              (flattenState (destination t)) )

\end{document}
