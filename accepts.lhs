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
\title{\texttt{accepts} --- program for collecting accepted strings}
\date{}

\begin{document}

\maketitle\thispagestyle{empty}
\begin{verbatim}
       accepts bound
       reads fsa from stdin
       writes strings accepted by fsa up to length bound on stdout
\end{verbatim}


> module Main (main) where

> import LTK.FSA
> import LTK.Porters
> import LTK.Factors
> import LTK.Traversals

> import qualified Data.Set as Set
> import qualified Data.List as List

> import System.Environment as Env

> getBound ::  IO Integer
> getBound = fmap (read . head) getArgs

> getFSA :: IO (FSA Integer String)
> getFSA = fmap (from Jeff) getContents

> shorterOrLessThan :: Ord a => [a] -> [a] -> Ordering
> shorterOrLessThan l r
>     | l == r               =  EQ
>     | (ll < rl)            =  LT
>     | (ll == rl && l < r)  =  LT
>     | otherwise            =  GT
>     where ll = length l
>           rl = length r

> main = do
>        bound <- getBound
>        fsa <- getFSA
>        (putStr .
>         unlines .
>         tmap (concat . tmap (take 2 . (++ " ") . transliterateString)) .
>         List.sortBy shorterOrLessThan .
>         tmap (tmap (untransliterateString) . unsymbols . word) .
>         Set.toList $
>         rejectingPaths (complement fsa) bound)

%% This was originally acceptsDFS instead of rejectingPaths.
%% But acceptsDFS is no longer exported and there is no acceptingPaths.
%% This is fine for now.

\end{document}
