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
\title{\texttt{accepts} --- program for colleting accepted strings}
\date{}

\begin{document}

\maketitle\thispagestyle{empty}
\begin{verbatim}
       accepts bound
       reads fsa from stdin
       writes strings accepted by fsa up to length bound on stdout
\end{verbatim}

> module Main (main) where
> 
>     
> import FSA
> 
> import ReadJeff
> 
> -- import SLfactors
> import Factors
> import Exporters
> import Mungers
> import Traversals
>     
> import qualified Data.Set as Set
> import qualified Data.List as List
>     
> import System.Environment as Env
> 
> burstWith :: Char -> [String] -> String
> burstWith c sts = foldr (catc) "" sts
>                   where
>                     catc s1 s2 = s1 ++ c:s2
> 
> burstnl = burstWith '\n'
> 
> getBound ::  IO Integer
> getBound = getArgs >>= return.read.head
> 
> getFSA :: IO (FSA Int String)
> getFSA = getContents >>= return.readJeff.transLit
> 
> getFSAbyName :: String -> IO (FSA Int String)
> getFSAbyName path = readFile path >>= return.readJeff.transLit
> 
> shorterOrLessThan :: String -> String -> Ordering
> shorterOrLessThan l r
>     | ((length l) < (length r)) = LT
>     | ((length l) == (length r) && l < r) = LT
>     | ((length l) == (length r) && l == r) = EQ
>     | otherwise = GT
> 
> main = do
>        bound <- getBound
>        fsa <- getFSA
>        (putStr.burstnl) (List.sortBy shorterOrLessThan (Set.toList(acceptsDFS fsa bound)))

\end{document}
