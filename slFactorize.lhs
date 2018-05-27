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
\title{slFactorize}
\date{}

\begin{document}

\maketitle\thispagestyle{empty}
Extract Forbidden Factors from  Jeff's FSAs:

Functions for retrieving forbidden factors from automata for SLk
  stringsets. 

slFactorize Name < fsa (in Jeff's format)
\begin{itemize}
\item Write:
  \begin{itemize}
  \item Haskell FSA (Name.fsa.hs) -- in Haskell show syntax
  \item Dot file (Name.fsa.dot)
  \item Their powerset graph as a Haskell FSA (Name.psg.hs)
    as a Dot file (Name.psg.dot)
  \item Forbidden factors (Name.FF.hs) as
    \mbox{(units, words, initial factors, free factors final factors)}
    each as set of list of (Symbol String) in Haskell show syntax
  \item The residue FSA as a Haskell FSA (Name.res.hs)
    as a Dot file (Name.res.dot)
  \item If the residue is non-empty
    \begin{itemize}
    \item The SL approximation as a Haskell FSA (Name.SL.hs)
    \item as a Dot file (Name.SL.dot)
    \end{itemize}
  \end{itemize}
\item    as well as output, one line for each language,
  \begin{itemize} \item
    \mbox{name, k, sf, ssm, sunits, swords, sinits, sfrees, sfinals, ssres}
    \item where k = 0 if language is not SL
  \item sf is number of states in FSA
  \item ssm is number of states in powerset graph
  \item sunits is the number of forbidden units
  \item swords is the number of forbidden words
  \item sinits is the number of forbidden initial factors
  \item sfrees is the number of forbidden free factors
  \item sfinals is the number of forbidden final factors
  \item sres is size of the residue DFA or "valid" if empty
  \end{itemize}
\end{itemize}

> module Main (main) where

> import ExtractSL
> import FSA
> import Porters
> 
> import Data.Set (Set)
> import System.Environment as Env

Get name of pattern from first argument for exportDotWithName

> getName ::  IO String
> getName = getArgs >>= return.aName
>           where aName [] = ""
>                 aName (x:xs) = x

Get FSA in multiline format, as in STII fsasJeff

> getFSA :: IO (FSA Integer String)
> getFSA = fmap (from Jeff) getContents

Write fsa as show show of Haskell datatype (as per Dakotah's usage)
 to name.fsa.hs and its dot format to name.fsa.dot
Returns fsa wrapped in IO

> writeFSA :: (Ord a, Show a, Ord b, Show b) => 
>                    String -> String -> (FSA b a) -> IO (FSA b a)
> writeFSA name ext fsa =
>     do
>       writeFile (name++"."++ext++".hs") (show fsa)
>       writeFile (name++"."++ext++".dot") (to Dot fsa)
>       return fsa

Convert to PSG and write as show show and its dot as with fsa\\
Returns the PSG wrapped in IO\\
Q: Why does generatePowerSetGraph fix elt type of stateset as Int?

> writePSG :: (Ord a, Show a, Ord b, Show b) => 
>                      String -> (FSA b a) -> IO (FSA (Set b) a)
> writePSG name fsa =
>     do
>       writeFile (name++".psg.hs") (show psg)
>       writeFile (name++".psg.dot") (to Dot (renameStatesBy formatSet psg))
>       return psg
>           where psg = powersetGraph fsa

> writeFactors :: (Ord b, Show b, Integral c, Enum b) =>
>                      String -> (FSA b String) -> IO (FSA c String)
> writeFactors name fsa =
>     do
>       writeFile (name++".ff.hs") (show ffs)
>       putStr ((show (size units)) ++ ", ") 
>       putStr ((show (size words)) ++ ", ") 
>       putStr ((show (size inits)) ++ ", ") 
>       putStr ((show (size free)) ++ ", ") 
>       putStr ((show (size finals)) ++ ", ")
>       writeFSA name ("SL") slFSA
>       return (renameStates $ residue slFSA fsa)
>         where
>           ffs = forbiddenSubstrings fsa
>           units = forbiddenUnits ffs
>           words = forbiddenWords ffs
>           inits = forbiddenInitials ffs
>           free = forbiddenFrees ffs
>           finals = forbiddenFinals ffs
>           slFSA = ((renameStates . minimize . buildFSA) ffs) `asTypeOf` fsa

> chkValid :: (Ord a, Show a, Ord b, Show b) =>
>             (FSA b a) -> String
> chkValid res
>     | (isNull res) = "valid"
>     | otherwise = (show . size . FSA.states) res

> main = do
>          name <- getName
>          fsa <- getFSA
>          writeFSA name "fsa" fsa
>          psg <- writePSG name fsa
>          putStr (name ++ ", " ++ (show (slQ fsa)) ++ ", ")
>          putStr ((show (size(states fsa))) ++ ", ")
>          putStr (show (size(states psg)) ++ ", ")
>          res <- writeFactors name fsa
>          writeFSA name "res" res
>          putStrLn (chkValid res)

\end{document}
