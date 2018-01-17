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
\title{Additional Exporters}
\date{}

\begin{document}

\maketitle\thispagestyle{empty}
Adding \texttt{dotifyWithName}\\
I maintain that should be $\f{dotify} f = \f{dotifyWithName} f []$
\begin{code}
module MoreExporters where

import Exporters
import FSA

dotifyWithName :: (Ord e, Ord n, Show e, Show n) => FSA n e -> String -> String
dotifyWithName f name = 
    unlines $ ["digraph " ++ name ++ "{",
               "graph [rankdir=\"LR\"];",
               "node  [fixedsize=\"false\", fontsize=\"12.0\"];",
               "edge  [fontsize=\"12.0\", arrowsize=\"0.5\"];"] ++
               dotifyInitials f     ++
               dotifyStates f       ++
               dotifyFinals f       ++
               dotifyTransitions f  ++
               ["}"]
\end{code}
\end{document}
% ----- Configure Emacs -----
Local Variables: ***
mode: latex ***
mmm-classes: literate-haskell-latex ***
End: ***
