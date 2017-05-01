\documentclass[12pt,twoside]{article}

%include polycode.fmt

%format combineMap a b = "\bigcup\limits_{\mathclap{" i "\in " b "}}\left(" a "\;" i "\right)"
%format `difference` = "-"
%format empty = "\varnothing"
%format frontierZero = frontier "_0"
%format `intersection` = "\cap"
%format isIn a = "(\in" a ")"
%format isNotIn a = "(\not\in" a ")"
%format isSSQ = "(\sqsubseteq)"
%format `isSSQ` = "\sqsubseteq"
%format `isNotSSQ` = "\not\sqsubseteq"
%format `isomorphic` = "\cong"
%format `mappend` = "\mathbin{\lozenge}"
%format mempty    = "\mathord{\mathbf{e}}"
%format mergeBy f = merge "_{" f "}"
%format minimizeOver r = minimize "_{" r "}"
%format nerode = "\mathrel{\equiv^N}"
%format nextFrontier = frontier "_{" n "+ 1}"
%format (singleton a) = "\{" a "\}"
%format sortBy f = sort "_{" f "}"
%format size a = "\left\|" a "\right\|"
%format `union` = "\cup"
%format unionAll = "\bigcup{}"

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

\DeclareMathOperator{\RA}{RA}
\DeclareMathOperator{\PR}{PR}
\DeclareMathOperator{\SI}{SI}

\newcommand*{\EmptyString}{\varepsilon}
\newcommand*{\holyzero}{\mathord{\mathbf{0}}}
\newcommand*{\vocab}[1]{\emph{#1}}

\theoremstyle{plain}
\newtheorem{theorem}{Theorem}
\newtheorem{lemma}{Lemma}
\newtheorem{corollary}{Corollary}

\theoremstyle{definition}
\newtheorem{definition}{Definition}

\theoremstyle{remark}
\newtheorem{remark}{Remark}

\renewcommand{\qedsymbol}{\rule{0.5\baselineskip}{0.5\baselineskip}}

\author{Dakotah Lambert}
\title{A method for determining and approximating $\SP$}
\date{}

\begin{document}

\maketitle\thispagestyle{empty}

%if false

> module SPTest where
> import LogicClasses
> import Factors
> import FSA
> import Data.Monoid
> import Data.Set (Set)
> import qualified Data.Set as Set

%endif

\section{Introduction}

This module is structured loosely as a set of notes.
It is by no means an attempt at a paper.

In this module we define and implement an algorithm
for deciding whether a given regular stringset
is strictly piecewise ($\SP$).
A regular stringset is any that can be defined by a
deterministic finite-state automaton (DFA).

A DFA is defined by a five-tuple
$\Automaton{m}=\Tup{Q,\Sigma,\delta,q_0,F}$, where
$Q$ is the set of states in $\Automaton{m}$,
$\Sigma$ is the alphabet,
$\delta : Q\times \Sigma \to Q$ is the (partial) transition function,
$q_0\in Q$ is the initial state, and
$F\subseteq Q$ is the set of final states.
We will use @FSA n e@ to represent the class of DFAs
where $Q\subseteq @n@$ and $\Sigma\subseteq @e@$.
Let $L$ be a stringset with alphabet $\Sigma$,
whose tail-canonical acceptor is $\Automaton{m}$.

\begin{definition}
Let $w=\sigma_1\sigma_2\dots\sigma_n\in\Sigma^*$.
The \vocab{shuffle ideal of $w$}, $\SI(w)$, is the set:
\[
  \SI(w) =
  \{
    u_0\sigma_1 u_1\sigma_2 u_2\dots\sigma_n u_n
    : u_i\in\Sigma^*
  \}\mbox{.}
\]
\end{definition}

If $v\in\SI(w)$, we say $v$ is a \emph{subsequence} of $w$,
$v\sqsubseteq w$.
Determining whether $v$ is a subsequence of $w$ is quite a simple algorithm:

> isSSQ :: (Eq a) => [a] -> [a] -> Bool
> []      `isSSQ`  _   =  True
> _       `isSSQ`  []  =  False
> (v:vs)  `isSSQ`  (w:ws)
>     | v == w     =  vs `isSSQ` ws
>     | otherwise  =  (v:vs) `isSSQ` ws

%if false
For formatting's sake:

> isNotSSQ :: (Eq a) => [a] -> [a] -> Bool
> a `isNotSSQ` b = not (a `isSSQ` b)

%endif


A stringset is $\SP$ iff it is the intersection of the complements of
finitely many shuffle ideals.  Then an $\SP$ stringset can be described
completely by:
\[
\overline{G} =
\left\{w : \SI(w)\cap L = \varnothing\right\}
\]

Since we want to create an $\SP$ approximation of any given stringset,
a na\"{\i}ve algorithm to determine whether the stringset is already $\SP$
might be something like:

> isSP :: (Ord e, Ord n) => FSA n e -> Bool
> isSP f   =   f' `isomorphic` g'
>     where  f'  =  normalize f
>            g'  =  (normalize . flip asTypeOf f' . approximateSP) f

We say a string $w\in\Sigma^*$ is zero for $L$ (denoted $w=\holyzero$)
iff for all $v,x\in\Sigma^*$, $vwx\not\in L$.

It has been proven by Fu et al.\@@ (2011)
that $\SP$ stringsets have two fundamental properties.
First, they are wholly nonzero, which simply means that if
$w\not\in L$, then $w=\holyzero$.
Second, they are right-annihilating.

\begin{definition}
A stringset is \emph{right-annihilating} iff for all $a,w,x\in\Sigma^*$,
$wxa=\holyzero$ whenever $wa=\holyzero$.
\end{definition}

\begin{lemma}
If $L$ is right-annihilating and $w=\holyzero$,
then $vw=\holyzero$ for all $v\in\Sigma^*$
\end{lemma}
\begin{proof}
Represent the empty string by $\EmptyString$.
If $w=\holyzero$, then $\EmptyString w=\holyzero$.
Since $L$ is right-annihilating and $v\in\Sigma^*$,
$\EmptyString vw=\holyzero$, or simply $vw=\holyzero$.
\end{proof}

\begin{corollary}
If $L$ is $\SP$ and $w$ is a forbidden subsequence of $L$,
then there is no path
$\Path[w]{q_0}{q^\prime}$ in $\Automaton{m}$ for any $q^\prime\in Q$.
If $\Automaton{m}$ is completed, this corresponds to a path
$\Path[w]{q_0}{\holyzero}$.
Further, there exists a path $\Path[w]{\EmptyString}{\holyzero}$
in the syntactic monoid of $\Automaton{m}$.
\end{corollary}

Thus, to collect the minimal forbidden subsequences of $L$,
it suffices to simply traverse
either $\Automaton{m}$ or its syntactic monoid,
finding all minimal (in terms of subsequence) paths
from $q_0$ or $\EmptyString$ to $\holyzero$.

To start, we will need a notion of a @Path@:

> data Path n e  =  Path [State n] [Symbol e] (Set (State n))
>                deriving (Eq, Ord, Read, Show)

> statePath   :: Path n e -> [State n]
> symbolPath  :: Path n e -> [Symbol e]
> seenStates  :: Path n e -> Set (State n)
> statePath   (Path qs _ _)  =  qs
> symbolPath  (Path _ xs _)  =  xs
> seenStates  (Path _ _ ss)  =  ss

It will also help to have a means of creating simple paths,
as well as a way to combine them:

> path :: (Ord e, Ord n) => State n -> Symbol e -> Path n e
> path q x = Path [q] [x] (singleton q)

> instance (Ord e, Ord n) => Monoid (Path n e) where
>     mempty           =  Path mempty mempty empty
>     p1 `mappend` p2  =  Path
>                         (statePath p1 ++ statePath p2)
>                         (symbolPath p1 ++ symbolPath p2)
>                         (seenStates p1 `union` seenStates p2)

In the simplest terms, we want to search a graph from bottom to top,
visiting a given state no more than once in a given path.  Since in
theory we could trim a path upon reaching an already-seen forbidden
subsequence, we want a breadth-first traversal:

> breadthFirstSearch ::  (Ord e, Ord n) =>
>                        FSA n e -> Set (Path n e)
> breadthFirstSearch f  =  snd (until ((== 0) . size . fst) next start)
>     where  next (a, b)  =  let nf = nextFrontier f a
>                            in (nf, b `union` nf)
>            start        =  (frontierZero f, frontierZero f)

We will work our way down, from the high level to the concrete:

> nextFrontier ::  (Ord e, Ord n) =>
>                  FSA n e -> Set (Path n e) -> Set (Path n e)
> nextFrontier f ps  =  combineMap (flip (extendPathsUp f) ps) (alphabet f)

%if false

> combineMap :: (Container (s c) b, Container c a, Collapsible s) =>
>               (a1 -> b) -> s a1 -> c
> combineMap f xs  = unionAll (tmap f xs)

%endif

> extendPathsUp ::  (Ord e, Ord n) =>
>                   FSA n e -> Symbol e -> Set (Path n e) -> Set (Path n e)
> extendPathsUp f x ps  =  combineMap (extendPathUp f x) ps

> extendPathUp ::  (Ord e, Ord n) =>
>                  FSA n e -> Symbol e -> Path n e -> Set (Path n e)
> extendPathUp f x p
>     | size (statePath p) == 0  =  empty
>     | otherwise                =  tmap (\r -> r `mappend` p) ps
>     where  q   =  chooseOne (statePath p)
>            ss  =  keep (isNotIn (seenStates p))  .
>                   tmap source                    .
>                   keep ((== x) . edgeLabel)      .
>                   keep ((== q) . destination)    $
>                   transitions f
>            ps  =  tmap (\s -> path s x) ss

> frontierZero :: (Ord e, Ord n) => FSA n e -> Set (Path n e)
> frontierZero  =  tmap f . zeroStates
>     where  f p  =  Path [p] mempty empty

> zeroStates ::  (Ord e, Ord n) =>
>                FSA n e -> Set (State n)
> zeroStates f  =  states f `difference` (states . trimFailStates) f

This gives us everything we need to actually construct a set of
forbidden subsequences, from either an automaton or a syntactic
monoid:

> collectFSSQs   ::   (Ord e, Ord n) =>
>                     FSA n e -> Set [Symbol e]
> collectFSSQs f  =  tmap symbolPath                        .
>                    keep (isIn i . chooseOne . statePath)  .
>                    keep ((/= 0) . size . statePath)       $
>                    breadthFirstSearch f
>     where  i  = initials f

Further, we can derive a minimal set of forbidden subsequences by
filtering out elements that are generated by others.  Formally, if
$w\in\SI(v)$, for $w$ and $v$ forbidden subsequences, $w$ is not a
minimal forbidden subsequence.

> collectMinimalFSSQs   ::   (Ord e, Ord n) =>
>                            FSA n e -> Set [Symbol e]
> collectMinimalFSSQs  =  Set.fromList             .
>                         filterAbsorbed           .
>                         sortBy (comparing size)  .
>                         Set.toList               .
>                         collectFSSQs
>     where  filterAbsorbed []      =  []
>            filterAbsorbed (x:xs)  =  x : filterAbsorbed
>                                      (keep (\y -> x `isNotSSQ` y) xs)

Putting it all together gives us the following $\SP$ approximation:

> approximateSP  ::  (Ord e, Ord n, Enum n1, Ord n1) =>
>                    FSA n e -> FSA n1 e
> approximateSP f
>     | size fssqs == 0  =  emptyWithAlphabet (alphabet f)
>     | otherwise        =  pairwise ms cs
>     where  fssqs   =  (Set.toList . collectMinimalFSSQs) f
>            si      =  negativePiecewiseFactor (alphabet f)
>            cs      =  tmap (si . tmap singleton) fssqs
>            g       =  renameStates . minimizeOver nerode
>            ms a b  =  g (a `intersection` b)

\clearpage
\section{Appendix --- merge sort}

To perform a merge sort, we must be able to split a list
into two smaller lists.  Taking the even and odd elements seems the
best approach when working with a lazy linked-list structure.

> evens :: [a] -> [a]
> evens []        = []
> evens (x:[])    = [x]
> evens (x:y:ys)  = x : evens ys

> odds :: [a] -> [a]
> odds []         = []
> odds (x:[])     = []
> odds (x:y:ys)   = y : odds ys

Then, to merge two already-sorted lists, progress through the two
lists linearly, at each step placing the smallest visible element.

> mergeBy :: (a -> a -> Ordering) -> [a] -> [a] -> [a]
> mergeBy _  x       []  = x
> mergeBy _  []      y   = y
> mergeBy f  (x:xs)  (y:ys)
>     | f x y /= GT  =  x : mergeBy f xs (y:ys)
>     | otherwise    =  y : mergeBy f (x:xs) ys

To sort using this method, repeatedly split until all lists are singleton,
then merge the results.

> sortBy :: (a -> a -> Ordering) -> [a] -> [a]
> sortBy _  []      =  []
> sortBy _  (x:[])  =  [x]
> sortBy f  xs      =  mergeBy f (sortBy f (evens xs)) (sortBy f (odds xs))

Since we want to be able to say @sortBy (comparing size)@, a reasonable way
to define @comparing@ is:

> comparing :: (Ord b) => (a -> b) -> a -> a -> Ordering
> comparing f x y  = compare (f x) (f y)

\clearpage
\section{Appendix --- pairwise intersection}

> pairwise :: (a -> a -> a) -> [a] -> a
> pairwise _ []      = undefined
> pairwise _ (x:[])  = x
> pairwise f xs      = (pairwise f . pairwise' f) xs
> pairwise' :: (a -> a -> a) -> [a] -> [a]
> pairwise' _ []        = []
> pairwise' _ (x:[])    = [x]
> pairwise' f (x:y:ys)  = f x y : pairwise' f ys

\end{document}
