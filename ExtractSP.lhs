\documentclass[12pt,twoside]{article}

%include polycode.fmt

%format (alphabet a) = ssigma "_" a
%format combineMap a b = "\bigcup\limits_{\mathclap{" i "\in " b "}}\left(" a "\;" i "\right)"
%format `compose` = 
%format delta = "\delta"
%format delta_prime = delta "^\prime"
%format `difference` = "-"
%format empty = "\varnothing"
%format Epsilon = "\varepsilon"
%format frontierZero = frontier "_0"
%format (FSA a b c d e) = "\Tup{Q," a "," b "," c "," d "}"
%format FSAt = "\textit{FSA}"
%format isSSQ = "(\sqsubseteq)"
%format isIn (a) = "(\in" a ")"
%format isNotIn (a) = "\not\in" a
%format `isSSQ` = "\sqsubseteq"
%format `isNotSSQ` = "\not\sqsubseteq"
%format `isomorphic` = "\cong"
%format keep = filter
%format `mappend` = "\mathbin{\lozenge}"
%format mempty    = "\mathord{\mathbf{e}}"
%format mergeBy f = merge "_{" f "}"
%format minimizeOver r = minimize "_{" r "}"
%format nerode = "\mathrel{\equiv^N}"
%format nextFrontier = frontier "_{" n "+ 1}"
%format normalizeNoTrim =
%format notNull = (/= empty)
%format null (a) = a == empty
%format p1 = "p_1"
%format p2 = "p_2"
%format qf = "F"
%format q_0 = "q_0"
%format (Set (a)) = "\{" a "\}"
%format Set.null = (= empty)
%format (singleton a) = "\{" a "\}"
%format size (a) = "\left\|" a "\right\|"
%format sortBy f = sort "_{" f "}"
%format ssigma = "\Sigma"
%format tmap = "\textit{map}"
%format Transition a b c = "\Transition[" a "]{" b "}{" c "}"
%format `union` = "\cup"
%format unionAll = "\bigcup{}"

\usepackage[letterpaper,margin=1in]{geometry}
\usepackage[T1]{fontenc}
\usepackage{times,newpxmath}\let\openbox\relax
\usepackage[english]{babel}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{amsthm}
\usepackage{draftnote}\draftcp
\usepackage{ec-phonology}
\usepackage{mathtools}
\usepackage{microtype}

\DeclareMathOperator{\SI}{SI}

\newcommand*{\EmptyString}{\varepsilon}
\newcommand*{\holyzero}{\mathord{\mathbf{0}}}
\newcommand*{\vocab}[1]{\emph{#1}}
\newcommand*{\Transition}[3][]{#2 \stackrel{#1}{\rightarrow} #3}

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
\title{Extracting FSSQs from Regular Stringsets}
\date{}

\begin{document}

\maketitle\thispagestyle{empty}

%if false

> module ExtractSP where
> import LogicClasses
> import FSA
> import Data.Monoid
> import Data.Set (Set)
> import qualified Data.Set as Set

> type FSAt = FSA

> normalizeNoTrim :: (Ord n, Ord e) => FSAt n e -> FSAt Integer e
> normalizeNoTrim f = renameStates . minimize . trimUnreachables $ f

> notNull = not . null

> compose = (.)
> infixr 9 `compose`

%endif

\section{Introduction}

In this module we define and implement a method for extracting
strictly piecewise ($\SP$) constraints from arbitrary regular stringsets.
These constraints are also known as forbidden subsequences,
due to the nature of $\SP$ stringsets.
Although extracting these constraints is an exponential-time operation,
the implementation clarified a linear-time algorithm to
generate an $\SP$ approximation of a stringset.

\begin{definition}
Let $v=\sigma_1\sigma_2\dots\sigma_n\in\Sigma^*$.
The \vocab{shuffle ideal} of $v$, $\SI(v)$, is the set:
\[
  \SI(v) =
  \{
    u_0\sigma_1 u_1\sigma_2 u_2\dots\sigma_n u_n
    : u_i\in\Sigma^*
  \}\mbox{.}
\]
\end{definition}

If $w\in\SI(v)$, we say $v$ is a \emph{subsequence} of $w$,
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


\section{Augmenting a regular stringset}
A regular stringset can be augmented
by adding transitions to its representative DFA,
or by augmenting the set of accepting states.
By the nature of the construction described herein,
we only need the first method.

Let $\Automaton{M}=\Tup{Q,\Sigma,\delta,q_0,F}$ be an automaton.
Define the \vocab{subsequence-closure} of $\Language{\Automaton{M}}$ as
the smallest superset of $\Language{\Automaton{M}}$
that is closed under deletion.  This can be implemented as a function
that inserts a transition on $\EmptyString$
wherever a transition occurred in $\delta$.


> subsequenceClosure :: (Ord n, Ord e) => FSAt n e -> FSAt n e
> subsequenceClosure (FSA ssigma delta q_0 qf d)  =  FSA ssigma (delta `union` delta_prime) q_0 qf False
>     where  delta_prime  =  tmap (\(Transition x a b) -> (Transition Epsilon a b)) delta

%if false

> spresidue :: (Enum n, Ord n, Ord e) => FSAt n e -> FSAt Integer e
> spresidue f = renameStates . minimize . determinize $
>               (complSpApprox f `union` f)
>     where complSpApprox  =  renameStates . complement . subsequenceClosure
>           renameStates' :: (Ord n, Ord e') => FSA n e' -> FSA Integer e'
>           renameStates' f =  renameStates f
>           f' = renameStates' f

% endif

Let $\Automaton{M}^\prime=\operatorname{subsequenceClosure} \Automaton{M}$,
and let $u,v,w\in\Sigma^*$
such that $uvw\in\Language{\Automaton{M}^\prime}$.
Then $uv\in\Language{\Automaton{M}^\prime}$, as every transition taken in
$w$ can be replaced by transitions on $\EmptyString$.
Similary $vw$ and $uw$ are in $\Language{\Automaton{M}^\prime}$.
Thus $\Language{\Automaton{M}^\prime}$ is $\SP$.
Note that since all of the original transitions remain intact,
$\Language{\Automaton{M}}\subseteq\Language{\Automaton{M}^\prime}$.

\section{Extracting forbidden subsequences}

\begin{lemma}
The set of forbidden subsequences of
$\Language{\Automaton{M}^\prime}$ is a subset of
that of $\Language{\Automaton{M}}$.
\end{lemma}
\begin{proof}
Suppose the set of forbidden subsequences of
$\Language{\Automaton{M}^\prime}$ is not a subset of
the set of forbidden subsequences of
$\Language{\Automaton{M}}$.
Then there exists some sequence $u$
that is forbidden in $\Language{\Automaton{M}^\prime}$
but not forbidden in $\Language{\Automaton{M}}$.
It follows that some string $w$ in $\Language{\Automaton{M}}$
contains $u$ as a subsequence.
But since $\Language{\Automaton{M}}\subseteq\Language{\Automaton{M}^\prime}$,
this string $w$ also occurs in $\Language{\Automaton{M}^\prime}$.
This contradicts the assumption that $u$ is a forbidden subsequence of
$\Language{\Automaton{M}^\prime}$.
Thus the set of forbidden subsequences of
$\Language{\Automaton{M}^\prime}$ is a subset of
the set of forbidden subsequences of
$\Language{\Automaton{M}}$.
\end{proof}

\begin{lemma}
The set of forbidden subsequences of
$\Language{\Automaton{M}}$ is a subset of
that of $\Language{\Automaton{M}^\prime}$.
\end{lemma}
\begin{proof}
Suppose the set of forbidden subsequences of
$\Language{\Automaton{M}}$ is not a subset of
the set of forbidden subsequences of
$\Language{\Automaton{M}^\prime}$.
Then there exists some sequence $u$
that is forbidden in $\Language{\Automaton{M}}$
but not forbidden in $\Language{\Automaton{M}^\prime}$.
It follows that some string $v$ in $\Language{\Automaton{M}^\prime}$
contains $u$ as a subsequence.
But since $\Language{\Automaton{M}^\prime}$ was formed
by allowing a computation to skip transitions of $\Automaton{M}$,
there exists a string $w$ in $\Language{\Automaton{M}}$
such that $v\sqsubseteq w$.
By the transitive property of subsequences,
this means $u\sqsubseteq w$.
This contradicts the assumption that $u$ is a forbidden subsequence of
$\Language{\Automaton{M}}$.
Thus the set of forbidden subsequences of
$\Language{\Automaton{M}}$ is a subset of
the set of forbidden subsequences of
$\Language{\Automaton{M}^\prime}$.
\end{proof}

Since each is a subset of the other, it follows that
the set of forbidden subsequences in $\Language{\Automaton{M}^\prime}$
is exactly the same set as those forbidden in $\Language{\Automaton{M}}$.
Because of this, collecting the minimal forbidden subsequences of
$\Language{\Automaton{M}^\prime}$
will give us the strictly piecewise constraints on
$\Language{\Automaton{M}}$.

> extractForbiddenSSQs :: (Ord n, Ord e) => FSAt n e -> Set [Symbol e]
> extractForbiddenSSQs = collectMinimalFSSQs . normalizeNoTrim `compose` subsequenceClosure

Since $\Automaton{M}^\prime$ is $\SP$,
it suffices to simply traverse $\Automaton{M}^\prime$,
finding all minimal (in terms of subsequence) paths
from $q_0$ to the fail-state ($\holyzero$).
To start, we will need a notion of a @Path@:

> data Path n e = Path [State n] [Symbol e] (Set (State n)) deriving (Eq, Ord, Read, Show)

> statePath   :: Path n e -> [State n]
> symbolPath  :: Path n e -> [Symbol e]
> seenStates  :: Path n e -> Set (State n)
> statePath   (Path qs _ _)  =  qs
> symbolPath  (Path _ xs _)  =  xs
> seenStates  (Path _ _ ss)  =  ss

It will also help to have a means of creating simple paths,
as well as a way to combine them.
We create a simple constructor function @path@,
and take advantage of the fact that paths act as a monoid
under extension.

> path :: (Ord n, Ord e) => State n -> Symbol e -> Path n e
> path q x = Path [q] [x] (singleton q)

> instance (Ord n, Ord e) => Monoid (Path n e) where
>     mempty           =  Path   mempty mempty empty
>     p1 `mappend` p2  =  Path  (statePath p1 ++ statePath p2)
>                               (symbolPath p1 ++ symbolPath p2)
>                               (seenStates p1 `union` seenStates p2)

In the simplest terms, we want to search a graph from bottom to top,
visiting a given state no more than once in a given path.  Since in
theory we could trim a path upon reaching an already-seen forbidden
subsequence, we want a breadth-first traversal:

> breadthFirstSearch :: (Ord n, Ord e) => FSAt n e -> Set (Path n e)
> breadthFirstSearch f  =  snd (until (Set.null . fst) next start)
>     where  next (a, b)  =  let nf = nextFrontier f a
>                            in (nf, b `union` nf)
>            start        =  (frontierZero f, frontierZero f)

We will work our way down, from the high level to the concrete:

> nextFrontier :: (Ord n, Ord e) => FSAt n e -> Set (Path n e) -> Set (Path n e)
> nextFrontier f ps  =  combineMap (flip (extendPathsUp f) ps) (alphabet f)

%if false

> combineMap :: (Container (s c) b, Container c a, Collapsible s) =>
>               (a1 -> b) -> s a1 -> c
> combineMap f xs  = unionAll (tmap f xs)

%endif

> extendPathsUp :: (Ord n, Ord e) => FSAt n e -> Symbol e -> Set (Path n e) -> Set (Path n e)
> extendPathsUp f x ps  =  combineMap (extendPathUp f x) ps

> extendPathUp :: (Ord n, Ord e) => FSAt n e -> Symbol e -> Path n e -> Set (Path n e)
> extendPathUp f x p
>     | null (statePath p)  =  empty
>     | otherwise           =  tmap (\r -> r `mappend` p) ps
>     where  q   =  chooseOne (statePath p)
>            ss  =  keep (isNotIn (seenStates p))  .
>                   tmap source                    .
>                   keep ((== x) . edgeLabel)      .
>                   keep ((== q) . destination)    $
>                   transitions f
>            ps  =  tmap (\s -> path s x) ss

> frontierZero :: (Ord n, Ord e) => FSAt n e -> Set (Path n e)
> frontierZero  =  tmap f . zeroStates
>     where  f p  =  Path [p] mempty empty

> zeroStates :: (Ord n, Ord e) => FSAt n e -> Set (State n)
> zeroStates f  =  states f `difference` (states . trimFailStates) f

This gives us everything we need to actually construct a set of
forbidden subsequences from an automaton:

> collectFSSQs :: (Ord n, Ord e) => FSAt n e -> Set [Symbol e]
> collectFSSQs f  =  tmap symbolPath                        .
>                    keep (isIn i . chooseOne . statePath)  .
>                    keep (notNull . statePath)             $
>                    breadthFirstSearch f
>     where  i  = initials f

Further, we can derive a minimal set of forbidden subsequences by
filtering out elements that are generated by others.  Formally, if
$v\sqsubseteq w$, for $v$ and $w$ forbidden subsequences, $w$ is not a
minimal forbidden subsequence.

> collectMinimalFSSQs :: (Ord n, Ord e) => FSAt n e -> Set [Symbol e]
> collectMinimalFSSQs  =  Set.fromList             .
>                         filterAbsorbed           .
>                         sortBy (comparing size)  .
>                         Set.toList               .
>                         collectFSSQs
>     where  filterAbsorbed (x:xs)  =  x : filterAbsorbed (keep (\y -> x `isNotSSQ` y) xs)
>            filterAbsorbed _       =  []

This concludes the algorithm for extracting minimal forbidden subsequences,
and thus for extracting strictly-piecewise factors
from an arbirary regular stringset.

\section{Testing whether a stringset is strictly piecewise}

If $\Automaton{M}$ already represents an $\SP$ stringset,
then $\Automaton{M}^\prime$ will recognize
the same stringset as its source.
This makes for quite the simple test to determine
whether a stringset is $\SP$:

> isSP :: (Ord n, Ord e) => FSAt n e -> Bool
> isSP f = normalize f `isomorphic` normalize (subsequenceClosure f)

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
> odds (x:xs)     = evens xs

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

\end{document}
