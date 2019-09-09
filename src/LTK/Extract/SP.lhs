\documentclass[12pt,twoside]{article}

%include polycode.fmt

%format delta = "\delta"
%format delta_prime = delta "^\prime"
%format empty = "\varnothing"
%format Epsilon = "\varepsilon"
%format (FSA a b c d e) = "\Tup{Q," a "," b "," c "," d "}"
%format FSAt = "\textit{FSA}"
%format isSP' = isSP
%format isSSQ = "(\sqsubseteq)"
%format isIn (a) = "(\in" a ")"
%format isNotIn (a) = "\not\in" a
%format `isSSQ` = "\sqsubseteq"
%format `isNotSSQ` = "\not\sqsubseteq"
%format `isomorphic` = "\cong"
%format keep = filter
%format mergeBy f = merge "_{" f "}"
%format minimizeOver r = minimize "_{" r "}"
%format qf = "F"
%format q_0 = "q_0"
%format (Set (a)) = "\{" a "\}"
%format size (a) = "\left\|" a "\right\|"
%format isize (a) = "\left\|" a "\right\|"
%format sortBy f = sort "_{" f "}"
%format ssigma = "\Sigma"
%format subsequenceClosure' = subsequenceClosure
%format ForbiddenSubsequences e = Set [e]
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


> {-# OPTIONS_HADDOCK show-extensions #-}
> {-# Language
>   MultiParamTypeClasses
>   #-}
> {-|
> Module    : LTK.Extract.SP
> Copyright : (c) 2017-2019 Dakotah Lambert
> License   : MIT
> 
> Find forbidden subsequences of an automaton.
> Formerly known as @LTK.ExtractSP@.
>
> @since 0.2
> -}

> module LTK.Extract.SP ( ForbiddenSubsequences(..)
>                       , forbiddenSubsequences
>                       , fsaFromForbiddenSubsequences
>                       , isSP
>                       , isSSQ
>                       , subsequenceClosure
>                       ) where
> import LTK.Factors
> import LTK.FSA
> import LTK.Traversals

> import Control.DeepSeq (NFData)
> import Data.List (sortBy)
> import Data.Ord (comparing)
> import Data.Set (Set)
> import qualified Data.Set as Set

%if false

> -- | A convenience-type for declaring collections of forbidden subsequences.
> -- The member types are (lists of) the raw alphabet type (not (Symbol .))
> data ForbiddenSubsequences e = ForbiddenSubsequences {
>       attestedAlphabet  ::  Set e
>     , getSubsequences   ::  Set [e]
>     } deriving (Eq, Ord, Read, Show)

%endif

> instance Ord e => Container (ForbiddenSubsequences e) [e] where
>     isEmpty c     =  isEmpty (getSubsequences c)
>     isIn c        =  isIn (getSubsequences c)
>     union         =  g union
>     intersection  =  g intersection
>     difference    =  g difference
>     empty         =  ForbiddenSubsequences {
>                        attestedAlphabet = empty
>                      , getSubsequences = empty
>                      }
>     singleton a   =  ForbiddenSubsequences {
>                        attestedAlphabet = fromCollapsible a
>                      , getSubsequences = singleton a
>                      }

> g :: Ord e => (Set [e] -> Set [e] -> Set [e]) ->
>      ForbiddenSubsequences e -> ForbiddenSubsequences e ->
>      ForbiddenSubsequences e
> g f c1 c2 = ForbiddenSubsequences {
>               attestedAlphabet = union
>                                  (attestedAlphabet c1)
>                                  (attestedAlphabet c2)
>             , getSubsequences = f
>                                 (getSubsequences c1)
>                                 (getSubsequences c2)
>             }

> type FSAt = FSA

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

%if false
Documentation


> -- |@(isSSQ a b)@ returns true iff @b@ contains the symbols of @a@
> -- in order, but not necessarily adjacently.

%endif


> isSSQ :: (Eq a) => [a] -> [a] -> Bool
> []      `isSSQ`  _   =  True
> (v:vs)  `isSSQ`  ws
>     | isEmpty notV  =  False
>     | otherwise     =  vs `isSSQ` tail notV
>     where notV = dropWhile (/= v) ws

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



> subsequenceClosure' :: (Ord n, Ord e) => FSAt n e -> FSAt n e
> subsequenceClosure' (FSA ssigma delta q_0 qf _)  =  FSA ssigma (delta `union` delta_prime) q_0 qf False
>     where  delta_prime  =  tmap (\(Transition _ a b) -> (Transition Epsilon a b)) delta

%if false

> -- |Returns an 'FSA' that accepts every string accepted by the
> -- original, as well as every subsequence of these strings.
> subsequenceClosure :: (Ord n, Ord e) => FSA n e -> FSA n e
> subsequenceClosure = subsequenceClosure'

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

%if false

> -- |Given an 'FSA' \(A\),
> -- returns the set of subsequences \(v\) such that
> -- for all words \(w\), \(v\sqsubseteq w\) implies
> -- that \(w\) is not accepted by \(A\).
> forbiddenSubsequences :: (Ord n, Ord e) => FSA n e -> ForbiddenSubsequences e
> forbiddenSubsequences fsa = ForbiddenSubsequences {
>                               attestedAlphabet = alphabet fsa
>                             , getSubsequences  = collectMinimalFSSQs fsa
>                             }

%endif

Since $\Automaton{M}^\prime$ is $\SP$,
it suffices to simply traverse $\Automaton{M}^\prime$,
finding all minimal (in terms of subsequence) paths
from $q_0$ to the fail-state ($\holyzero$).
A cyclic path is necessarily non-minimal,
so it suffices to check only the acyclic paths.
Since every state in an $\SP$ automaton is accepting
save for a possible unique non-accepting sink,
we can merely check paths in the complement.
Since this complement has exactly one accepting state,
and exactly one initial state,
we can also use the acyclic paths of its reversal,
which prevents having to reverse every extracted string.

> collectFSSQs :: (Ord n, Ord e) => FSAt n e -> Set [e]
> collectFSSQs f = tmap (unsymbols . labels) .
>                  keep (maybe False (isIn (finals f')) . endstate) $
>                  acyclicPaths f'
>     where f' = normalize . LTK.FSA.reverse . complement $
>                subsequenceClosure f

Further, we can derive a minimal set of forbidden subsequences by
filtering out elements that are generated by others.  Formally, if
$v\sqsubseteq w$, for $v$ and $w$ forbidden subsequences, $w$ is not a
minimal forbidden subsequence.


> collectMinimalFSSQs :: (Ord n, Ord e) => FSAt n e -> Set [e]
> collectMinimalFSSQs  =  Set.fromList              .
>                         absorb                    .
>                         sortBy (comparing isize)  .
>                         Set.toList                .
>                         collectFSSQs
>     where  absorb (x:xs)  =  x : absorb (keep (\y -> x `isNotSSQ` y) xs)
>            absorb _       =  []

This concludes the algorithm for extracting minimal forbidden subsequences,
and thus for extracting strictly-piecewise factors
from an arbirary regular stringset.

\section{Testing whether a stringset is strictly piecewise}

If $\Automaton{M}$ already represents an $\SP$ stringset,
then $\Automaton{M}^\prime$ will recognize
the same stringset as its source.
This makes for quite the simple test to determine
whether a stringset is $\SP$:

> isSP' :: (Ord n, Ord e) => FSAt n e -> Bool
> isSP' f = f == subsequenceClosure f

%if false

> -- |Returns @True@ iff the stringset represented by the given 'FSA'
> -- is Strictly Piecewise, that is,
> -- if the 'FSA' accepts all subsequences of every string it accepts.
> isSP :: (Ord n, Ord e) => FSA n e -> Bool
> isSP = isSP'

> -- |The stringset represented by the forbiddenSubsequences.
> fsaFromForbiddenSubsequences :: (Ord e, NFData e) =>
>                                 ForbiddenSubsequences e -> FSA Integer e
> fsaFromForbiddenSubsequences fssqs
>     = build (attestedAlphabet fssqs) . singleton .
>       makeConstraint .
>       tmap (singleton . forbidden . Subsequence . tmap singleton) .
>       fromCollapsible $ getSubsequences fssqs

%endif

\end{document}
