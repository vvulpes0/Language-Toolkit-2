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
\title{ExtractSL}
\date{}

\begin{document}

\maketitle\thispagestyle{empty}
Note: A major difficulty in working with this module is the fact that
sometimes, such as in \texttt{FSA n e} `\texttt{e}' is the base type of
Symbols, so the actual edge label type is \texttt{Symbol e}.  This is also
true in the definition of \texttt{Path} and {\texttt ForbiddenSubstrings}.
At others, such as the definition of\texttt{ForbiddenPaths} it is bound to
\texttt{Symbol e}.  This creates conflicts.

Functions for
\begin{itemize}
\item Determining if the stringset recongized by an automaton is $\SL$ and, if
  so, determining $k$.
\item Extracting the sets of Forbidden Initial, Free and Final Factors,
  and Forbidden Words that (partially) define that stringset.
\item Generating an automaton that provides an $\SL$ approximation of the
  stringset recognized by an automaton.
\item andere Dinge
\end{itemize}

Forbidden factors and words are explained in Rogers and Lambert,
MoL'17 as is the notion of an $\SL$ approximation of a non-$\SL$ stringset.


> {-# OPTIONS_HADDOCK show-extensions #-}
> {-# Language
>   MultiParamTypeClasses
>   #-}
> {-|
> Module    : LTK.Extract.SL
> Copyright : (c) 2017-2019,2023 Jim Rogers and Dakotah Lambert
> License   : MIT
>
> Find forbidden substrings of an automaton.
> Formerly known as @LTK.ExtractSL@.
>
> @since 0.2
> -}
> module LTK.Extract.SL
>        ( ForbiddenSubstrings(..)
>        , ForbiddenPaths(..)
>        , TaggedSubstring(..)
>        -- *Extracting forbidden substrings
>        , factorsFromPaths
>        , forbiddenSubstrings
>        -- *Building automata
>        , buildFSA
>        -- *Determining SL
>        , isSL
>        , slQ
>        ) where

> import Control.DeepSeq (NFData)
> import Data.Set (Set)
> import qualified Data.List as List
> import qualified Data.Set as Set

> import LTK.Factors
> import LTK.FSA
> import LTK.Traversals

\section*{Determining $\SL{k}$}
This is an implementation of the powerset graph based algorithm given in
Edlefsen, et al., MCURCSM'08 and sketched in Rogers and Lambert, MoL'17.
Since we are often working with the full powerset graph anyway, we do not use
the polynomial-time pair-graph version.


> -- |Returns @True@ iff the stringset represented by the given t'FSA'
> -- is Strictly Local, that is,
> -- if it satisfies Suffix-Substition Closure for
> -- some specific factor size \(k\).
> isSL :: (Ord e, Ord n) => FSA n e -> Bool
> isSL = (> 0) . slQ

> -- |Returns the smallest factor size for which
> -- the stringset represented by the given t'FSA'
> -- satisfies Suffix-Substitution Closure,
> -- or @0@ if there is no such \(k\).
> slQ :: (Ord e, Ord n) => FSA n e -> Integer
> slQ fsa = slPSGQ (powersetGraph fsa)

> -- |slQ with precomputed PSG
> slPSGQ :: (Ord e, Ord n) => FSA (Set n) e -> Integer
> slPSGQ psg = slTraversal psg (initialsPaths psg) 0

slTraversal is a top-down traversal of the powerset graph which
terminates when either a non-singleton cycle is encountered, or all paths
terminate in (at most) singleton state sets.  In the latter case the
corresponding stringset is $\SL{k}$, where $k$ is the length of the longest
path to a singleton stateset plus $1$, and the function evaluates to $k$.
In the former case it evaluates to $0$.

> slTraversal :: (Ord e, Ord n) =>
>                FSA (Set n) e ->         -- PSG
>                Set(Path (Set n) e) ->   -- Current frontier
>                Integer ->               -- Depth of current frontier
>                Integer
> slTraversal psg ps k
>     | isEmpty ps  =  k + 1
>     | hasCycle    =  0
>     | someSingle  =  slTraversal psg (live `union` ps')
>                      (max k $ depth p + 1)
>     | otherwise   =  slTraversal psg (live `union` ps') k
>     where (p, ps')    =  choose ps
>           exts        =  extensions psg p
>           someSingle  =  flip anyS exts $
>                          maybe False ((1 ==) . isize . nodeLabel) .
>                          endstate
>           live        =  flip keep exts $
>                          maybe False ((1 <) . isize . nodeLabel) .
>                          endstate
>           hasCycle    =  flip anyS live $
>                          maybe False (isIn (stateMultiset p)) .
>                          endstate

\section*{Extracting Forbidden Factors}
The algorithms for gathering Forbidden Initial, Free and Final Factors all
involve a traversal of the powerset graph of a DFA.  In the case that the
corresponding stringset is $\SL$ the traversals are guaranteed to terminate.
If it is not, this is not the case.  In practice, it is often sufficient to
limit the traversals to acyclic paths, but in general that is not the case
either.

The cycles of the PSG, other than cycles of singletons, embody, in a strong
sense, the non-$\SL$ aspects of the stringset; paths including cycles of
non-singletons are witnesses to non-closure under SSC.  In order to isolate
these aspects, it is, in principle, sufficient to explore the sequence of
traversals in which cycles are taken increasingly many times, until the set of
cycles occurring in the paths converges.  To support this, we provide
versions of these traversals which are paramaterized by a bound on the number
of times any state is re-entered during the traversal.


If $\f{psg}$ is the powerset graph of a DFA, then $\f{psgQ}\;\f{psg}$ is the
label of its initial state, i.e., the stateset of the original DFA.  Note that
the there is exactly one initial state of a PSG, so this is just lowering the
type of a singleton set.

> psgQ :: (Ord a, Ord b) => FSA (Set b) a -> State (Set b)
> psgQ = Set.findMin . initials


%% {--------------------------------------------------------------------------}
%%    Forbidden Factors
%%    Forbidden Factors of fsa are the
%%      initial forbidden factors of DFA, free forbidden factors of psGraph,
%%      final forbidden factors of psGraph and forbidden words of DFA.
%%    Initial FF are the labels of acyclic paths from the start state to the
%%      sink state in the minimal but not trimmed DFA.  These are minimal iff
%%      they contain no Free FF.
%%    Free FF are labels of paths Q --> $\emptyset$ in psGraph
%%       These are minimal iff they contain no other Free FF as a suffix
%%    Final FF are labels of paths Q --> state sets in the psGraph other than
%%      $\emptyset$ that are disjoint with the final states of the DFA.
%%      These are minimal iff they contain no other Final FF as a suffix.
%%    Forbidden words are labels of paths from the start state to a
%%      non-accepting state in the DFA that do not include an Initial FF as a
%%      prefix, a Free FF as a substring or a Final FF as a suffix.  For this
%%      set to be bounded, the stringset has to be SL, in which case the bound
%%      is k.

> -- |A convenience-type for declaring collections of  forbidden substrings.
> --  The member types are (lists of) the raw alphabet type (not (Symbol .))
> data ForbiddenSubstrings e
>     = ForbiddenSubstrings
>       { -- |Symbols that actually label transitions
>         attestedUnits      ::  Set e
>         -- |Sequences of symbols that cannot occur as words
>       , forbiddenWords     ::  Set [e]
>         -- |Sequences of symbols that cannot occur initially
>       , forbiddenInitials  ::  Set [e]
>         -- |Sequences of symbols that cannot occur anywhere
>       , forbiddenFrees     ::  Set [e]
>         -- |Sequences of symbols that cannot occur finally
>       , forbiddenFinals    ::  Set [e]
>       }
>     deriving (Eq, Ord, Show, Read)

> -- |A sequence of symbols, possibly annotated with end-markers.
> data TaggedSubstring e = Free [e] | Initial [e] | Final [e] | Word [e]
>                          deriving (Eq, Ord, Read, Show)

> instance Ord e => Container (ForbiddenSubstrings e) (TaggedSubstring e)
>     where empty         =  ForbiddenSubstrings empty empty empty empty empty
>           isEmpty fs    =  isEmpty (forbiddenWords fs)     &&
>                            isEmpty (forbiddenInitials fs)  &&
>                            isEmpty (forbiddenFrees fs)     &&
>                            isEmpty (forbiddenFinals fs)
>           insert (Free [x]) c
>               = c {forbiddenFrees = insert [x] (forbiddenFrees c)}
>           insert (Free x) c
>               = c {forbiddenFrees = insert x (forbiddenFrees c)}
>           insert (Final x) c
>               = c {forbiddenFinals = insert x (forbiddenFinals c)}
>           insert (Initial x) c
>               = c {forbiddenInitials = insert x (forbiddenInitials c)}
>           insert (Word x) c
>               = c {forbiddenWords = insert x (forbiddenWords c)}
>           contains (Free x) c
>               = contains x (forbiddenFrees c)
>           contains (Final x) c
>               = contains x (forbiddenFinals c)
>           contains (Initial x) c
>               = contains x (forbiddenInitials c)
>           contains (Word x) c
>               = contains x (forbiddenWords c)
>           union         =  g union
>           intersection  =  g intersection
>           difference    =  g difference

> g :: Ord e => (Set [e] -> Set [e] -> Set [e]) ->
>      ForbiddenSubstrings e -> ForbiddenSubstrings e -> ForbiddenSubstrings e
> g f a b = ForbiddenSubstrings
>           { attestedUnits    =  attestedUnits a `union` attestedUnits b
>           , forbiddenWords   =  forbiddenWords a `f` forbiddenWords b
>           , forbiddenInitials
>               = forbiddenInitials a `f` forbiddenInitials b
>           , forbiddenFrees   =  forbiddenFrees a `f` forbiddenFrees b
>           , forbiddenFinals  =  forbiddenFinals a `f` forbiddenFinals b
>           }

> -- |The internal structure gathered by the PSG traversals.
> -- This structure does not include attested units or forbidden words,
> -- which are computable separately from the FSA and the forbidden paths
> -- and are not relevant until the optimal set of initial, free and
> -- final forbidden paths are fixed.  Labels of paths are (Symbol e).
> -- Note that, since these are paths in the powerset graph, the states of
> -- each path are labelled by elements of type @Set n@ if @n@ is
> -- the type that labels states in the underlying FSA.
> data ForbiddenPaths n e
>     = ForbiddenPaths
>       { -- |Paths witnessing forbidden initial factors
>         initialPaths :: Set (Path n e)
>         -- |Paths witnessing forbidden free factors
>       , freePaths    :: Set (Path n e)
>         -- |Paths witnessing forbidden final factors
>       , finalPaths   :: Set (Path n e)
>       }
>     deriving (Eq, Ord)

> -- |Convert Set of Paths to Set of sequences of (Symbol e)
> factorsFromPaths :: (Ord e, Ord n) => Set (Path n e) -> Set [Symbol e]
> factorsFromPaths = tmap labels

\begin{itemize}
\item Attested units are alphabet elements that actually occur on a productive
  path of the FSA.  Since the FSA is normalized (by precondition) these are
  just the alphabet elements that occur as symbols as the label of any
  transition.
\item Forbidden words are the sequences of alphabet elements occurring on
  non-accepting paths of the FSA bounded by the max of:
  \begin{itemize}
  \item $k$ if it is non-zero
  \item The max length of the free forbidden paths
  \item The max length of the initial or final forbidden paths plus 1
  \end{itemize}
  Note that if $k$ is non-zero then it is an error to have the other three
  bounds be greater than $k$.  This error is not checked.
\end{itemize}

> -- |Forbidden substrings of the given t'FSA' relative to a domain alphabet
> -- which must include the alphabet of the t'FSA'
> forbiddenSubstringsWithAlphabet :: (Ord e, Ord n, Enum n) =>
>                                    Set e -> FSA n e -> ForbiddenSubstrings e
> forbiddenSubstringsWithAlphabet alph fsa =
>     ForbiddenSubstrings aUns fWds fIns fFrs fFis
>         where aUns  =   unsymbols . tmap edgeLabel $ transitions fsa
>               fPs   =  forbiddenPathsWithAlphabet alph fsa
>               fInS  =  factorsFromPaths $ initialPaths fPs
>               fFrS  =  factorsFromPaths $ freePaths fPs
>               fFiS  =  factorsFromPaths $ finalPaths fPs
>               fWds  =  tmap unsymbols $ fWords fsa (slQ fsa) fInS fFrS fFiS
>               fIns  =  tmap unsymbols fInS
>               fFrs  =  tmap unsymbols fFrS
>               fFis  =  tmap unsymbols fFiS

> -- |Forbidden substrings of the given t'FSA' relative to its alphabet
> forbiddenSubstrings :: (Ord e, Ord n, Enum n) =>
>                        FSA n e -> ForbiddenSubstrings e
> forbiddenSubstrings fsa = forbiddenSubstringsWithAlphabet (alphabet fsa) fsa

> forbiddenPathsWithAlphabet :: (Ord e, Ord n, Enum n) =>
>                               Set e -> FSA n e ->
>                               ForbiddenPaths (Set (Set n)) e
> forbiddenPathsWithAlphabet alph fsa =
>     ForbiddenPaths fInitP fFreeP fFinP
>         where f'      =  fsa {sigma = union alph $ alphabet fsa}
>               psg     =  powersetGraph f'
>               fInitP  =  initialFPs f'
>               fFreeP  =  freeFPsPSG psg
>               fFinP   =  finalFPsPSG psg


%% Forbidden words
%% Labels of acyclic paths from the start state of the DFA that end at a
%% non-accepting state.

%% These could possibly already be barred by a forbidden final factor,
%% but neither an initial or free forbidden factor

%% However, for the nonce we fall back to just filtering rejects as in 2016
%% This just filters the empty string and words with initialFFs as a previc,
%% freeFFs as a substring, or finalFFs as a suffix from rejected words of 
%% length less than or equal to bound

fWords collects the set of words rejected by the given FSA which are not
already excluded by the given initial, free or final FFs that are no longer
than the max of the given bound (typically $k$), one less than the longest
initial or final forbidden factor and two less than the longest free forbidden
factor.

Note that the FFs here are actual forbidden substrings, not forbidden paths

%% Argument order: Initials, Frees, Finals
%% Output: Words

> fWords :: (Ord e, Ord n) => FSA n e -> Integer ->
>           Set [Symbol e] -> Set [Symbol e] -> Set [Symbol e] ->
>           Set [Symbol e]
> fWords fsa bound iFFs frFFs fiFFs
>     = Set.fromList .
>       filter
>       (\wrd ->
>        not (any (`List.isSuffixOf` wrd) (Set.toList fiFFs) ||
>             any (`List.isInfixOf`  wrd) (Set.toList frFFs) ||
>             any (`List.isPrefixOf` wrd) (Set.toList iFFs)
>            )
>       ) . map word . Set.toList $ rejectingPaths fsa bnd
>     where bnd = max (supermax (Set.union iFFs fiFFs) - 1) $
>                 max (supermax frFFs - 2) bound
>           supermax s
>               | Set.null s  =  0
>               | otherwise   =  maximum . map size $ Set.toList s


%% Only the labels (a.k.a. word) component of the resulting paths
%% has any validity, as the states of the reversed FSA have no
%% meaningful connection to those of the input.

> initialFPs :: (Ord a, Ord b, Enum b) =>
>               FSA b a -> Set (Path (Set (Set b)) a)
> initialFPs fsa = tmap (\p -> p {labels = word p}) $
>                    finalFPsPSG (powersetGraph rFSA)
>         where rFSA = renameStates . normalize $ LTK.FSA.reverse fsa

> -- if bound >= 0 then take cycles up to bound+1 times
> -- otherwise take cycles arbitrarily many times
> -- bound should be < 0 only if the psg is the PSG of an FSA that recognizes
> -- an SL stringset, otherwise termination is not guaranteed
> freeFPsPSG :: (Ord e, Ord n, Enum n) =>
>               FSA (Set n) e -> Set (Path (Set (Set n)) e)
> freeFPsPSG psg = gatherFPs psgR (singleton stateQ) initialFront empty
>     where psgR    =  trimRevPSG psg
>           stateQ  =  psgQ psg
>           initialFront
>               | contains (State empty) $ states psg
>                     = singleton $
>                       Path
>                       { labels    =  empty
>                       , endstate  =  Just . State $ singleton empty
>                       , stateMultiset
>                             = singleton . State $ singleton empty
>                       , depth     =  0
>                       }
>               | otherwise = empty


%% finalFPs
%%  graph: reversed powerset graph
%%    less: in-edges to $\emptyset$
%%          --- path necessarily would include ff as prefix
%%          out-edges from Q
%%          --- path necessarily includes final ff as suffix
%%  goals: {State Q}
%%  initial states:  {s $\in$ (states psg) |
%%                     s /= $\emptyset$ and
%%                     s $\cap$ (finals fsa) == $\emptyset$}
%%                   This is complement of initial states of reversed psGraph
%% if bound >= 0 then take cycles up to bound+1 times
%% otherwise take cycles arbitrarily many times
%% bound should be < 0 only if the psg is the PSG of an FSA that recognizes an
%%   SL stringset, otherwise termination is not guaranteed

> finalFPsPSG :: (Ord e, Ord n, Enum n) =>
>                  FSA (Set n) e -> Set (Path (Set (Set n)) e)
> finalFPsPSG psg = gatherFPs psgR (singleton stateQ) front0 empty
>     where psgR    =  trimRevPSG psg
>           stateQ  =  psgQ psg
>           front0  =  singleton $
>                      Path
>                      { labels = empty
>                      , endstate = pure nonFin
>                      , stateMultiset = singleton nonFin
>                      , depth = 0
>                      }
>           nonFin  =  fmap Set.fromList         .
>                      sequence . Set.toList     .
>                      difference (states psgR)  .
>                      insert (State empty) $ initials psgR

%% trimRevPSG psg is reverse of
%%    (psg with in-edges to Q and out-edges from $\emptyset$ removed)
%%    note that such edges are necessarily self-edges

> trimRevPSG :: (Ord e, Ord n, Enum n) => FSA (Set n) e -> FSA (Set n) e
> trimRevPSG psg
>     = LTK.FSA.reverse $
>       psg
>       { transitions
>             = keep
>               (both
>                ((/= psgQ psg) . destination)
>                ((/= State empty) . source)) $
>               transitions psg
>       }

%%  Breadth-first traversal of graph
%%   Returns list of strings labeling paths from initial frontier to a goal
%%    that are:  acyclic other than, if bound < 0, cycles of singletons
%%               & do not include shorter such path as a suffix
%% if bound is >= 0 then follow cycles up to bound+1 times
%% ow follow singleton cycles which, by assumption, will be the only cycles
%% This is guaranteed to terminate if (and only if) bound >=0 or graph is the
%%   reversed PSG of an FSA that recognizes an SL stringset.
%% The k in the comments is an iteration counter and is the length of the FPs
%%   being in a given pass 

> gatherFPs :: (Ord e, Ord n, Enum n) =>
>           FSA (Set n) e -> Set (State (Set n)) -> [Path (Set (Set n)) e] ->
>           Set (Path (Set (Set n)) e) -> Set (Path (Set (Set n)) e)
> gatherFPs psg goal front fps
>     | isEmpty front = fps
>     | otherwise = gatherFPs psg goal nextFront (nextFPs `union` fps)
>     where (nextFront, nextFPs)
>               = passK goal
>                 (Set.toList $
>                  foldr (union . acceptableExtensions) empty front)
>                 empty empty
>           acceptableExtensions = nondeterministicAcyclicExtensions psg


%% passK scans extensions of kth frontier for length k FPs 
%%  paths with label of a known k-FP are dropped
%%  paths that end at a goal are added to FPs and paths with same label
%%      already in front k+1 are stripped
%% Returns (front k+1, k-FPs)
%% This k is not that k

> passK :: (Ord e, Ord n, Enum n) =>
>          Set (State (Set n)) -> [Path (Set (Set n)) e] ->
>          [Path (Set (Set n)) e] -> Set (Path (Set (Set n)) e) ->
>          ( [Path (Set (Set n)) e]
>          , Set (Path (Set (Set n)) e) )
> passK _ [] front fps = (front, fps)
> passK goals (p:ps) front fps
>     | contains (labels p) (tmap labels fps)
>         = passK goals ps front fps
>     | maybe False (anyS (isIn goals . State) . nodeLabel) $ endstate p
>         = passK goals ps
>            (keep
>               (isNotIn (insert (labels p) $ tmap labels fps) . labels)
>               front) $ insert p fps
>     | otherwise = passK goals ps (p:front) fps


%% verification 

> buildFSAsFromFFs :: (NFData e, Ord e) => ForbiddenSubstrings e ->
>                     ( Set e            -- alphabet
>                     , [FSA Integer e]  -- words
>                     , [FSA Integer e]  -- initials
>                     , [FSA Integer e]  -- free
>                     , [FSA Integer e]  -- finals
>                     )
> buildFSAsFromFFs fs = (alphs, ws, is, frs, fis)
>     where alphs        =  attestedUnits fs
>           f h t        =  buildLiteral alphs . forbidden .
>                           (\x -> Substring x h t) . tmap singleton
>           buildHT h t  =  tmap (f h t) . Set.toList
>           ws           =  buildHT True   True   (forbiddenWords fs)
>           is           =  buildHT True   False  (forbiddenInitials fs)
>           frs          =  buildHT False  False  (forbiddenFrees fs)
>           fis          =  buildHT False  True   (forbiddenFinals fs)

%% build FSA from FSAs

> combineFSAs :: (NFData e, Ord e) => ( Set e            -- alphabet
>                                     , [FSA Integer e]  -- words
>                                     , [FSA Integer e]  -- initials
>                                     , [FSA Integer e]  -- free
>                                     , [FSA Integer e]  -- finals
>                                     ) -> FSA Integer e
> combineFSAs (alphs,ws,is,frs,fis)
>     = flatIntersection $ totalWithAlphabet alphs : concat [ws, is, frs, fis]

%% build FSA from forbidden factors
%% Since this uses renameStates the State type of the result will be Integer
%% This really needs to be as strict as possible, which I hope it isn't

> -- |Create an t'FSA' satisfying the conditions imposed by the
> -- given sets of forbidden substrings.
> buildFSA :: (NFData e, Ord e) => ForbiddenSubstrings e -> FSA Integer e
> buildFSA = combineFSAs . buildFSAsFromFFs

\end{document}
