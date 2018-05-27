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
true in the definition of \texttt{Path} and {\texttt ForbiddenSubstrings}.  At others, such as the definition of\texttt{ForbiddenPaths} it is bound to
\texttt{Symbol e}.  This creates conflicts.

Functions for
\begin{itemize}
\item Determining if the stringset recongized by an automaton is $\SL$ and, if
  so, determining $k$.
\item Extracting the sets of Forbidden Initial, Free and Final Factors,
  Forbidden Units and Forbidden Words that (partially) define that stringset.
\item Generating an automaton that provides an $\SL$ approximation of the
  stringset recognized by an automaton.
\item andere Dinge
\end{itemize}

Forbidden factors, units and words are explained in Rogers and Lambert,
MoL'17 as is the notion of an $\SL$ approximation of a non-$\SL$ stringset. 


> {-# OPTIONS_HADDOCK show-extensions #-}
> {-# Language
>   MultiParamTypeClasses
>   #-}
> {-|
> Module    : ExtractSL
> Copyright : (c) 2017-2018 Jim Rogers and Dakotah Lambert
> License   : BSD-style, see LICENSE
> 
> Find forbidden substrings of an automaton.
> -}
> module ExtractSL ( ForbiddenSubstrings(..)
>                  , ForbiddenPaths(..)
>                  , TaggedSubstring(..)
>                  -- *Extracting forbidden substrings
>                  , factorsFromPaths
>                  , forbiddenSubstrings
>                  , forbiddenPaths
>                  , forbiddenPathsWithBound
>                  -- *Building automata
>                  , buildFSA
>                  -- *Determining SL
>                  , isSL
>                  , slQ
>                  -- *...with precomputed PSG
>                  , isSLPSG
>                  , slPSGQ
>                  ) where

> import FSA
> import Traversals  -- for initialsPaths, rejectingPaths
> import Factors

> import Control.DeepSeq
> import Data.Set (Set)
> import qualified Data.Set as Set
> import qualified Data.List as List
> import qualified Data.Map as Map

\section*{Determining $\SL{k}$}
This is an implementation of the powerset graph based algorithm given in
Edlefsen, et al., MCURCSM'08 and sketched in Rogers and Lambert, MoL'17.
Since we are often working with the full powerset graph anyway, we do not use
the polynomial-time pair-graph version.


> -- |Returns @True@ iff the stringset represented by the given 'FSA'
> -- is Strictly Local, that is,
> -- if it satisfies Suffix-Substition Closure for
> -- some specific factor size \(k\).
> isSL :: (Ord e, Ord n) => FSA n e -> Bool
> isSL = (> 0) . slQ

> -- |Returns the smallest factor size for which
> -- the stringset represented by the given 'FSA'
> -- satisfies Suffix-Substitution Closure,
> -- or @0@ if there is no such \(k\).
> slQ :: (Ord e, Ord n) => FSA n e -> Integer
> slQ fsa = slPSGQ (powersetGraph fsa)

> -- |isSL with precomputed PSG
> isSLPSG :: (Ord e, Ord n) => FSA (Set n) e -> Bool
> isSLPSG = (>0) . slPSGQ

> -- |slQ with precomputed PSG
> slPSGQ :: (Ord e, Ord n) => FSA (Set n) e -> Integer
> slPSGQ psg = slTraversal psg (initialsPaths psg) 0

slTraversal is a top-down traversal of the powerset graph which
terminates when either a non-singleton cycle is encountered, or all paths
terminate in (at most) singleton state sets.  In the latter case the
corresponding stringset is $\SL{k}$, where $k$ is the length of the longest path
to a singleton stateset plus $1$, and the function evaluates to $k$.  In the
former case it evaluates to $0$. 

> slTraversal :: (Ord e, Ord n) => 
>                   FSA (Set n) e               -- PSG
>                       -> Set(Path (Set n) e)  -- Current frontier
>                       -> Integer              -- Depth of current frontier
>                       -> Integer
> slTraversal psg ps k
>     | (Set.null ps) = k + 1
>     | cycle = 0
>     | someSingle = slTraversal psg (union live restps) (max k ((depth thisp)+1))
>     | otherwise = slTraversal psg (union live restps) k
>     where
>       (thisp,restps) = choose ps
>       exts = (extensions psg thisp)
>       someSingle  = anyS
>                     (maybe False
>                      ((1 ==) . Set.size . nodeLabel) . endstate)
>                     exts
>       live = Set.filter
>              (maybe False
>               ((1 <) . Set.size . nodeLabel) . endstate)
>              exts
>       cycle = anyS (maybe False (isIn (stateMultiset thisp)) . endstate) live

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


%% {---------------------------------------------------------------------------}
%%    Forbidden Factors
%%    Forbidden Factors of fsa are the forbidden units of psGraph, 
%%      initial forbidden factors of DFA, free forbidden factors of psGraph,
%%      final forbidden factors of psGraph and forbidden words of DFA.
%%    Forbidden units are elts of alphabet that do not label any edge from Q
%%     in psGraph
%%     - Since sigma forbidden iff no edge q1 -sigma-> q2 for any q1, q2 in DFA
%%         iff no edge Q-sigma->S  for any S in psGraph
%%    Initial FF are the labels of acyclic paths from the start state to the 
%%      sink state in the minimal but not trimmed DFA.  These are minimal iff 
%%      they contain no Free FF.
%%    Free FF are labels of paths Q --> $\emptyset$ in psGraph
%%       These are minimal iff they contain no other Free FF as a suffix
%%    Final FF are labels of paths Q --> state sets in the psGraph other than
%%      $\emptyset$ that are  
%%      disjoint with the final states of the DFA.  These are minimal iff they 
%%      contain no other Final FF as a suffix.
%%    Forbidden words are labels of paths from the start state to a non-accepting 
%%      state in the DFA that do not include an Initial FF as a prefix, a Free FF 
%%      as a substring or a Final FF as a suffix.  For this set to be bounded, 
%%      the stringset has to be SL, in which case the bound is k.

%%    Since the bare forbiddenFactors generates unitFFs wrt the defaultAlphabet 
%%     defined in Factors.hs, which is of type Set(String), its applicable only 
%%     to FSA String b.


> -- |A convenience-type for declaring collections of  forbidden substrings.
> --  The member types are (lists of) the raw alphabet type (not (Symbol .))
> data ForbiddenSubstrings e = 
>     ForbiddenSubstrings { -- |Symbols that actually label transitions
>                           attestedUnits  ::   Set e
>                           -- |Symbols of alphabet of FSA - attestedUnits
>                         , forbiddenUnits ::   Set e 
>                           -- |Sequences of symbols that cannot occur as words
>                         , forbiddenWords ::   Set [e]
>                           -- |Sequences of symbols that cannot occur initially
>                         , forbiddenInitials ::   Set [e]
>                           -- |Sequences of symbols that cannot occur anywhere
>                         , forbiddenFrees          ::   Set [e]
>                           -- |Sequences of symbols that cannot occur finally
>                         , forbiddenFinals         ::   Set [e]
>                         }
>     deriving (Eq, Ord, Show, Read)

> data TaggedSubstring e = Free [e] | Initial [e] | Final [e] | Word [e]
>                          deriving (Eq, Ord, Read, Show)

> instance Ord e =>
>     Container (ForbiddenSubstrings e) (TaggedSubstring e) where
>         empty = ForbiddenSubstrings empty empty empty empty empty empty
>         isEmpty fs = isEmpty (forbiddenWords fs) &&
>                      isEmpty (forbiddenInitials fs) &&
>                      isEmpty (forbiddenFrees fs) &&
>                      isEmpty (forbiddenFinals fs)
>         insert (Free [x]) c = c {
>                                 forbiddenUnits = insert x (forbiddenUnits c)
>                               , forbiddenFrees = insert [x] (forbiddenFrees c)
>                               }
>         insert (Free x) c = c {
>                               forbiddenFrees = insert x (forbiddenFrees c)
>                             }
>         insert (Final x) c = c {
>                                forbiddenFinals = insert x (forbiddenFinals c)
>                              }
>         insert (Initial x) c = c {
>                                  forbiddenInitials = insert x (forbiddenInitials c)
>                                }
>         insert (Word x) c = c {
>                               forbiddenWords = insert x (forbiddenWords c)
>                             }
>         contains (Free x) c = contains x (forbiddenFrees c)
>         contains (Final x) c = contains x (forbiddenFinals c)
>         contains (Initial x) c = contains x (forbiddenInitials c)
>         contains (Word x) c = contains x (forbiddenWords c)
>         union = g union union
>         intersection = g intersection intersection
>         difference = g difference difference

> g :: Ord e =>
>      (Set e -> Set e -> Set e)
>   -> (Set [e] -> Set [e] -> Set [e])
>   -> ForbiddenSubstrings e -> ForbiddenSubstrings e
>   -> ForbiddenSubstrings e
> g fU f a b = ForbiddenSubstrings {
>                attestedUnits = union (attestedUnits a) (attestedUnits b)
>              , forbiddenUnits = fU (forbiddenUnits a) (forbiddenUnits b)
>              , forbiddenWords = f (forbiddenWords a) (forbiddenWords b)
>              , forbiddenInitials = f
>                                    (forbiddenInitials a)
>                                    (forbiddenInitials b)
>              , forbiddenFrees = f (forbiddenFrees a) (forbiddenFrees b)
>              , forbiddenFinals = f (forbiddenFinals a) (forbiddenFinals b)
>              }

> -- |forbiddenUnits relative to a domain alphabet
> forbiddenUnitsWithAlphabet :: (Ord e) => 
>                                 Set e -> ForbiddenSubstrings e -> Set e
> forbiddenUnitsWithAlphabet a fs = difference a (attestedUnits fs)


ForbiddenPaths are the internal structure gathered by the PSG traversals.
This structure does not include attested units or forbidden units or words,
which are computable separately from the FSA and the forbidden paths and are
not relevant until the optimal set of initial, free and final forbidden paths
are fixed.  Labels of paths are (Symbol e).  Note that since these are paths in the powerset graph `n' here is `Set n' for the `n' of the FSA.

> data ForbiddenPaths n e = 
>           ForbiddenPaths { -- |Paths witnessing forbidden initial factors
>                             initialPaths :: Set (Path n e)
>                             -- |Paths witnessing forbidden free factors
>                           , freePaths    :: Set (Path n e)
>                             -- |Paths witnessing forbidden final factors
>                           , finalPaths   :: Set (Path n e)
>                          }
>           deriving (Eq, Ord)
>                                   
> -- |Convert Set of Paths to Set of sequences of (Symbol e)
> factorsFromPaths :: (Ord e, Ord n) =>
>                       Set (Path n e) -> Set [Symbol e]
> factorsFromPaths = tmap labels

> -- |Convert Set of Paths to Set of Substrings of alphabet type
> stringsFromPaths :: (Ord e, Ord n) =>
>                      Set(Path n e) -> Set [e]
> stringsFromPaths = tmap (unsymbols . labels)

> -- |Convert path to Set of states visited by path
> pathToStateSet :: (Ord a, Ord b) => Path b a -> Set (State b)
> pathToStateSet = setFromMultiset . stateMultiset

> -- visitedStateSets paths is the set of sets of states visited in each path
> --  in paths
> visitedStateSets :: (Ord a, Ord b) => Set (Path b a) -> Set (Set (State b))
> visitedStateSets = tmap pathToStateSet

> -- a tractable version of unsymbol
> emancipate :: (Symbol e) -> e
> emancipate (Symbol x) = x

\begin{itemize}
\item Attested units are alphabet elements that actually occur on a productive  
  path of the FSA.  Since the FSA is normalized (by precondition) these are  
  just the alphabet elements that occur as symbols as the label of any  
  transition. 
\item Forbidden units are those elts of the alphabet that are not attested. 
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

> -- |Forbidden substrings of the given 'FSA' relative to a domain alphabet
> -- which must include the alphabet of the 'FSA'
> forbiddenSubstringsWithAlphabet :: (Ord e, Ord n, Enum n) =>
>                                    Set e
>                                 -> FSA n e
>                                 -> ForbiddenSubstrings e
> forbiddenSubstringsWithAlphabet alph fsa =
>     ForbiddenSubstrings aUns fUns fWds fIns fFrs fFis
>         where
>           aUns = tmap (emancipate . edgeLabel) (transitions fsa)
>           fUns = alph `difference` aUns
>           fPs = forbiddenNDPathsWithAlphabet alph fsa
>           fInSym = factorsFromPaths (initialPaths fPs)
>           fFrSym = factorsFromPaths (freePaths fPs)
>           fFiSym = factorsFromPaths (finalPaths fPs)
>           fWds = tmap unsymbols 
>                       (fWords fsa (slQ fsa) fInSym fFrSym fFiSym)
>           fIns = tmap unsymbols fInSym
>           fFrs = tmap unsymbols fFrSym
>           fFis = tmap unsymbols fFiSym

> -- |Forbidden substrings of the given 'FSA' relative to its alphabet
> forbiddenSubstrings :: (Ord e, Ord n, Enum n) =>
>                        FSA n e
>                     -> ForbiddenSubstrings e
> forbiddenSubstrings fsa = forbiddenSubstringsWithAlphabet (alphabet fsa) fsa

> -- |Paths representing the forbidden substrings of the given 'FSA'.
> --   the alphabet of which must be a subset of the provided alphabet.
> forbiddenPathsWithAlphabet:: (Ord e, Ord n, Enum n) =>
>                                Set e
>                             -> FSA n e
>                             -> ForbiddenPaths (Set n) e
> forbiddenPathsWithAlphabet alph fsa =
>     ForbiddenPaths fInitP fFreeP fFinP
>     where
>        psg = powersetGraph fsa
>        k = slPSGQ psg
>        fInitP = initialFPs fsa (max 0 (k-1))
>        fFreeP = freeFPsPSG psg k
>        fFinP = finalFPsPSG psg (max 0 (k-1))


> -- |Paths representing forbidden substrings of the given 'FSA'.
> forbiddenPaths:: (Ord n, Enum n, Ord e) =>
>                  FSA n e ->
>                  ForbiddenPaths (Set n) e
> forbiddenPaths fsa = forbiddenPathsWithAlphabet (alphabet fsa) fsa

> forbiddenNDPathsWithAlphabet :: (Ord e, Ord n, Enum n) =>
>                                 Set e
>                              -> FSA n e
>                              -> ForbiddenPaths (Set (Set n)) e
> forbiddenNDPathsWithAlphabet alph fsa =
>     ForbiddenPaths fInitP fFreeP fFinP
>         where psg     =  powersetGraph fsa
>               fInitP  =  initialNDFPs fsa
>               fFreeP  =  freeNDFPsPSG psg
>               fFinP   =  finalNDFPsPSG psg

> forbiddenNDPaths :: (Ord e, Ord n, Enum n) =>
>                     FSA n e -> ForbiddenPaths (Set (Set n)) e
> forbiddenNDPaths fsa = forbiddenNDPathsWithAlphabet (alphabet fsa) fsa

%% Bounded search for forbidden factors.

%% In gathering initial, free and final forbidden factors cycles in the psGraph
%% are taken up to bound many times.  If bound is negative then cycles are taken
%% arbitrarily many times and these searches are guaranteed to terminate only if
%% the psGraph represents a DFA that recognizes an SL stringset.

%% In gathering forbidden words, the maximum length of word is bound.  If bound
%% is negative, it is computed to be slQ-2.  If either bound or slQ-2 is less than
%% 0, no forbidden words will be gathered.  If either is equal to 0 then, at
%% most, \epsilon will be gathered.



> -- |The forbidden paths of the given 'FSA',
> -- the alphabet of which must be a subset of the
> -- provided alphabet.  Takes at most bound-1 many
> -- iterations of each cycle in the powerset graph.
> forbiddenPathsWithAlphabetWithBound :: (Ord e, Ord n, Enum n) =>
>                                         Set e   -- alphabet
>                                      -> Integer -- bound on iterations of cycles
>                                      -> FSA n e
>                                      -> ForbiddenPaths (Set n) e
> forbiddenPathsWithAlphabetWithBound alph bnd fsa = 
>     ForbiddenPaths fInitP fFreeP fFinP
> -- (uFFs, fWs, iFFs, frFFs, fiFFs)
>     where
>        psg = powersetGraph fsa
>        fInitP = initialFPs fsa bnd
>        fFreeP = freeFPsPSG psg bnd
>        fFinP = finalFPsPSG psg bnd

> -- |The forbidden substrings of the given 'FSA'.
> -- Takes at most bound-1 many iterations of each
> -- cycle in the powerset graph.
> forbiddenPathsWithBound :: (Ord n, Enum n, Ord e) =>
>                            Integer -- bound
>                         -> FSA n e
>                         -> ForbiddenPaths (Set n) e
> forbiddenPathsWithBound b fsa =
>     forbiddenPathsWithAlphabetWithBound (alphabet fsa) b fsa

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

> fWords :: (Ord e, Ord n) => FSA n e
>                             -> Integer             -- bound
>                             -> Set.Set([Symbol e]) -- initialFFs
>                             -> Set.Set([Symbol e]) -- freeFFs
>                             -> Set.Set([Symbol e]) -- finalFFs
>                             -> Set.Set([Symbol e])
> fWords fsa bound iFFs frFFs fiFFs =
>     Set.fromList
>            (filter
>             (\wrd -> not ((any (\x -> (List.isSuffixOf x wrd)) (Set.toList fiFFs))
>                           ||
>                           (any (\x -> (List.isInfixOf x wrd)) (Set.toList frFFs))
>                           ||
>                           (any (\x -> (List.isPrefixOf x wrd)) (Set.toList iFFs))) )
>             (map ((Prelude.reverse) . labels)
>                      (Set.toList (rejectingPaths fsa bnd)) ) )
>         where bnd =
>                   max ((supermax (Set.union iFFs fiFFs)) - 1)
>                       (max ((supermax frFFs)-2)
>                            bound)
>               supermax :: Set.Set [a] -> Integer
>               supermax s
>                   | (Set.null s) = 0
>                   | otherwise = 
>                       (maximum . map size) (Set.toList s)

> initialFPs :: (Ord a, Ord b, Enum b) =>
>               FSA b a
>            -> Integer                 -- k
>            -> Set(Path(Set b) a)
> initialFPs fsa bound = tmap (\p -> p {labels = word p}) $ finalFPs rFSA bound
> -- hmmm. can't really just reverse labels, can we?  Does endstate matter?
> -- if it is potentially so, then it should be (states rFSA), but these are not
> --   related in any meaningful way with the initials of fsa
>         where rFSA = renameStates . normalize $ FSA.reverse fsa

> initialNDFPs :: (Ord a, Ord b, Enum b) =>
>                 FSA b a
>              -> Set (Path (Set (Set b)) a)
> initialNDFPs fsa = tmap (\p -> p {labels = word p}) $
>                    finalNDFPsPSG (powersetGraph rFSA)
> -- See note in initialFPs
>         where rFSA = renameStates . normalize $ FSA.reverse fsa

> freeFPs :: (Ord e, Ord n, Enum n) =>
>            (FSA n e) -> Integer -> Set(Path(Set n) e)
> freeFPs fsa bound = freeFPsPSG (powersetGraph fsa) bound

> -- if bound >= 0 then take cycles up to bound+1 times
> -- otherwise take cycles arbitrarily many times
> -- bound should be < 0 only if the psg is the PSG of an FSA that recognizes an
> --   SL stringset, otherwise termination is not guaranteed
> freeFPsPSG :: (Ord e, Ord n, Enum n) => (FSA (Set n) e) -> Integer ->
>                                  Set(Path(Set n) e)
> freeFPsPSG psg bound
>     = gatherFPs psgR bound (Set.singleton stateQ) initialFront empty
>     where 
>       psgR = (trimRevPSG psg)
>       stateQ = psgQ psg
>       initialFront
>           | (contains stateEmpty (states psg))
>               =  singleton
>                  (Path empty (pure stateEmpty) (singleton stateEmpty) 0)
>           | otherwise = empty
>       stateEmpty = (State empty)

> -- if bound >= 0 then take cycles up to bound+1 times
> -- otherwise take cycles arbitrarily many times
> -- bound should be < 0 only if the psg is the PSG of an FSA that recognizes an
> --   SL stringset, otherwise termination is not guaranteed
> freeNDFPsPSG :: (Ord e, Ord n, Enum n) =>
>                 (FSA (Set n) e)
>              -> Set (Path(Set (Set n)) e)
> freeNDFPsPSG psg
>     = gatherNDFPs psgR (Set.singleton stateQ) initialFront empty
>     where 
>       psgR = (trimRevPSG psg)
>       stateQ = psgQ psg
>       initialFront
>           | (contains (State empty) (states psg))
>               =  singleton
>                  (Path {
>                     labels = empty
>                   , endstate = pure (State (singleton empty))
>                   , stateMultiset = singleton (State (singleton (empty)))
>                   , depth = 0
>                   })
>           | otherwise = empty


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

> finalFPs :: (Ord e, Ord n, Enum n) => (FSA n e)
>                                -> Integer                 -- bound
>                                -> Set (Path (Set n) e)
> finalFPs fsa bound = finalFPsPSG (powersetGraph fsa) bound

> finalFPsPSG :: (Ord e, Ord n, Enum n) =>
>                (FSA (Set n) e) -> Integer
>                                -> Set (Path (Set n) e)
> finalFPsPSG psg bound
>     = gatherFPs psgR bound (singleton stateQ) initialFront empty
>     where 
>       psgR = (trimRevPSG psg)
>       stateQ = psgQ psg
>       initialFront = fromCollapsible $
>                      tmap
>                      (\s -> Path empty (pure s) (singleton s) 0)
>                      (difference
>                       (states psgR)
>                       (insert (State empty) (initials psgR)))


%% [DL, 19 May 2018]:
%% I don't know if the initial frontier should consist of
%% a single stateset containing all non-final states
%% or several singleton statesets.
%% Right now, I am going with the former.

> finalNDFPsPSG :: (Ord e, Ord n, Enum n) =>
>                  (FSA (Set n) e)
>               -> Set (Path (Set (Set n)) e)
> finalNDFPsPSG psg
>     = gatherNDFPs psgR (singleton stateQ) initialFront empty
>     where 
>       psgR = (trimRevPSG psg)
>       stateQ = psgQ psg
>       initialFront = singleton $
>                      Path {
>                        labels = empty
>                      , endstate = pure nonFinalsState
>                      , stateMultiset = singleton nonFinalsState
>                      , depth = 0
>                      }
>       nonFinalsState = fmap Set.fromList         .
>                        sequence . Set.toList     .
>                        difference (states psgR)  $
>                        insert (State empty) (initials psgR)

%% trimRevPSG psg is reverse of
%%    (psg with in-edges to Q and out-edges from $\emptyset$ removed)
%%    note that such edges are necessarily self-edges

> trimRevPSG :: (Ord e, Ord n, Enum n) => FSA (Set n) e -> FSA (Set n) e
> trimRevPSG psg = FSA.reverse $
>                  psg {
>                    transitions = keep
>                                  (\t -> (destination t /= psgQ psg
>                                         && source t /= State empty))
>                                  (transitions psg)
>                  }

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


> gatherFPs :: (Ord e, Ord n, Enum n) => FSA (Set n) e -- graph (psGraph based)
>                   -> Integer                 -- bound
>                   -> Set (State (Set n))     -- set of goal states
>                   -> [Path (Set n) e]        -- frontier
>                   -> Set (Path (Set n) e)    -- FPs so far
>                   -> Set (Path (Set n) e)    -- FPs
> gatherFPs psg bound goal [] fps = fps
> gatherFPs psg bound goal front fps
>     = gatherFPs psg bound goal nextFront (union nextFPs fps)
>     where
>       (nextFront,nextFPs)           -- (frontier k+1, k-FPs)
>           = passK goal                   
>                   (List.foldl' union empty (map acceptableExtensions front) )
>                                     -- extensions of front k
>                   empty empty       -- initial front & FPs for pass k
>       acceptableExtensions p
>           | (bound < 0) = Set.toList (extensions psg p)
>           | otherwise = Set.toList (boundedCycleExtensions psg bound p)

> gatherNDFPs :: (Ord e, Ord n, Enum n) =>
>                FSA (Set n) e               -- graph (psGraph based)
>             -> Set (State (Set n))         -- set of goal states
>             -> [Path (Set (Set n)) e]      -- frontier
>             -> Set (Path (Set (Set n)) e)  -- FPs so far
>             -> Set (Path (Set (Set n)) e)  -- FPs
> gatherNDFPs psg goal front fps
>     | isEmpty front = fps
>     | otherwise = gatherNDFPs psg goal nextFront (union nextFPs fps)
>     where
>       (nextFront,nextFPs)           -- (frontier k+1, k-FPs)
>           = nondeterministicPassK goal
>             (unionAll (map acceptableExtensions front)) -- extensions of front k
>             empty empty       -- initial front & FPs for pass k
>       acceptableExtensions = Set.toList . nondeterministicAcyclicExtensions psg


%% passK scans extensions of kth frontier for length k FPs 
%%  paths with label of a known k-FP are dropped
%%  paths that end at a goal are added to FPs and paths with same label
%%      already in front k+1 are stripped
%% Returns (front k+1, k-FPs)
%% This k is not that k


> passK :: (Ord e, Ord n, Enum n) => Set (State (Set n))      -- goal states
>                               -> [Path (Set n) e]      -- extensions of front k
>                               -> [Path (Set n) e]      -- front k+1 so far
>                               -> Set (Path (Set n) e)  -- k-FPs so far
>                               -> ([Path (Set n) e], Set (Path (Set n) e))
>                                                  -- (front, k-FPs)
> passK goals [] front fps = (front, fps)
> passK goals (p:ps) front fps 
>     | contains (labels p) (tmap labels fps)    -- extends known fp
>         = passK goals ps front fps
>     | maybe False (isIn goals) (endstate p)    -- new fp
>         = passK goals ps
>            (keep
>               ((\x -> doesNotContain (labels x)
>                       (insert (labels p) (tmap labels fps))))
>               front)
>            (insert p fps)
>     | otherwise = passK goals ps (p:front) fps -- in frontier k+1

> nondeterministicPassK :: (Ord e, Ord n, Enum n) =>
>                          Set (State (Set n))           -- goal states
>                       -> [Path (Set (Set n)) e]        -- extensions of front k
>                       -> [Path (Set (Set n)) e]        -- front k+1 so far
>                       -> Set (Path (Set (Set n)) e)    -- k-FPs so far
>                       -> ([Path (Set (Set n)) e],
>                           Set (Path (Set (Set n)) e))  -- (front, k-FPs)
> nondeterministicPassK goals [] front fps = (front, fps)
> nondeterministicPassK goals (p:ps) front fps
>     | contains (labels p) (tmap labels fps)    -- extends known fp
>         = nondeterministicPassK goals ps front fps
>     | maybe False (any (isIn goals . State) . nodeLabel) (endstate p) -- new fp
>         = nondeterministicPassK goals ps
>            (keep
>               ((\x -> doesNotContain (labels x)
>                       (insert (labels p) (tmap labels fps))))
>               front)
>            (insert p fps)
>     | otherwise = nondeterministicPassK
>                   goals ps (p:front) fps -- in frontier k+1


%% verification 

buildFSAs FFs -> tuple of lists of FSAs for each FF


> buildFSAs :: (NFData e, Ord e)
>              => FSA Integer e
>              -> ( Set e           -- alphabet
>                 , [FSA Integer e] -- words
>                 , [FSA Integer e] -- initials
>                 , [FSA Integer e] -- free
>                 , [FSA Integer e] -- finals
>                 )
> buildFSAs = buildFSAsFromFFs . forbiddenSubstrings

> buildFSAsFromFFs :: (NFData e, Ord e) =>
>                     ForbiddenSubstrings e
>                  -> ( Set e    -- alphabet
>                     , [FSA Integer e]  -- words
>                     , [FSA Integer e]  -- initials
>                     , [FSA Integer e]  -- free
>                     , [FSA Integer e]  -- finals
>                     )
> buildFSAsFromFFs fs = (alphs, was, ias, fras, fias)
>     where
>       alphs = attestedUnits fs
>       f hanchor tanchor = (buildLiteral alphs) . forbidden .
>               (\x -> Substring x hanchor tanchor)        .
>               tmap singleton 
>       build hanchor tanchor = tmap (f hanchor tanchor) . Set.toList
>       was = build True True (forbiddenWords fs)
>       ias = build True False (forbiddenInitials fs)
>       fras = build False False (forbiddenFrees fs)
>       fias = build False True (forbiddenFinals fs)

%% build FSA from FSAs

> combineFSAs :: (NFData e, Ord e) =>
>                (Set e,    -- alphabet
>                 [FSA Integer e],  -- words
>                 [FSA Integer e],  -- initials
>                 [FSA Integer e],  -- free
>                 [FSA Integer e] ) -- finals
>                 -> FSA Integer e
> combineFSAs (alphs,was,ias,fras,fias) =
>     flatIntersection
>     (totalWithAlphabet alphs : concat [was, ias, fras, fias])

%% build FSA from forbidden factors
%% Since this uses renameStates the State type of the result will be Integer
%% This really needs to be as strict as possible, which I hope it isn't

> -- |Create an 'FSA' satisfying the conditions imposed by the
> -- given sets of forbidden substrings.
> buildFSA :: (NFData e, Ord e) => (ForbiddenSubstrings e) -> FSA Integer e
> buildFSA = combineFSAs . buildFSAsFromFFs

\end{document}
