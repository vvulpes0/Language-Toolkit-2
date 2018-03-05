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
\title{SLFactors}
\date{}

\begin{document}

\maketitle\thispagestyle{empty}
 Functions for retrieving forbidden factors from automata for SLk
  stringsets. 

> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : ExtractSL
> Copyright : (c) 2017-2018 Jim Rogers and Dakotah Lambert
> License   : BSD-style, see LICENSE
> 
> Find forbidden substrings of an automaton.
> -}
> module ExtractSL ( ForbiddenSubstrings
>                  , ForbiddenPaths
>                  -- *Extracting forbidden substrings
>                  , factorsFromPaths
>                  , forbiddenPaths
>                  , forbiddenPathsWithBound
>                  -- *Building automata
>                  , buildFSA
>                  -- *Determining SL
>                  , isSL
>                  , slQ
>                  ) where

> import FSA
> import Traversals
> import Factors
> 
> import Control.DeepSeq
> import Data.Set (Set)
> import qualified Data.Set as Set
> import qualified Data.List as List
> import qualified Data.Map as Map

> -- |Returns @True@ iff the stringset represented by the given 'FSA'
> -- is Strictly Local, that is,
> -- if it satisfies Suffix-Substition Closure for
> -- some specific window size \(k\).
> isSL :: (Ord e, Ord n) => FSA n e -> Bool
> isSL = (> 0) . slQ

> -- |Returns the smallest window size for which
> -- the stringset represented by the given 'FSA'
> -- satisfies Suffix-Substitution Closure,
> -- or @0@ if there is no such \(k\).
> slQ :: (Ord e, Ord n) => FSA n e -> Integer
> slQ fsa = slPSGQ (powersetGraph fsa)

> -- Assumes states are (Set n)
> -- in improved-semantics states are now (Set Int) ?????
> slPSGQ :: (Ord e, Ord n) => FSA (Set n) e -> Integer
> slPSGQ sm = slTraversal sm (initialsPaths sm) 0
> 
> slTraversal :: (Ord e, Ord n) => 
>                   FSA (Set n) e -> Set(Path (Set n) e) -> Integer -> Integer
> slTraversal sm ps k
>     | (Set.null ps) = k + 1
>     | cycle = 0
>     | someSingle = slTraversal sm (union live restps) (max k ((depth thisp)+1))
>     | otherwise = slTraversal sm (union live restps) k
>     where
>       (thisp,restps) = choose ps
>       exts = (extensions sm thisp)
>       someSingle  = anyS
>                     (maybe False
>                      ((1 ==) . Set.size . nodeLabel) . endstate)
>                     exts
>       live = Set.filter
>              (maybe False
>               ((1 <) . Set.size . nodeLabel) . endstate)
>              exts
>       cycle = anyS (maybe False (isIn (stateMultiset thisp)) . endstate) live

psgQ is the label of the initial state of the PSG, i.e., the stateset of
  the original DFA

> psgQ :: (Ord a, Ord b) => FSA (Set b) a -> State (Set b)
> psgQ = Set.findMin . initials

{---------------------------------------------------------------------------}
   Forbidden Factors
   Forbidden Factors of fsa are the forbidden units of psGraph, 
     initial forbidden factors of DFA, free forbidden factors of psGraph,
     final forbidden factors of psGraph and forbidden words of DFA.
   Forbidden units are elts of alphabet that do not label any edge from Q
    in psGraph
    - Since sigma forbidden iff no edge q1 -sigma-> q2 for any q1, q2 in DFA
        iff no edge Q-sigma->S  for any S in psGraph
   Initial FF are the labels of acyclic paths from the start state to the 
     sink state in the minimal but not trimmed DFA.  These are minimal iff 
     they contain no Free FF.
   Free FF are labels of paths Q --> $\emptyset$ in psGraph
      These are minimal iff they contain no other Free FF as a suffix
   Final FF are labels of paths Q --> state sets in the psGraph other than
     $\emptyset$ that are  
     disjoint with the final states of the DFA.  These are minimal iff they 
     contain no other Final FF as a suffix.
   Forbidden words are labels of paths from the start state to a non-accepting 
     state in the DFA that do not include an Initial FF as a prefix, a Free FF 
     as a substring or a Final FF as a suffix.  For this set to be bounded, 
     the stringset has to be SL, in which case the bound is k.

   Since the bare forbiddenFactors generates unitFFs wrt the defaultAlphabet 
    defined in Factors.hs, which is of type Set(String), its applicable only 
    to FSA String b.

> -- |A convenience-type for declaring collections of  forbidden substrings.

> type ForbiddenSubstrings e = ( PermittedUnits e
>                              , ForbiddenWords e
>                              , ForbiddenInitialSubstrings e
>                              , ForbiddenFreeSubstrings e
>                              , ForbiddenFinalSubstrings e
>                              )
> type PermittedUnits e = Set e
> type ForbiddenWords e = Set [e]
> type ForbiddenInitialSubstrings e = Set [e]
> type ForbiddenFreeSubstrings e = Set [e]
> type ForbiddenFinalSubstrings e = Set [e]

> type ForbiddenPaths n e = ( PermittedUnits e
>                                , ForbiddenWordPaths n e
>                                , ForbiddenInitialPaths n e
>                                , ForbiddenFreePaths n e
>                                , ForbiddenFinalPaths n e
>                                )
> type ForbiddenWordPaths n e = Set (Path n e)
> type ForbiddenInitialPaths n e = Set (Path n e)
> type ForbiddenFreePaths n e = Set (Path n e)
> type ForbiddenFinalPaths n e = Set (Path n e)

> -- |Convert ForbiddenPaths into ForbiddenSubstrings
> factorsFromPaths :: Ord e =>
>                     ForbiddenPaths n e -> ForbiddenSubstrings e
> factorsFromPaths (u, w, i, r, f) = (u, g w, g i, g r, g f)
>     where g = tmap (unsymbols . labels)

> -- |Paths representing the forbidden substrings of the given 'FSA'.
> -- the alphabet of which must be a subset of the provided alphabet.
> forbiddenPathsWithAlphabet:: (Ord e, Ord n, Enum n) =>
>                                Set e
>                             -> FSA n e
>                             -> ForbiddenPaths (Set n) e
> forbiddenPathsWithAlphabet alph fsa = (uFFs, fWs, iFFs, frFFs, fiFFs)
>     where
>        psg = powersetGraph fsa
>        k = slPSGQ psg
>        uFFs = unitFFsWithAlphabet alph psg
>        iFFs = initialFFs fsa (max 0 (k-1))
>        fWs =  fWords fsa (max 0 (k-2)) iFFs frFFs fiFFs
>        frFFs = freeFFsPSG psg k
>        fiFFs = finalFFsPSG psg (max 0 (k-1))


> -- |The forbidden substrings of the given 'FSA'.
> forbiddenPaths:: (Ord n, Enum n, Ord e) =>
>                  FSA n e ->
>                  ForbiddenPaths (Set n) e
> forbiddenPaths fsa = forbiddenPathsWithAlphabet (alphabet fsa) fsa


Bounded search for forbidden factors.

In gathering initial, free and final forbidden factors cycles in the psGraph
are taken up to bound many times.  If bound is negative then cycles are taken
arbitrarily many times and these searches are guaranteed to terminate only if
the psGraph represents a DFA that recognizes an SL stringset.

In gathering forbidden words, the maximum length of word is bound.  If bound
is negative, it is computed to be slQ-2.  If either bound or slQ-2 is less than
0, no forbidden words will be gathered.  If either is equal to 0 then, at
most, \epsilon will be gathered.


> -- |The forbidden substrings of the given 'FSA',
> -- the alphabet of which must be a subset of the
> -- provided alphabet.  Takes only boundedly many
> -- iterations of each cycle in the powerset graph.
> forbiddenPathsWithAlphabetWithBound :: (Ord e, Ord n, Enum n) =>
>                                         Set e   -- alphabet
>                                      -> Integer -- bound on iterations of cycles
>                                      -> FSA n e
>                                      -> ForbiddenPaths (Set n) e
> forbiddenPathsWithAlphabetWithBound alph bnd fsa = 
>     (uFFs, fWs, iFFs, frFFs, fiFFs)
>     where
>        psg = powersetGraph fsa
>        uFFs = unitFFsWithAlphabet alph psg
>        iFFs = initialFFs fsa bnd
>        wrdBound :: (Ord e, Ord n) => Integer -> FSA n e -> Integer
>        wrdBound bnd fsa
>            | (bnd < 0) = max 0 ((slQ fsa)-2)
>            | otherwise = bnd
>        fWs = fWords fsa (wrdBound bnd fsa) iFFs frFFs fiFFs
>        frFFs = freeFFsPSG psg bnd
>        fiFFs = finalFFsPSG psg bnd

> -- |The forbidden substrings of the given 'FSA'.
> -- Takes only boundedly many iterations of each
> -- cycle in the powerset graph.
> forbiddenPathsWithBound :: (Ord n, Enum n, Ord e) =>
>                            Integer -- bound
>                         -> FSA n e
>                         -> ForbiddenPaths (Set n) e
> forbiddenPathsWithBound b fsa =
>     forbiddenPathsWithAlphabetWithBound (alphabet fsa) b fsa


   Forbidden Units
   For FSAs constructed from sources such as Jeff's fsa, these will generally 
     be empty, since the alphabet of the fsa is determined by its transitions.       In general, and in the case of derived FSAs, the fsa may have a declared 
     alphabet that includes symbols that never actually occur in any accepted 
     string.
   From a linguistic perspective, I think, these are interesting because they 
     express constraints such as "all heavy syllables bear some stress" and 
     "there are no stressed light syllables."  For those circumstances, it is
     probably most appropriate to generate the set of forbidden units relative 
     to a standard unified alphabet, even though it may include syllable 
     weights or stress levels that are irrelevant to the particular language in
     question. 

alphabet is initial argument to aid in generalizing
this should include 1-FreeFFs from freeFFs
the best way to do that is to include $\sigma$ where $\tup{\sigma, Q, \emptyset}$
is in the edgeset of the 

> unitFFsWithAlphabet :: (Ord a, Ord b) => Set a -- alphabet
>                                -> (FSA (Set b) a ) -- psGraph
>                                -> PermittedUnits a
> unitFFsWithAlphabet alphs psg =
>     alphs `difference` (unsymbols (tmap edgeLabel oneFFs))
>         where
>           initialTrans = Set.filter
>                           (((psgQ psg) ==).source)
>                           (transitions psg)
>           oneFFs = Set.filter(((State Set.empty) ==).destination) initialTrans

> unitFFs :: (Ord a, Ord b) => (FSA (Set b) a) -- psGraph
>                                -> PermittedUnits a
> unitFFs psg = unitFFsWithAlphabet (alphabet psg) psg


   Forbidden words
   Labels of acyclic paths from the start state of the DFA that end at a 
   non-accepting state.

   These could possibly already be barred by a forbidden final factor,
   but neither an initial or free forbidden factor

   However, for the nonce we fall back to just filtering rejects as in 2016
   This just filters the empty string and words with initialFFs as a previc, 
   freeFFs as a substring, or finalFFs as a suffix from rejected words of 
   length less than or equal to bound


> fWords :: (Ord a, Ord b) =>
>           FSA b a
>        -> Integer             -- bound
>        -> ForbiddenInitialPaths c a
>        -> ForbiddenFreePaths d a
>        -> ForbiddenFinalPaths e a
>        -> ForbiddenWordPaths (Set b) a
> fWords fsa' bound iFFs frFFs fiFFs =
>     (keep
>      ((\wrd -> not ((anyS (\x -> (List.isPrefixOf x wrd)) (tmap labels fiFFs))
>                     ||
>                     (anyS (\x -> (List.isInfixOf x wrd)) (tmap labels frFFs))
>                     ||
>                     (anyS (\x -> (List.isSuffixOf x wrd)) (tmap labels iFFs))) ) .
>       word)
>      (rejectingPaths fsa bnd))
>     where fsa = renameStatesBy singleton fsa'
>           bnd = maximum
>                 [(1+supermax iFFs), (1+supermax fiFFs), (supermax frFFs)]
>                 - 2
>           supermax :: Set (Path n e) -> Integer
>           supermax = Set.findMax . insert 0 . tmap (size . labels)


            -- No longer strip epsilon
            -- (\wrd -> not ((null wrd) 
            --               ||

k is only significant if it is 0


> initialFFs :: (Ord a, Ord b, Enum b) =>
>               FSA b a
>            -> Integer                 -- k
>            -> ForbiddenInitialPaths (Set b) a
> initialFFs fsa k = tmap (\p -> p {labels = word p}) $ finalFFs rFSA k
>         where rFSA = renameStates . normalize $ FSA.reverse fsa

> freeFFs :: (Ord a, Ord b) =>
>            (FSA b a) -> Integer -> ForbiddenFreePaths (Set b) a
> freeFFs fsa k = freeFFsPSG (powersetGraph fsa) k

> -- k is only significant if it is 0
> freeFFsPSG :: (Ord a, Ord b) => (FSA (Set b) a) -> Integer ->
>                                  ForbiddenFreePaths (Set b) a
> freeFFsPSG psg k
>     = gatherFFs psgR k (Set.singleton stateQ) initialFront empty
>     where 
>       psgR = (trimRevPSG psg)
>       stateQ = psgQ psg
>       initialFront
>           | (contains stateEmpty (states psg))
>               =  singleton
>                  (Path empty (pure stateEmpty) (singleton stateEmpty) 0)
>           | otherwise = empty
>       stateEmpty = (State empty)


finalFFs
 graph: reversed powerset graph
   less: in-edges to $\emptyset$
         --- path necessarily would include ff as prefix
         out-edges from Q
         --- path necessarily includes final ff as suffix
 goals: {State Q}
 initial states:  {s $\in$ (states psg) |
                    s /= $\emptyset$ and
                    s $\cap$ (finals fsa) == $\emptyset$}
                  This is complement of initial states of reversed psGraph
k is only significant if it is 0


> finalFFs :: (Ord a, Ord b) => (FSA b a)
>                                -> Integer                 -- k
>                                -> ForbiddenFinalPaths (Set b) a
> finalFFs fsa k = finalFFsPSG (powersetGraph fsa) k

> finalFFsPSG :: (Ord a, Ord b) =>
>                (FSA (Set b) a) -> Integer
>             -> ForbiddenFinalPaths (Set b) a
> finalFFsPSG psg k
>     = gatherFFs psgR k (singleton stateQ) initialFront empty
>     where 
>       psgR = (trimRevPSG psg)
>       stateQ = psgQ psg
>       initialFront = fromCollapsible $
>                      tmap
>                      (\s -> Path empty (pure s) (singleton s) 0)
>                      (difference
>                       (states psgR)
>                       (insert (State empty) (initials psgR)))


trimRevPSG psg is reverse of
   (psg with in-edges to Q and out-edges from $\emptyset$ removed)
   note that such edges are necessarily self-edges


> trimRevPSG :: (Ord a, Ord b) => FSA (Set b) a -> FSA (Set b) a
> trimRevPSG psg = FSA.reverse psgr
>     where
>       psgr = FSA (alphabet psg)
>                  (Set.filter
>                          (\t ->
>                               ((destination t) /= (psgQ psg))
>                               && (source t) /= (State (Set.empty)) )
>                              (transitions psg) )
>                  (initials psg) (finals psg) (isDeterministic psg)


 Breadth-first traversal of graph
  Returns list of strings labeling paths from initial frontier to a goal
   that are:  acyclic other than, if k/=0, cycles of singletons
              & do not include shorter such path as a suffix
k is only significant if it is 0
if k is 0 then do not follow any cycles
ow follow singleton cycles which, since k>0, will be the only cycles

> gatherFFs :: (Ord a, Ord b) => FSA (Set b) a -- graph (psGraph based)
>                   -> Integer                 -- bound
>                   -> Set (State (Set b))     -- set of goal states
>                   -> [Path (Set b) a]        -- frontier
>                   -> Set (Path (Set b) a)    -- FFs so far
>                   -> Set (Path (Set b) a)    -- FFs
> gatherFFs psg bound goal [] ffs = ffs
> gatherFFs psg bound goal front ffs
>     = gatherFFs psg bound goal nextFront (union nextFFs ffs)
>     where
>       (nextFront,nextFFs)  -- (frontier k+1, k-FFs)
>           = passK goal                   
>                   (List.foldl' union empty       -- extensions
>                                (map acceptableExtensions front) )
>                   empty empty                    -- front k+1 & k-FFs
>       acceptableExtensions p
>           | (bound < 0) = Set.toList (extensions psg p)
>           | otherwise = Set.toList (boundedCycleExtensions psg bound p)


passK scans extensions of kth frontier for length k FFs 
 paths with label of a known k-FF are dropped
 labels of paths that end at a goal are added to FFs and
  paths with same label already in front k+1 are stripped
--  excluded factors are freeFFs (empty when finding freeFFs)
Returns (front k+1, k-FFs)
This k is not that k

> passK :: (Ord a, Ord b) => Set (State b)      -- goal states
>                               -> [Path b a]      -- extensions of front k
>                               -> [Path b a]      -- front k+1 so far
>                               -> Set (Path b a)  -- k-FFs so far
>                               -> ([Path b a], Set (Path b a))
>                                                  -- (front, k-FFs)
> passK goals [] front ffs = (front, ffs)
> passK goals (p:ps) front ffs 
>     | contains (labels p) (tmap labels ffs)    -- extends known ff
>         = passK goals ps front ffs
>     | maybe False (isIn goals) (endstate p)    -- new ff
>         = passK goals ps
>            (keep
>               ((\x -> doesNotContain (labels x)
>                       (insert (labels p) (tmap labels ffs))))
>               front)
>            (insert p ffs)
>     | otherwise = passK goals ps (p:front) ffs -- in frontier k+1

verification 
This is using forbiddenFactors, hence assumes FSA String b


buildFSAs FFs -> tuple of lists of FSAs for each FF

> buildFSAs :: (NFData e, Ord e)
>              => FSA Integer e
>              -> ( Set e
>                 , [FSA Integer e]
>                 , [FSA Integer e]
>                 , [FSA Integer e]
>                 , [FSA Integer e]
>                 )
> buildFSAs = buildFSAsFromFFs . forbiddenPaths


> buildFSAsFromFFs :: (NFData e, Ord e) =>
>                     ForbiddenPaths n e
>                  -> ( Set e    -- alphabet
>                     , [FSA Integer e]  -- words
>                     , [FSA Integer e]  -- initials
>                     , [FSA Integer e]  -- free
>                     , [FSA Integer e]  -- finals
>                     )
> buildFSAsFromFFs (alphs,fws,ifs,frfs,fifs) = (alphs, was, ias, fras, fias)
>     where
>       f h t = buildLiteral alphs . forbidden .
>               (\x -> Substring x h t)        .
>               tmap singleton . unsymbols . labels
>       build h t = tmap (f h t) . Set.toList
>       was = build True True fws
>       ias = build True False ifs
>       fras = build False False frfs
>       fias = build False True fifs


build FSA from FSAs

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


build FSA from forbidden factors
Since this uses renameStates the State type of the result will be Integer
This really needs to be as strict as possible, which I hope it isn't

> -- |Create an 'FSA' satisfying the conditions imposed by the
> -- given sets of forbidden substrings.
> buildFSA :: (NFData e, Ord e) => ForbiddenPaths n e -> FSA Integer e
> buildFSA = combineFSAs . buildFSAsFromFFs

\end{document}
