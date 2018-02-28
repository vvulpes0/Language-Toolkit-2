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


> module SLfactors where

> import FSA
> import Traversals
> import Factors
> import Containers
> 
> import Data.Set (Set)
> import qualified Data.Set as Set
> import qualified Data.List as List
> import qualified Data.Map as Map

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
>       someSingle  = any
>                     (maybe False
>                      ((1 ==) . Set.size . nodeLabel) . endstate)
>                     exts
>       live = Set.filter
>              (maybe False
>               ((1 <) . Set.size . nodeLabel) . endstate)
>              exts
>       cycle = any (maybe False (isIn (stateMultiset thisp)) . endstate) live

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


> forbiddenFactorsWithAlphabet:: (Ord e, Ord n) =>
>                              Set e -- alphabet
>                                      -> FSA n e
>                                      -> ( (Set e),  -- unitFFs
>                                           (Set [e]),  -- fwords
>                                           (Set [e]),  -- initialFFs
>                                           (Set [e]),  -- freeFFs
>                                           (Set [e]) ) -- finalFFs
> forbiddenFactorsWithAlphabet alph fsa = (uFFs, fWs, iFFs, frFFs, fiFFs)
>     where
>        psg = powersetGraph fsa
>        k = slPSGQ psg
>        uFFs = unitFFsWithAlphabet alph psg
>        iFFs = initialFFs fsa (max 0 (k-1))
>        fWs = fWords fsa (max 0 (k-2)) iFFs frFFs fiFFs
>        frFFs = freeFFsPSG psg k
>        fiFFs = finalFFsPSG psg (max 0 (k-1))

> forbiddenFactors:: (Ord b) => FSA b String
>                                -> ( (Set (String)),  -- unitFFs
>                                     (Set [String]),  -- fWords
>                                     (Set [String]),  -- initialFFs
>                                     (Set [String]),  -- freeFFs
>                                     (Set [String]) ) -- finalFFs
> forbiddenFactors fsa = forbiddenFactorsWithAlphabet defaultAlphabet fsa


Bounded search for forbidden factors.

In gathering initial, free and final forbidden factors cycles in the psGraph
are taken up to bound many times.  If bound is negative then cycles are taken
arbitrarily many times and these searches are guaranteed to terminate only if
the psGraph represents a DFA that recognizes an SL stringset.

In gathering forbidden words, the maximum length of word is bound.  If bound
is negative, it is computed to be slQ-2.  If either bound or slQ-2 is less than
0, no forbidden words will be gathered.  If either is equal to 0 then, at
most, \epsilon will be gathered.


> forbiddenFactorsWithAlphabetWithBound :: (Ord e, Ord n) =>
>                                         Set e -- alphabet
>                                      -> Integer -- bound on iterations of cycles
>                                      -> FSA n e
>                                      -> ( (Set e),  -- unitFFs
>                                           (Set [e]),  -- fwords
>                                           (Set [e]),  -- initialFFs
>                                           (Set [e]),  -- freeFFs
>                                           (Set [e]) ) -- finalFFs
> forbiddenFactorsWithAlphabetWithBound alph bnd fsa = 
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

> forbiddenFactorsWithBound :: (Ord b) =>
>                                   Integer -- bound
>                                -> FSA b String
>                                -> ( (Set String),  -- unitFFs
>                                     (Set [String]),  -- fWords
>                                     (Set [String]),  -- initialFFs
>                                     (Set [String]),  -- freeFFs
>                                     (Set [String]) ) -- finalFFs
> forbiddenFactorsWithBound = 
>     forbiddenFactorsWithAlphabetWithBound defaultAlphabet


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
>                                -> Set a
> unitFFsWithAlphabet alphs psg =
>     union (alphs `difference` unsymbols (tmap edgeLabel initialTrans))
>           (unsymbols (tmap edgeLabel oneFFs))
>         where
>           initialTrans = Set.filter
>                           (((psgQ psg) ==).source)
>                           (transitions psg)
>           oneFFs = Set.filter(((State Set.empty) ==).destination) initialTrans

> unitFFs :: (Ord a, Ord b) => (FSA (Set b) a) -- psGraph
>                                -> Set a
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


> fWords :: (Ord a, Ord b) => FSA b a
>                             -> Integer             -- bound
>                             -> Set([a]) -- initialFFs
>                             -> Set([a]) -- freeFFs
>                             -> Set([a]) -- finalFFs
>                             -> Set([a])
> fWords fsa bound iFFs frFFs fiFFs =
>     Set.fromList
>            (filter
>             (\wrd -> not ((any (\x -> (List.isSuffixOf x wrd)) (Set.toList fiFFs))
>                           ||
>                           (any (\x -> (List.isInfixOf x wrd)) (Set.toList frFFs))
>                           ||
>                           (any (\x -> (List.isPrefixOf x wrd)) (Set.toList iFFs))) )
>             (map ((Prelude.reverse) . unsymbols . labels)
>                      (Set.toList (rejectingPaths fsa bnd)) ) )
>            where bnd =
>                    (max (1+(supermax (Set.union iFFs fiFFs))) (supermax frFFs))
>                    - 2
>                  supermax :: Set [a] -> Integer
>                  supermax l
>                      | (Set.null l) = 0
>                      | otherwise = 
>                          toInteger ((maximum . map length) (Set.toList l))


            -- No longer strip epsilon
            -- (\wrd -> not ((null wrd) 
            --               ||

k is only significant if it is 0


> initialFFs :: (Ord a, Ord b) => FSA b a
>                                 -> Integer                 -- k
>                                 -> Set [a]
> initialFFs fsa k = 
>     Set.map List.reverse (finalFFs rFSA k)
>         where rFSA = (FSA.normalize (FSA.reverse fsa))

> freeFFs :: (Ord a, Ord b) => (FSA b a) -> Integer -> Set [a]
> freeFFs fsa k = freeFFsPSG (powersetGraph fsa) k

> -- k is only significant if it is 0
> freeFFsPSG :: (Ord a, Ord b) => (FSA (Set b) a) -> Integer ->
>                                  Set [a]
> freeFFsPSG psg k
>     = Set.fromList (gatherFFs psgR k (Set.singleton stateQ) initialFront [])
>     where 
>       psgR = (trimRevPSG psg)
>       stateQ = psgQ psg
>       initialFront
>           | (Set.member stateEmpty (states psg))
>               =  [(Path [] (Just stateEmpty) (singleton stateEmpty) 0)]
>           | otherwise = []
>       stateEmpty = (State (Set.empty))


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
>                                -> Set [a]
> finalFFs fsa k = finalFFsPSG (powersetGraph fsa) k

> finalFFsPSG :: (Ord a, Ord b) =>
>                   (FSA (Set b) a)
>                       -> Integer                 -- k
>                       -> Set [a]
> finalFFsPSG psg k --fFFs
>     = Set.fromList (gatherFFs psgR k
>                                   (Set.singleton stateQ) -- goal
>                                   initialFront [])
>     where 
>       psgR = (trimRevPSG psg)
>       stateQ = psgQ psg
>       initialFront =  
>           [(Path [] (Just s) (singleton s) 0) |
>               s <- Set.toList (Set.difference (states psgR) (initials psgR)),
>                    s /= stateEmpty ]
>       stateEmpty = (State (Set.empty))


trimRevPSGPSG psg is reverse of
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
>                   -> [[a]]                   -- FFs so far
>                   -> [[a]]                   -- FFs
> gatherFFs psg bound goal [] ffs = ffs
> gatherFFs psg bound goal front ffs 
>     = gatherFFs psg bound goal nextFront (nextFFs ++ ffs)
>     where
>       (nextFront,nextFFs)  -- (frontier k+1, k-FFs)
>           = passK goal                   
>                   (List.foldl' (++) []       -- extensions
>                                (map acceptableExtensions front) )
>                   [] []                      -- front k+1 & k-FFs
>       acceptableExtensions p
>           | (bound < 0) = Set.toList (extensions psg p)
>           | otherwise = Set.toList (boundedCycleExtensions psg bound p)
>           -- | ((depth p) >= bound) = Set.toList (acyclicExtensions psg p)
>           -- | otherwise = Set.toList (extensions psg p)


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
>                               -> [[a]]    -- k-FFs so far
>                               -> ([Path b a], [[a]])
>                                                  -- (front, k-FFs)
> passK goals [] front ffs = (front, ffs)
> passK goals (p:ps) front ffs 
>     | List.elem  (unsymbols $ labels p) ffs      -- extends known ff
>         = passK goals ps front ffs
>     | maybe False (isIn goals) (endstate p)    -- new ff
>         = passK goals ps
>            (filter
>               ((\x -> List.notElem x ((unsymbols $ labels p):ffs)) . unsymbols . labels)
>               front)
>            ((unsymbols $ labels p):ffs)
>     | otherwise = passK goals ps (p:front) ffs -- in frontier k+1


verification 
This is using forbiddenFactors, hence assumes FSA String b


buildFSAs FFs -> tuple of lists of FSAs for each FF


> buildFSAs :: FSA Int String
>                                -> ( Set String,    -- alphabet
>                                     [FSA Int String],  -- words
>                                     [FSA Int String],  -- initials
>                                     [FSA Int String],  -- free
>                                     [FSA Int String] ) -- finals
> buildFSAs fsa = (alphs, was, ias, fras, fias)
>     where
>       (ufs, fws, ifs, frfs, fifs) = forbiddenFactors fsa
>       alphs = Set.difference defaultAlphabet ufs
>       f x = (renameStates . minimize . complement) x `asTypeOf` x
>       g   = map singleton
>       was = map (f . singletonWithAlphabet alphs)
>             (Set.toList fws) -- no longer adds epsilon
>       ias =  map (f . initialLocal True alphs . g)
>              (Set.toList ifs)
>       fras =  map (f . local True alphs . g)
>               (Set.toList frfs)
>       fias =  map (f . finalLocal True alphs . g)
>               (Set.toList fifs)


build FSA from FSAs


> combineFSAs :: (Set String,    -- alphabet
>                 [FSA Int String],  -- words
>                 [FSA Int String],  -- initials
>                 [FSA Int String],  -- free
>                 [FSA Int String] ) -- finals
>                 -> FSA Int String
> combineFSAs (alphs,was,ias,fras,fias) =
>     flatIntersection
>     (totalWithAlphabet alphs : concat [was, ias, fras, fias])


build FSA from forbidden factors
Since this uses renameStates the State type of the result will be Int
This really needs to be as strict as possible, which I hope it isn't


> buildFSA :: ( (Set String),  -- unitFFs
>               (Set [String]),  -- fWords
>               (Set [String]),  -- initialFFs
>               (Set [String]),  -- freeFFs
>               (Set [String]) ) -- finalFFs
>             -> FSA Int String
> buildFSA (ufs, fws, ifs, frfs, fifs) =
>     combineFSAs (alphs,was,ias,fras,fias) -- renameStates (minimize fia)
>     where
>       alphs = Set.difference defaultAlphabet ufs
>       f x = (renameStates . minimize . complement) x `asTypeOf` x
>       g   = map singleton
>       was = map (f . singletonWithAlphabet alphs)
>             (Set.toList fws) -- no longer adds epsilon
>       ias =  map (f . initialLocal True alphs . g)
>              (Set.toList ifs)
>       fras =  map (f . local True alphs . g)
>               (Set.toList frfs)
>       fias =  map (f . finalLocal True alphs . g)
>               (Set.toList fifs)


residue FFs -> FSA -> FSA
residue FSA is FSA that recognizes the set overgenerated by the FFs
This throws the error "Undergenerate" if the opposite difference is
  not empty.
Logically this can't happen, but "Undergenerate" is much less embarassing
  than "This can't happen"


> residue :: (Integral c, Ord b, Ord d) => 
>                   FSA d String -> FSA b String -> FSA c String
> residue ffsa fsa 
>     | (not . isNull) under = error "Undergenerate"
>     | otherwise = renameStates over
>     where
>       under = minimize  (difference (makeInt fsa) (makeInt ffsa))
>       over = minimize  (difference (makeInt ffsa) (makeInt fsa))
>       makeInt :: (Ord n, Ord e) => FSA n e -> FSA Int e
>       makeInt = renameStates

> residueFromFFs :: (Integral c, Ord b) =>
>                  ((Set String),  -- unitFFs
>                   (Set [String]),  -- fWords
>                   (Set [String]),  -- initialFFs
>                   (Set [String]),  -- freeFFs
>                   (Set [String]) ) -- finalFFs
>                    -> FSA b String
>                    -> FSA c String 
> residueFromFFs fFactors fsa 
>     | (not . isNull) under = error "Undergenerate"
>     | otherwise = renameStates over
>     where
>       ffsa = buildFSA fFactors
>       under = minimize  (difference (makeInt fsa) (makeInt ffsa))
>       over = minimize  (difference (makeInt ffsa) (makeInt fsa))
>       makeInt :: (Ord n, Ord e) => FSA n e -> FSA Int e
>       makeInt = renameStates

\end{document}
