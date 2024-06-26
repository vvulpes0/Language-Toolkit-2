> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module:    LTK.Factors
> Copyright: (c) 2017-2019,2023 Dakotah Lambert
> License:   MIT

> This module provides a means to define
> positive and negative factors
> over the adjacency or precedence relations,
> as well as unions and intersections thereof.
> -}

> module LTK.Factors
>        ( -- *Constructions
>          required
>        , forbidden
>        , buildLiteral
>        , build
>        , makeConstraint
>        -- *Logical Expressions
>        , Factor(..)
>        , Literal(..)
>        , Disjunction(..)
>        , Conjunction(..)
>        ) where

> import Control.DeepSeq (NFData)
> import Data.Set (Set)
> import qualified Data.Set as Set

> import LTK.FSA

> -- |A substring or subsequence, from which to build constraints.
> data Factor e
>     = Substring
>       { substring :: [Set e] -- ^The sequence of symbol types,
>                              -- e.g. @[wxs0, wxs0]@
>                              -- for two consecutive unstressed syllables.
>       , headAnchored :: Bool -- ^Anchored to the head of the word?
>       , tailAnchored :: Bool -- ^Anchored to the tail of the word?
>       }
>     | Subsequence [Set e]
>     deriving (Eq, Ord, Read, Show)

> -- |A constraint.
> data Literal e = Literal Bool (Factor e) deriving (Eq, Ord, Read, Show)

> -- |Multiple constraints, joined by @OR@.
> newtype Disjunction e = Disjunction (Set (Literal e))
>     deriving (Eq, Ord, Read, Show)

> -- |Multiple disjunctions, joined by @AND@.
> newtype Conjunction e = Conjunction (Set (Disjunction e))
>     deriving (Eq, Ord, Read, Show) -- Primitive Constraint

> -- |The factor is required to appear in every string.
> -- Note that a conjunctive constraint of
> -- (@required (Substring x True True)@)
> -- restricts the stringset to at most one word.
> required :: Factor e -> Literal e
> required = Literal True

> -- | The factor is not allowed to appear in any word.
> forbidden :: Factor e -> Literal e
> forbidden = Literal False

> buildFactor :: (Enum n, Ord n, Ord e) =>
>                Set e -> Factor e -> Bool -> FSA n e
> buildFactor alpha (Substring factor anchoredToHead anchoredToTail)
>     = flip (`f` alpha) factor
>     where f = case (anchoredToHead, anchoredToTail)
>               of (True,   True)   ->  word
>                  (True,   False)  ->  initialLocal
>                  (False,  True)   ->  finalLocal
>                  (False,  False)  ->  local
> buildFactor alpha (Subsequence factor)
>     =  \isPositive ->
>        FSA { sigma        =  alpha
>            , transitions  =  tran
>            , initials     =  singleton . State $ toEnum 0
>            , finals       =  if isPositive then fin else fin'
>            , isDeterministic = True
>            }
>     where tagged     =  zip factor $ iterate succ (toEnum 0)
>           trans'     =  unionAll
>                         $ tmap
>                           (\(symset, st) ->
>                            tmap (succtrans st)
>                                 (intersection alpha symset)
>                            `union`
>                            tmap (selftrans st)
>                                 (difference alpha symset)
>                           )
>                         tagged
>           tran       =  tmap (selftrans nextState) alpha
>                         `union` trans'
>           fin'       =  Set.fromList $ tmap (State . snd) tagged
>           nextState  =  succ . maximum $ tmap snd tagged
>           fin        =  singleton (State nextState)

> -- |Build an t'FSA' representing a single constraint.
> buildLiteral :: (Enum n, Ord n, Ord e) => Set e -> Literal e -> FSA n e
> buildLiteral alpha (Literal isPositive factor)
>     = buildFactor alpha factor isPositive

> buildDisjunction :: (Enum n, NFData n, Ord n, NFData e, Ord e) =>
>                     Set e -> Disjunction e -> FSA n e
> buildDisjunction alpha (Disjunction literals)
>     = flatUnion . insert (emptyWithAlphabet alpha) .
>       tmap (buildLiteral alpha) $ Set.toList literals

> buildConjunction :: (Enum n, NFData n, Ord n, NFData e, Ord e) =>
>                     Set e -> Conjunction e -> FSA n e
> buildConjunction alpha (Conjunction disjunctions)
>     = flatIntersection . insert (totalWithAlphabet alpha) .
>       tmap (buildDisjunction alpha) $ Set.toList disjunctions

> -- |Build an t'FSA' representing the conjunction of a set of
> -- constraints provided in conjunctive normal form.
> build :: (Enum n, NFData n, Ord n, NFData e, Ord e) =>
>          Set e -> Set (Conjunction e) -> FSA n e
> build alpha = flatIntersection                  .
>               insert (totalWithAlphabet alpha)  .
>               tmap (buildConjunction alpha) . Set.toList

> -- |Combine inner lists by t'Disjunction',
> -- and form a t'Conjunction' of the results.
> makeConstraint :: (Ord e) => [[Literal e]] -> Conjunction e
> makeConstraint
>     = Conjunction . Set.fromList . tmap (Disjunction . Set.fromList)

> word :: (Enum a, Ord a, Ord b) =>
>              Bool -> Set b -> [Set b] -> FSA a b
> word True  alpha []  =  singletonWithAlphabet alpha []
> word False alpha []  =  complementDeterministic $
>                         singletonWithAlphabet alpha []
> word isPositive alpha symseq
>     = renameStates .
>       (if isPositive then id else complementDeterministic) .
>       determinize $
>       FSA { sigma            =  alpha
>           , transitions      =  trans
>           , initials         =  singleton $ State 0
>           , finals           =  singleton $ State nextState
>           , isDeterministic  =  False
>           }
>     where tagged     =  zip symseq [0 :: Integer ..]
>           trans'     =  unionAll $
>                         tmap
>                         (\(symset, st) ->
>                          tmap (succtrans st)
>                               (intersection alpha symset)
>                          `union`
>                          tmap (sinktrans sinkState st)
>                               (difference alpha symset)
>                         )
>                         tagged
>           trans      =  tmap (succtrans nextState) alpha
>                         `union` trans'
>           nextState  =  succ . maximum $ tmap snd tagged
>           sinkState  =  succ nextState

> initialLocal :: (Enum a, Ord a, Ord b) =>
>                 Bool -> Set b -> [Set b] -> FSA a b
> initialLocal True  a [] = complementDeterministic $ initialLocal False a []
> initialLocal False a [] = emptyWithAlphabet a
> initialLocal isPositive alpha symseq
>     = FSA { sigma            =  alpha
>           , transitions      =  trans
>           , initials         =  singleton . State $ toEnum 0
>           , finals           =  if isPositive then fin else fin'
>           , isDeterministic  =  True
>           }
>     where tagged     =  zip symseq $ iterate succ (toEnum 0)
>           trans'     =  unionAll $
>                         tmap
>                         (\(symset, st) ->
>                          tmap (succtrans st)
>                               (intersection alpha symset)
>                          `union`
>                          tmap (sinktrans sinkState st)
>                               (difference alpha symset)
>                         ) tagged
>           trans      =  unionAll
>                         [ tmap (selftrans nextState) alpha
>                         , tmap (selftrans sinkState) alpha
>                         , trans'
>                         ]
>           nextState  =  succ . maximum $ tmap snd tagged
>           sinkState  =  succ nextState
>           fin'       =  insert
>                         (State sinkState)
>                         (Set.fromList $ tmap (State . snd) tagged)
>           fin        =  singleton (State nextState)

For final and non-anchored factors, it would be nice to use KMP.
However, for that to work properly, I believe we would have to expand
the symbol-sets, then combine all the results with either union or
intersection (depending on whether the factor is to be positive or
negative).  Making these from NFAs is cheaper, it seems.

> finalLocal :: (Enum a, Ord a, Ord b) =>
>                 Bool -> Set b -> [Set b] -> FSA a b
> finalLocal True  a [] = complementDeterministic $ finalLocal False a []
> finalLocal False a [] = emptyWithAlphabet a
> finalLocal isPositive alpha symseq
>     = renameStates . (if isPositive then id else complementDeterministic) .
>       determinize $ FSA { sigma            =  alpha
>                         , transitions      =  trans
>                         , initials         =  singleton $ State 0
>                         , finals           =  singleton $ State nextState
>                         , isDeterministic  =  False
>                         }
>     where tagged     =  zip symseq [0 :: Integer ..]
>           trans'     =  unionAll
>                         $ tmap
>                           (\(symset, st) ->
>                            tmap (succtrans st)
>                            $ intersection alpha symset
>                           ) tagged
>           trans      =  tmap (selftrans 0) alpha `union` trans'
>           nextState  =  succ . maximum $ tmap snd tagged

> local :: (Enum a, Ord a, Ord b) =>
>                 Bool -> Set b -> [Set b] -> FSA a b
> local True  alpha [] = complementDeterministic $ local False alpha []
> local False alpha [] = emptyWithAlphabet alpha
> local isPositive alpha symseq
>     = renameStates .
>       (if isPositive then id else complementDeterministic) .
>       determinize $
>       FSA
>       { sigma        =  alpha
>       , transitions  =  trans
>       , initials     =  singleton $ State 0
>       , finals       =  singleton $ State nextState
>       , isDeterministic = False
>       }
>     where tagged  = zip symseq [0 :: Integer ..]
>           trans'  = unionAll $
>                     tmap
>                     (\(symset, st) ->
>                      tmap (succtrans st) $ intersection alpha symset
>                     )
>                     tagged
>           trans   = unionAll
>                     [tmap (selftrans 0) alpha
>                     , tmap (selftrans nextState) alpha
>                     , trans'
>                     ]
>           nextState = succ . maximum $ tmap snd tagged

> selftrans, succtrans :: (Enum n) => n -> e -> Transition n e
> selftrans  =  transTo id
> succtrans  =  transTo succ

> sinktrans :: n -> n -> e -> Transition n e
> sinktrans sinkState = transTo (const sinkState)

> transTo :: (n -> n) -> n -> e -> Transition n e
> transTo f n x
>     = Transition
>       { edgeLabel = Symbol x
>       , source = State n
>       , destination = State $ f n
>       }
