> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module:    LTK.Factors
> Copyright: (c) 2017-2019 Dakotah Lambert
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
>        -- *Symbols
>        -- |@w/n/s/x/@ is a syllable whose weight is level \(n\)
>        -- and whose stress is level \(s\).
>        -- Stress ranges from 0-2,
>        -- while weight is in theory not limited.
>        -- Here, only weights up to level 4 are defined.
>        -- For both weight and stress,
>        -- \"plus\" means \"greater than zero\".
>        -- For stress, \"minus\" means \"less than two\".
>        -- Arbitrary weight is indicated by using @x@ for \(n\).
>        -- Arbitrary stress is indicated by omission of @s/x/@.
>        , defaultAlphabet
>        , w0s0, w0s1, w0s2, w0plus, w0minus, w0
>        , w1s0, w1s1, w1s2, w1plus, w1minus, w1
>        , w2s0, w2s1, w2s2, w2plus, w2minus, w2
>        , w3s0, w3s1, w3s2, w3plus, w3minus, w3
>        , w4s0, w4s1, w4s2, w4plus, w4minus, w4
>        , wpluss0, wpluss1, wpluss2, wplusplus, wplusminus, wplus
>        , wxs0, wxs1, wxs2, wxplus, wxminus, wx
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
> data Disjunction e = Disjunction (Set (Literal e))
>                      deriving (Eq, Ord, Read, Show)

> -- |Multiple disjunctions, joined by @AND@.
> data Conjunction e = Conjunction (Set (Disjunction e))
>                      deriving (Eq, Ord, Read, Show) -- Primitive Constraint

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
>     = flip (flip f alpha) factor
>     where f = case (anchoredToHead, anchoredToTail)
>               of (True,   True)   ->  word
>                  (True,   False)  ->  initialLocal
>                  (False,  True)   ->  finalLocal
>                  (False,  False)  ->  local
> buildFactor alpha (Subsequence factor)
>     =  (\isPositive ->
>         FSA { sigma        =  alpha
>             , transitions  =  tran
>             , initials     =  singleton . State $ toEnum 0
>             , finals       =  if isPositive then fin else fin'
>             , isDeterministic = True
>             }
>        )
>     where tagged     =  zip factor $ iterate succ (toEnum 0)
>           trans'     =  unionAll $
>                         tmap
>                         (\(symset, st) ->
>                          union
>                          (tmap (succtrans st) $ intersection alpha symset)
>                          (tmap (selftrans st) $ difference alpha symset)
>                         )
>                         tagged
>           tran       =  union trans' $
>                         tmap (selftrans nextState) alpha
>           fin'       =  Set.fromList $ tmap (State . snd) tagged
>           nextState  =  succ . maximum $ tmap snd tagged
>           fin        =  singleton (State nextState)

> -- |Build an 'FSA' representing a single constraint.
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

> -- |Build an 'FSA' representing the conjunction of a set of
> -- constraints provided in conjunctive normal form.
> build :: (Enum n, NFData n, Ord n, NFData e, Ord e) =>
>          Set e -> Set (Conjunction e) -> FSA n e
> build alpha = flatIntersection                  .
>               insert (totalWithAlphabet alpha)  .
>               tmap (buildConjunction alpha) . Set.toList

> -- |Combine inner lists by 'Disjunction',
> -- and form a 'Conjunction' of the results.
> makeConstraint :: (Ord e) => [[Literal e]] -> Conjunction e
> makeConstraint
>     = Conjunction . Set.fromList . tmap (Disjunction . Set.fromList)

> w0s0, w0s1, w0s2, w1s0, w1s1, w1s2 :: Set String
> w2s0, w2s1, w2s2, w3s0, w3s1, w3s2 :: Set String
> w4s0, w4s1, w4s2, wxs0, wxs1, wxs2 :: Set String
> -- |Light, unstressed
> w0s0 = singleton "L"
> -- |Light, secondary stress
> w0s1 = singleton "L`"
> -- |Light, primary stress
> w0s2 = singleton "L'"
> -- |Heavy, unstressed
> w1s0 = singleton "H"
> -- |Heavy, secondary stress
> w1s1 = singleton "H`"
> -- |Heavy, primary stress
> w1s2 = singleton "H'"
> -- |Superheavy, unstressed
> w2s0 = singleton "S"
> -- |Superheavy, secondary stress
> w2s1 = singleton "S`"
> -- |Superheavy, primary stress
> w2s2 = singleton "S'"
> -- |Weight 3, unstressed
> w3s0 = singleton "X"
> -- |Weight 3, secondary stress
> w3s1 = singleton "X`"
> -- |Weight 3, primary stress
> w3s2 = singleton "X'"
> -- |Weight 4, unstressed
> w4s0 = singleton "Y"
> -- |Weight 4, secondary stress
> w4s1 = singleton "Y`"
> -- |Weight 5, primary stress
> w4s2 = singleton "Y'"
> -- |Unstressed
> wxs0 = unionAll [w0s0, w1s0, w2s0, w3s0, w4s0]
> -- |Secondary stress
> wxs1 = unionAll [w0s1, w1s1, w2s1, w3s1, w4s1]
> -- |Primary stress
> wxs2 = unionAll [w0s2, w1s2, w2s2, w3s2, w4s2]

> w0, w1, w2, w3, w4, wx, defaultAlphabet :: Set String
> -- |Light, any stress
> w0 = unionAll [w0s0, w0s1, w0s2]
> -- |Heavy, any stress
> w1 = unionAll [w1s0, w1s1, w1s2]
> -- |Superheavy, any stress
> w2 = unionAll [w2s0, w2s1, w2s2]
> -- |Weight 3, any stress
> w3 = unionAll [w3s0, w3s1, w3s2]
> -- |Weight 4, any stress
> w4 = unionAll [w4s0, w4s1, w4s2]
> -- |Any weight or stress
> wx = unionAll [w0, w1, w2, w3, w4]
> -- |Equivalent to 'wx'.
> defaultAlphabet = wx

> w0plus, w1plus, w2plus, w3plus, w4plus, wxplus :: Set String
> -- |Light, some stress
> w0plus = unionAll [w0s1, w0s2]
> -- |Heavy, some stress
> w1plus = unionAll [w1s1, w1s2]
> -- |Superheavy, some stress
> w2plus = unionAll [w2s1, w2s2]
> -- |Weight 3, some stress
> w3plus = unionAll [w3s1, w3s2]
> -- |Weight 4, some stress
> w4plus = unionAll [w4s1, w4s2]
> -- |Some stress
> wxplus = unionAll [w0plus, w1plus, w2plus, w3plus, w4plus]

> w0minus, w1minus, w2minus, w3minus, w4minus, wxminus :: Set String
> -- |Light, non-primary stress
> w0minus = unionAll [w0s0, w0s1]
> -- |Heavy, non-primary stress
> w1minus = unionAll [w1s0, w1s1]
> -- |Superheavy, non-primary stress
> w2minus = unionAll [w2s0, w2s1]
> -- |Weight 3, non-primary stress
> w3minus = unionAll [w3s0, w3s1]
> -- |Weight 4, non-primary stress
> w4minus = unionAll [w4s0, w4s1]
> -- |Non-primary stress
> wxminus = unionAll [w0minus, w1minus, w2minus, w3minus, w4minus]

> wplus, wpluss0, wpluss1, wpluss2, wplusplus, wplusminus :: Set String
> -- |Non-light, any stress
> wplus = wx `difference` w0
> -- |Non-light, unstressed
> wpluss0 = wxs0 `difference` w0
> -- |Non-light, secondary stress
> wpluss1 = wxs1 `difference` w0
> -- |Non-light, primary stress
> wpluss2 = wxs2 `difference` w0
> -- |Non-light, some-stress
> wplusplus = wxplus `difference` w0
> -- |Non-light, non-primary stress
> wplusminus = wxminus `difference` w0

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
>                          union
>                          (tmap
>                           (succtrans st)
>                           (intersection alpha symset))
>                          (tmap
>                           (sinktrans sinkState st)
>                           (difference alpha symset))
>                         )
>                         tagged
>           trans      =  union
>                         (tmap (succtrans nextState) alpha)
>                         trans'
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
>                          union
>                          (tmap (succtrans st) $ intersection alpha symset)
>                          (tmap (sinktrans sinkState st) $
>                           difference alpha symset
>                          )
>                         )
>                         tagged
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
>           trans'     =  unionAll $
>                         tmap
>                         (\(symset, st) ->
>                          (tmap (succtrans st) (intersection alpha symset))
>                         )
>                            tagged
>           trans      =  union (tmap (selftrans 0) alpha) trans'
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
