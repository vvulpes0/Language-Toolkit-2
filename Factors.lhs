> module Factors where

> import Containers
> import FSA
> import Data.Set (Set)
> import qualified Data.Set as Set

> data Factor e       =  Substring [Set e] Bool Bool | Subsequence [Set e] deriving (Eq, Ord, Read, Show)
> data Literal e      =  Literal Bool (Factor e) deriving (Eq, Ord, Read, Show)
> data Disjunction e  =  Disjunction (Set (Literal e)) deriving (Eq, Ord, Read, Show)
> data Conjunction e  =  Conjunction (Set (Disjunction e)) deriving (Eq, Ord, Read, Show) -- Primitive Constraint

> required :: Factor e -> Literal e
> required = Literal True
> forbidden :: Factor e -> Literal e
> forbidden = Literal False

> buildFactor :: (Enum n, Ord n, Ord e) => Set e -> Factor e -> Bool -> FSA n e
> buildFactor alpha (Substring factor anchoredToHead anchoredToTail) = flip (flip f alpha) factor
>     where f = case (anchoredToHead, anchoredToTail) of
>                 (True,   True)   ->  word
>                 (True,   False)  ->  initialLocal
>                 (False,  True)   ->  finalLocal
>                 (False,  False)  ->  local
> buildFactor alpha (Subsequence factor) =  (\isPositive ->
>                                            FSA alpha trans
>                                            (singleton (State $ toEnum 0))
>                                            (if isPositive then fin else fin')
>                                            True)
>     where tagged         = zip factor $ tmap toEnum [0..]
>           trans'         = unionAll $
>                            tmap
>                            (\(symset, st) ->
>                             union
>                             (tmap (succtrans st) (intersection alpha symset))
>                             (tmap (selftrans st) (difference alpha symset))
>                            )
>                            tagged
>           trans          = union
>                            (tmap (selftrans nextState) alpha)
>                            trans'
>           fin'           = Set.fromList $ tmap (State . snd) tagged
>           nextState      = succ . maximum $ tmap snd tagged
>           fin            = singleton (State nextState)
> buildLiteral :: (Enum n, Ord n, Ord e) => Set e -> Literal e -> FSA n e
> buildLiteral alpha (Literal isPositive factor) = buildFactor alpha factor isPositive
> buildDisjunction :: (Enum n, NFData n, Ord n, NFData e, Ord e) =>
>                     Set e -> Disjunction e -> FSA n e
> buildDisjunction alpha (Disjunction literals) = flatUnion . tmap (buildLiteral alpha) . Set.toList $ literals
> buildConjunction :: (Enum n, NFData n, Ord n, NFData e, Ord e) =>
>                     Set e -> Conjunction e -> FSA n e
> buildConjunction alpha (Conjunction disjunctions) = flatIntersection . tmap (buildDisjunction alpha) . Set.toList $ disjunctions
> build :: (Enum n, NFData n, Ord n, NFData e, Ord e) =>
>          Set e -> Set (Conjunction e) -> FSA n e
> build alpha conjunctions = flatIntersection . tmap (buildConjunction alpha) . Set.toList $ conjunctions
> makeConstraint :: (Ord e) => [[Literal e]] -> Conjunction e
> makeConstraint = Conjunction . Set.fromList . tmap (Disjunction . Set.fromList)
> makeConstraintList :: (Ord e) => [[[Literal e]]] -> Set (Conjunction e)
> makeConstraintList = Set.fromList . tmap makeConstraint
> buildFromList :: (Enum n, NFData n, Ord n, NFData e, Ord e) =>
>                  Set e -> [[[Literal e]]] -> FSA n e
> buildFromList alpha = build alpha . makeConstraintList

> w0s0, w0s1, w0s2, w1s0, w1s1, w1s2 :: Set String
> w2s0, w2s1, w2s2, w3s0, w3s1, w3s2 :: Set String
> w4s0, w4s1, w4s2, wxs0, wxs1, wxs2 :: Set String
> w0s0 = singleton "L"
> w0s1 = singleton "L`"
> w0s2 = singleton "L'"
> w1s0 = singleton "H"
> w1s1 = singleton "H`"
> w1s2 = singleton "H'"
> w2s0 = singleton "S"
> w2s1 = singleton "S`"
> w2s2 = singleton "S'"
> w3s0 = singleton "X"
> w3s1 = singleton "X`"
> w3s2 = singleton "X'"
> w4s0 = singleton "Y"
> w4s1 = singleton "Y`"
> w4s2 = singleton "Y'"
> wxs0 = unionAll [w0s0, w1s0, w2s0, w3s0, w4s0]
> wxs1 = unionAll [w0s1, w1s1, w2s1, w3s1, w4s1]
> wxs2 = unionAll [w0s2, w1s2, w2s2, w3s2, w4s2]

> w0, w1, w2, w3, w4, wx, defaultAlphabet :: Set String
> w0 = unionAll [w0s0, w0s1, w0s2]
> w1 = unionAll [w1s0, w1s1, w1s2]
> w2 = unionAll [w2s0, w2s1, w2s2]
> w3 = unionAll [w3s0, w3s1, w3s2]
> w4 = unionAll [w4s0, w4s1, w4s2]
> wx = unionAll [w0, w1, w2, w3, w4]
> defaultAlphabet = wx

> w0plus, w1plus, w2plus, w3plus, w4plus, wxplus :: Set String
> w0plus = unionAll [w0s1, w0s2]
> w1plus = unionAll [w1s1, w1s2]
> w2plus = unionAll [w2s1, w2s2]
> w3plus = unionAll [w3s1, w3s2]
> w4plus = unionAll [w4s1, w4s2]
> wxplus = unionAll [w0plus, w1plus, w2plus, w3plus, w4plus]

> w0minus, w1minus, w2minus, w3minus, w4minus, wxminus :: Set String
> w0minus = unionAll [w0s0, w0s1]
> w1minus = unionAll [w1s0, w1s1]
> w2minus = unionAll [w2s0, w2s1]
> w3minus = unionAll [w3s0, w3s1]
> w4minus = unionAll [w4s0, w4s1]
> wxminus = unionAll [w0minus, w1minus, w2minus, w3minus, w4minus]

> wplus, wpluss0, wpluss1, wpluss2, wplusplus, wplusminus :: Set String
> wplus = wx `difference` w0
> wpluss0 = wxs0 `difference` w0
> wpluss1 = wxs1 `difference` w0
> wpluss2 = wxs2 `difference` w0
> wplusplus = wxplus `difference` w0
> wplusminus = wxminus `difference` w0

> word :: (Enum a, Ord a, Ord b) =>
>              Bool -> Set b -> [Set b] -> FSA a b
> word True alpha []            = emptyWithAlphabet alpha
> word False alpha []           = complementDeterministic $
>                                 singletonWithAlphabet alpha []
> word isPositive alpha symseq  = FSA alpha trans
>                                 (singleton (State $ toEnum 0))
>                                 (if isPositive then fin else fin')
>                                 True
>     where tagged         = zip symseq $ tmap toEnum [0..]
>           trans'         = unionAll $
>                            tmap
>                            (\(symset, st) ->
>                             union
>                             (tmap
>                              (succtrans st)
>                              (intersection alpha symset))
>                             (tmap
>                              (sinktrans sinkState st)
>                              (difference alpha symset))
>                            )
>                            tagged
>           trans          = union
>                            (tmap (succtrans nextState) alpha)
>                            trans'
>           fin'           = fromCollapsible . tmap State .
>                            insert sinkState $
>                            tmap snd tagged
>           nextState      = succ . maximum $ tmap snd tagged
>           sinkState      = succ nextState
>           fin            = singleton (State nextState)

> initialLocal :: (Enum a, Ord a, Ord b) =>
>                 Bool -> Set b -> [Set b] -> FSA a b
> initialLocal _ alpha [] = complementDeterministic $
>                           emptyWithAlphabet alpha
> initialLocal isPositive alpha symseq = FSA
>                                        alpha
>                                        trans
>                                        (singleton (State $ toEnum 0))
>                                        (if isPositive then fin else fin')
>                                        True
>     where tagged         = zip symseq $ tmap toEnum [0..]
>           trans'         = unionAll $
>                            tmap
>                            (\(symset, st) ->
>                             union
>                             (tmap (succtrans st) (intersection alpha symset))
>                             (tmap (sinktrans sinkState st)
>                              (difference alpha symset))
>                            )
>                            tagged
>           trans          = unionAll
>                            [(tmap (selftrans nextState) alpha),
>                             (tmap (selftrans sinkState) alpha),
>                             trans']
>           nextState      = succ . maximum $ tmap snd tagged
>           sinkState      = succ nextState
>           fin'           = insert
>                            (State sinkState)
>                            (Set.fromList $ tmap (State . snd) tagged)
>           fin            = singleton (State nextState)

For final and non-anchored factors, it would be nice to use KMP.
However, for that to work properly, I believe we would have to expand
the symbol-sets, then combine all the results with either union or
intersection (depending on whether the factor is to be positive or
negative).  Making these from NFAs is cheaper, it seems.

> finalLocal :: (Enum a, Ord a, Ord b) =>
>                 Bool -> Set b -> [Set b] -> FSA a b
> finalLocal _ alpha [] = complementDeterministic $
>                         emptyWithAlphabet alpha
> finalLocal isPositive alpha symseq = renameStates .
>                                      (if isPositive
>                                       then id
>                                       else complementDeterministic) $
>                                      determinize fsa
>     where tagged = zip symseq [0..]
>           trans'         = unionAll $
>                            tmap
>                            (\(symset, st) ->
>                             (tmap (succtrans st) (intersection alpha symset))
>                            )
>                            tagged
>           trans          = union (tmap (selftrans 0) alpha) trans'
>           nextState      = succ . maximum $ tmap snd tagged
>           fin            = singleton (State nextState)
>           fsa            = FSA alpha trans
>                            (singleton (State 0))
>                            fin False

> local :: (Enum a, Ord a, Ord b) =>
>                 Bool -> Set b -> [Set b] -> FSA a b
> local _ alpha [] = complementDeterministic $
>                    emptyWithAlphabet alpha
> local isPositive alpha symseq = renameStates .
>                                 (if isPositive
>                                  then id
>                                  else complementDeterministic) $
>                                 determinize fsa
>     where tagged = zip symseq [0..]
>           trans'         = unionAll $
>                            tmap
>                            (\(symset, st) ->
>                             (tmap (succtrans st) (intersection alpha symset))
>                            )
>                            tagged
>           trans          = unionAll
>                            [(tmap (selftrans 0) alpha),
>                             (tmap (selftrans nextState) alpha),
>                             trans']
>           nextState      = succ . maximum $ tmap snd tagged
>           fin            = singleton (State nextState)
>           fsa            = FSA alpha trans
>                            (singleton (State 0))
>                            fin False

> selftrans, succtrans :: (Enum n) => n -> e -> Transition n e
> selftrans n x  = Transition (Symbol x) (State n) (State n)
> succtrans n x  = Transition (Symbol x) (State n) (State $ succ n)
> sinktrans :: n -> n -> e -> Transition n e
> sinktrans sinkState n x = Transition (Symbol x) (State n) (State sinkState)
