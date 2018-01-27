> module Factors where

> import LogicClasses
> import FSA
> import Data.Set (Set)
> import qualified Data.Set as Set

> data Factor e       =  Substring [Set (Symbol e)] Bool Bool | Subsequence [Set (Symbol e)] deriving (Eq, Ord, Read, Show)
> data Literal e      =  Literal Bool (Factor e) deriving (Eq, Ord, Read, Show)
> data Disjunction e  =  Disjunction (Set (Literal e)) deriving (Eq, Ord, Read, Show)
> data Conjunction e  =  Conjunction (Set (Disjunction e)) deriving (Eq, Ord, Read, Show) -- Primitive Constraint

> required :: Factor e -> Literal e
> required = Literal True
> forbidden :: Factor e -> Literal e
> forbidden = Literal False

> buildFactor :: (Enum n, Ord n, Ord e) => Set (Symbol e) -> Factor e -> Bool -> FSA n e
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
>     where tagged         = zip factor $ tmap (State . toEnum) [0..]
>           selftrans n x  = Transition x n n
>           succtrans n x  = Transition x n (fmap succ n)
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
>           fin'           = Set.fromList $ tmap snd tagged
>           nextState      = State . succ . maximum $ tmap (nodeLabel . snd) tagged
>           fin            = singleton nextState
> buildLiteral :: (Enum n, Ord n, Ord e) => Set (Symbol e) -> Literal e -> FSA n e
> buildLiteral alpha (Literal isPositive factor) = buildFactor alpha factor isPositive
> buildDisjunction :: (Enum n, Ord n, Ord e) => Set (Symbol e) -> Disjunction e -> FSA n e
> buildDisjunction alpha (Disjunction literals) = unionAll . tmap (buildLiteral alpha) . Set.toList $ literals
> buildConjunction :: (Enum n, Ord n, Ord e) => Set (Symbol e) -> Conjunction e -> FSA n e
> buildConjunction alpha (Conjunction disjunctions) = intersectAll . tmap (buildDisjunction alpha) . Set.toList $ disjunctions
> build :: (Enum n, Ord n, Ord e) => Set (Symbol e) -> Set (Conjunction e) -> FSA n e
> build alpha conjunctions = intersectAll . tmap (buildConjunction alpha) . Set.toList $ conjunctions
> makeConstraint :: (Ord e) => [[Literal e]] -> Conjunction e
> makeConstraint = Conjunction . Set.fromList . tmap (Disjunction . Set.fromList)
> makeConstraintList :: (Ord e) => [[[Literal e]]] -> Set (Conjunction e)
> makeConstraintList = Set.fromList . tmap makeConstraint
> buildFromList :: (Enum n, Ord n, Ord e) => Set (Symbol e) -> [[[Literal e]]] -> FSA n e
> buildFromList alpha = build alpha . makeConstraintList

> w0s0, w0s1, w0s2, w1s0, w1s1, w1s2 :: Set (Symbol String)
> w2s0, w2s1, w2s2, w3s0, w3s1, w3s2 :: Set (Symbol String)
> w4s0, w4s1, w4s2, wxs0, wxs1, wxs2 :: Set (Symbol String)
> w0s0 = singleton $ Symbol "L"
> w0s1 = singleton $ Symbol "L`"
> w0s2 = singleton $ Symbol "L'"
> w1s0 = singleton $ Symbol "H"
> w1s1 = singleton $ Symbol "H`"
> w1s2 = singleton $ Symbol "H'"
> w2s0 = singleton $ Symbol "S"
> w2s1 = singleton $ Symbol "S`"
> w2s2 = singleton $ Symbol "S'"
> w3s0 = singleton $ Symbol "X"
> w3s1 = singleton $ Symbol "X`"
> w3s2 = singleton $ Symbol "X'"
> w4s0 = singleton $ Symbol "Y"
> w4s1 = singleton $ Symbol "Y`"
> w4s2 = singleton $ Symbol "Y'"
> wxs0 = unionAll [w0s0, w1s0, w2s0, w3s0, w4s0]
> wxs1 = unionAll [w0s1, w1s1, w2s1, w3s1, w4s1]
> wxs2 = unionAll [w0s2, w1s2, w2s2, w3s2, w4s2]

> w0, w1, w2, w3, w4, wx, defaultAlphabet :: Set (Symbol String)
> w0 = unionAll [w0s0, w0s1, w0s2]
> w1 = unionAll [w1s0, w1s1, w1s2]
> w2 = unionAll [w2s0, w2s1, w2s2]
> w3 = unionAll [w3s0, w3s1, w3s2]
> w4 = unionAll [w4s0, w4s1, w4s2]
> wx = unionAll [w0, w1, w2, w3, w4]
> defaultAlphabet = wx

> w0plus, w1plus, w2plus, w3plus, w4plus, wxplus :: Set (Symbol String)
> w0plus = unionAll [w0s1, w0s2]
> w1plus = unionAll [w1s1, w1s2]
> w2plus = unionAll [w2s1, w2s2]
> w3plus = unionAll [w3s1, w3s2]
> w4plus = unionAll [w4s1, w4s2]
> wxplus = unionAll [w0plus, w1plus, w2plus, w3plus, w4plus]

> w0minus, w1minus, w2minus, w3minus, w4minus, wxminus :: Set (Symbol String)
> w0minus = unionAll [w0s0, w0s1]
> w1minus = unionAll [w1s0, w1s1]
> w2minus = unionAll [w2s0, w2s1]
> w3minus = unionAll [w3s0, w3s1]
> w4minus = unionAll [w4s0, w4s1]
> wxminus = unionAll [w0minus, w1minus, w2minus, w3minus, w4minus]

> wplus, wpluss0, wpluss1, wpluss2, wplusplus, wplusminus :: Set (Symbol String)
> wplus = wx `difference` w0
> wpluss0 = wxs0 `difference` w0
> wpluss1 = wxs1 `difference` w0
> wpluss2 = wxs2 `difference` w0
> wplusplus = wxplus `difference` w0
> wplusminus = wxminus `difference` w0

> word :: (Enum a, Ord a, Ord b) =>
>              Bool -> Set (Symbol b) -> [Set (Symbol b)] -> FSA a b
> word True alpha []            = emptyWithAlphabet alpha
> word False alpha []           = FSA alpha trans
>                                 (singleton startState)
>                                 (singleton finalState) True
>     where selftrans n x = Transition x n n
>           succtrans n x = Transition x n (fmap succ n)
>           startState    = State (toEnum 0)
>           finalState    = fmap succ startState
>           trans         = unionAll
>                           [tmap (succtrans startState) alpha,
>                            tmap (selftrans finalState) alpha]
> word isPositive alpha symseq  = FSA alpha trans
>                                 (singleton (State $ toEnum 0))
>                                 (if isPositive then fin else fin')
>                                 True
>     where tagged         = zip symseq $ tmap (State . toEnum) [0..]
>           selftrans n x  = Transition x n n
>           succtrans n x  = Transition x n (fmap succ n)
>           trans'         = unionAll $
>                            tmap
>                            (\(symset, st) ->
>                             union
>                             (tmap (succtrans st) (intersection alpha symset))
>                             (tmap (\x -> Transition x st failState) (difference alpha symset))
>                            )
>                            tagged
>           trans          = union
>                            (tmap (succtrans nextState) alpha)
>                            trans'
>           fin'           = insert failState . Set.fromList $ tmap snd tagged
>           nextState      = State . succ . maximum $ tmap (nodeLabel . snd) tagged
>           failState      = fmap succ nextState
>           fin            = singleton nextState

> initialLocal :: (Enum a, Ord a, Ord b) =>
>                 Bool -> Set (Symbol b) -> [Set (Symbol b)] -> FSA a b
> initialLocal _ alpha [] = complementDeterminized $
>                           emptyWithAlphabet alpha
> initialLocal isPositive alpha symseq = FSA
>                                        alpha
>                                        trans
>                                        (singleton (State $ toEnum 0))
>                                        (if isPositive then fin else fin')
>                                        True
>     where tagged         = zip symseq $ tmap toEnum [0..]
>           selftrans n x  = Transition x (State n) (State n)
>           succtrans n x  = Transition x (State n) (State $ succ n)
>           sinktrans n x  = Transition x (State n) (State sinkState)
>           trans'         = unionAll $
>                            tmap
>                            (\(symset, st) ->
>                             union
>                             (tmap (succtrans st) (intersection alpha symset))
>                             (tmap (sinktrans st) (difference alpha symset))
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
>                 Bool -> Set (Symbol b) -> [Set (Symbol b)] -> FSA a b
> finalLocal _ alpha [] = complementDeterminized $
>                         emptyWithAlphabet alpha
> finalLocal isPositive alpha symseq = renameStates .
>                                      (if isPositive
>                                       then id
>                                       else complementDeterminized) $
>                                      determinize fsa
>     where tagged = zip symseq [0..]
>           selftrans n x  = Transition x (State n) (State n)
>           succtrans n x  = Transition x (State n) (State $ succ n)
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
>                 Bool -> Set (Symbol b) -> [Set (Symbol b)] -> FSA a b
> local _ alpha [] = complementDeterminized $
>                    emptyWithAlphabet alpha
> local isPositive alpha symseq = renameStates .
>                                 (if isPositive
>                                  then id
>                                  else complementDeterminized) $
>                                 determinize fsa
>     where tagged = zip symseq [0..]
>           selftrans n x  = Transition x (State n) (State n)
>           succtrans n x  = Transition x (State n) (State $ succ n)
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
