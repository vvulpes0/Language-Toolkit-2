> module Factors where

> import LogicClasses
> import FSA
> import Data.Set (Set)
> import qualified Data.Set as Set

> negativePiecewiseFactor :: (Enum a, Ord a, Ord b) => Set (Symbol b) -> [Set (Symbol b)] -> FSA a b
> positivePiecewiseFactor :: (Enum a, Ord a, Ord b) => Set (Symbol b) -> [Set (Symbol b)] -> FSA a b
> negativeInitialFactor :: (Enum a, Ord a, Ord b) => Set (Symbol b) -> [Set (Symbol b)] -> FSA a b
> positiveInitialFactor :: (Enum a, Ord a, Ord b) => Set (Symbol b) -> [Set (Symbol b)] -> FSA a b
> negativeFinalFactor :: (Enum a, Ord a, Ord b) => Set (Symbol b) -> [Set (Symbol b)] -> FSA a b
> positiveFinalFactor :: (Enum a, Ord a, Ord b) => Set (Symbol b) -> [Set (Symbol b)] -> FSA a b
> negativeFactor :: (Enum a, Ord a, Ord b) => Set (Symbol b) -> [Set (Symbol b)] -> FSA a b
> positiveFactor :: (Enum a, Ord a, Ord b) => Set (Symbol b) -> [Set (Symbol b)] -> FSA a b
> negativePiecewiseFactor = piecewise False
> positivePiecewiseFactor = piecewise True
> negativeInitialFactor = initialLocal False
> positiveInitialFactor = initialLocal True
> negativeFinalFactor = finalLocal False
> positiveFinalFactor = finalLocal True
> negativeFactor = local False
> positiveFactor = local True

> w0s0 :: Set (Symbol String)
> w0s1 :: Set (Symbol String)
> w0s2 :: Set (Symbol String)
> w1s0 :: Set (Symbol String)
> w1s1 :: Set (Symbol String)
> w1s2 :: Set (Symbol String)
> w2s0 :: Set (Symbol String)
> w2s1 :: Set (Symbol String)
> w2s2 :: Set (Symbol String)
> w3s0 :: Set (Symbol String)
> w3s1 :: Set (Symbol String)
> w3s2 :: Set (Symbol String)
> w4s0 :: Set (Symbol String)
> w4s1 :: Set (Symbol String)
> w4s2 :: Set (Symbol String)
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

> w0 :: Set (Symbol String)
> w1 :: Set (Symbol String)
> w2 :: Set (Symbol String)
> w3 :: Set (Symbol String)
> w4 :: Set (Symbol String)
> w0 = unionAll [w0s0, w0s1, w0s2]
> w1 = unionAll [w1s0, w1s1, w1s2]
> w2 = unionAll [w2s0, w2s1, w2s2]
> w3 = unionAll [w3s0, w3s1, w3s2]
> w4 = unionAll [w4s0, w4s1, w4s2]
> wx = unionAll [w0, w1, w2, w3, w4]

> w0plus :: Set (Symbol String)
> w1plus :: Set (Symbol String)
> w2plus :: Set (Symbol String)
> w3plus :: Set (Symbol String)
> w4plus :: Set (Symbol String)
> w0plus = unionAll [w0s1, w0s2]
> w1plus = unionAll [w1s1, w1s2]
> w2plus = unionAll [w2s1, w2s2]
> w3plus = unionAll [w3s1, w3s2]
> w4plus = unionAll [w4s1, w4s2]
> wxplus = unionAll [w0plus, w1plus, w2plus, w3plus, w4plus]

> w0minus :: Set (Symbol String)
> w1minus :: Set (Symbol String)
> w2minus :: Set (Symbol String)
> w3minus :: Set (Symbol String)
> w4minus :: Set (Symbol String)
> w0minus = unionAll [w0s0, w0s1]
> w1minus = unionAll [w1s0, w1s1]
> w2minus = unionAll [w2s0, w2s1]
> w3minus = unionAll [w3s0, w3s1]
> w4minus = unionAll [w4s0, w4s1]
> wxminus = unionAll [w0minus, w1minus, w2minus, w3minus, w4minus]

> wxs0 :: Set (Symbol String)
> wxs1 :: Set (Symbol String)
> wxs2 :: Set (Symbol String)
> wxs0 = unionAll [w0s0, w1s0, w2s0, w3s0, w4s0]
> wxs1 = unionAll [w0s1, w1s1, w2s1, w3s1, w4s1]
> wxs2 = unionAll [w0s2, w1s2, w2s2, w3s2, w4s2]

> piecewise :: (Enum a, Ord a, Ord b) =>
>              Bool -> Set (Symbol b) -> [Set (Symbol b)] -> FSA a b
> piecewise _ alpha []               = complementDeterminized $
>                                      emptyWithAlphabet alpha
> piecewise isPositive alpha symseq  = FSA
>                                      alpha
>                                      trans
>                                      (singleton (State $ toEnum 0))
>                                      (if isPositive then fin else fin')
>                                      True
>     where tagged         = zip symseq $ tmap toEnum [0..]
>           selftrans n x  = Transition x (State n) (State n)
>           succtrans n x  = Transition x (State n) (State $ succ n)
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
