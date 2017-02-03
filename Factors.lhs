> module Factors where

> import LogicClasses
> import FSA
> import Data.Set (Set)
> import qualified Data.Set as Set

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

> piecewise :: (Integral a, Ord b) =>
>              Bool -> Set (Symbol b) -> [Set (Symbol b)] -> FSA a b
> piecewise _ alpha []               = complementDeterminized $
>                                      emptyWithAlphabet alpha
> piecewise isPositive alpha symseq  = FSA
>                                      alpha
>                                      trans
>                                      (singleton (State 0))
>                                      (if isPositive then fin else fin')
>                                      True
>     where tagged         = zip symseq [0..]
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
>           fin            = singleton . State . succ . maximum $
>                            map snd tagged

> negativePiecewiseFactor :: (Integral a, Ord b) =>
>                            Set (Symbol b) -> [Set (Symbol b)] -> FSA a b
> negativePiecewiseFactor = piecewise False

> positivePiecewiseFactor :: (Integral a, Ord b) =>
>                            Set (Symbol b) -> [Set (Symbol b)] -> FSA a b
> positivePiecewiseFactor = piecewise True
