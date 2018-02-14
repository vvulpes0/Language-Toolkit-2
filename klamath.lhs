> module Main where

> import Containers
> import FSA
> import Factors
> import Data.Set (Set)
> import qualified Data.Set as Set

> ka = unionAll [w0s0, w0s2, w1, w2]

> primary_rightmost_s = piecewise False ka $ [wxs2, w2]
> no_lhp_after_s = piecewise False ka $ [w2, union w0s2 w1s2]
> primary_penult_if_h_and_no_s = union
>                                (piecewise True ka $ [w2])
>                                (finalLocal False ka $ [w1minus, wx])
> else_antepenult = unionAll
>                   [piecewise True ka $ [w2],
>                    finalLocal True ka $ [w1s2, wx],
>                    finalLocal False ka $ [wxminus, wx, wx]]
> no_final_syl_subsuperheavy_prime = finalLocal False ka $ [wx, union w0s2 w1s2]
> obligatoriness = piecewise True ka $ [wxs2]
> culminativity = piecewise False ka $ [wxs2, wxs2]
> no_initial_grave = initialLocal False ka $ [wxs1]
> no_final_grave = finalLocal False ka $ [wxs1]
> no_prepenult_grave = local False ka $ [wxs1, wx, wx]
> grave_only_after_superheavy = local False ka $ [union w0 w1, wxs1]
> no_final_superheavy_heavy_unstressed_syl = finalLocal False ka $ [w2, union w1s0 w2s0, wx]
> no_empty = piecewise True ka $ [wx]

> pairwise :: [a] -> [[a]]
> pairwise []        = []
> pairwise (x:[])    = [x] : []
> pairwise (x:y:xs)  = [x,y] : pairwise xs

> intersect_pairwise :: (Enum n, Ord e, Ord n) => [FSA n e] -> FSA n e
> intersect_pairwise []      = undefined
> intersect_pairwise (x:[])  = x
> intersect_pairwise xs      = intersect_pairwise $
>                              map (renameStates . minimize . intersectAll)
>                              (pairwise xs)

> klamath = intersect_pairwise
>           [primary_rightmost_s,
>            no_lhp_after_s,
>            primary_penult_if_h_and_no_s,
>            else_antepenult,
>            no_final_syl_subsuperheavy_prime,
>            obligatoriness,
>            culminativity,
>            no_initial_grave,
>            no_final_grave,
>            no_prepenult_grave,
>            grave_only_after_superheavy,
>            no_final_superheavy_heavy_unstressed_syl,
>            no_empty]

> klamath_real = FSA (Set.fromList [Symbol "L",Symbol "L'",Symbol "H",Symbol "H`",Symbol "H'",Symbol "S",Symbol "S`",Symbol "S'"]) (Set.fromList [Transition (Symbol "L") (State 0) (State 7),Transition (Symbol "L") (State 1) (State 14),Transition (Symbol "L") (State 3) (State 4),Transition (Symbol "L") (State 4) (State 4),Transition (Symbol "L") (State 5) (State 6),Transition (Symbol "L") (State 6) (State 11),Transition (Symbol "L") (State 7) (State 7),Transition (Symbol "L") (State 8) (State 6),Transition (Symbol "L") (State 9) (State 10),Transition (Symbol "L") (State 10) (State 11),Transition (Symbol "L") (State 12) (State 13),Transition (Symbol "L") (State 13) (State 14),Transition (Symbol "L") (State 14) (State 14),Transition (Symbol "L") (State 15) (State 4),Transition (Symbol "L") (State 16) (State 4),Transition (Symbol "L") (State 17) (State 14),Transition (Symbol "L'") (State 0) (State 5),Transition (Symbol "L'") (State 7) (State 9),Transition (Symbol "H") (State 0) (State 7),Transition (Symbol "H") (State 1) (State 12),Transition (Symbol "H") (State 3) (State 4),Transition (Symbol "H") (State 4) (State 4),Transition (Symbol "H") (State 5) (State 11),Transition (Symbol "H") (State 6) (State 11),Transition (Symbol "H") (State 7) (State 7),Transition (Symbol "H") (State 8) (State 11),Transition (Symbol "H") (State 10) (State 11),Transition (Symbol "H") (State 12) (State 13),Transition (Symbol "H") (State 13) (State 14),Transition (Symbol "H") (State 14) (State 14),Transition (Symbol "H") (State 15) (State 3),Transition (Symbol "H") (State 16) (State 3),Transition (Symbol "H") (State 17) (State 12),Transition (Symbol "H`") (State 1) (State 10),Transition (Symbol "H`") (State 15) (State 2),Transition (Symbol "H`") (State 16) (State 2),Transition (Symbol "H`") (State 17) (State 10),Transition (Symbol "H'") (State 0) (State 5),Transition (Symbol "H'") (State 7) (State 8),Transition (Symbol "S") (State 0) (State 15),Transition (Symbol "S") (State 3) (State 15),Transition (Symbol "S") (State 4) (State 15),Transition (Symbol "S") (State 7) (State 15),Transition (Symbol "S") (State 15) (State 16),Transition (Symbol "S") (State 16) (State 16),Transition (Symbol "S`") (State 15) (State 2),Transition (Symbol "S`") (State 16) (State 2),Transition (Symbol "S'") (State 0) (State 1),Transition (Symbol "S'") (State 2) (State 11),Transition (Symbol "S'") (State 3) (State 17),Transition (Symbol "S'") (State 4) (State 1),Transition (Symbol "S'") (State 7) (State 1),Transition (Symbol "S'") (State 15) (State 1),Transition (Symbol "S'") (State 16) (State 17)]) (Set.fromList [State 0]) (Set.fromList [State 1,State 5,State 6,State 11,State 12,State 14]) False

> main = if klamath == klamath_real
>        then putStrLn "Verified correct."
>        else (test_over >> test_under)
>     where diff1 = normalize $ difference klamath klamath_real
>           diff2 = normalize $ difference klamath_real klamath
>           test_over = if isNull diff1
>                       then return ()
>                       else putStrLn "Overgenerates:" >> print diff1
>           test_under = if isNull diff2
>                        then return ()
>                        else putStrLn "Undergenerates:" >> print diff2
