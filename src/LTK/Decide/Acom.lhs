> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.Acom
> Copyright : (c) 2022-2023 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> has a semigroup both Commutative and Aperiodic (Acom).  This is
> the class that LTT localizes (Almeida, 1989).
>
> https://doi.org/10.1016/0022-4049(89)90124-2
> -}
> module LTK.Decide.Acom (isAcom, isAcomM, comTest) where

> import Data.Set (Set)
> import qualified Data.Set as Set

> import LTK.Decide.SF (isSFM)
> import LTK.FSA
> import LTK.Algebra

> type S n e = (n, [Symbol e])

> -- |True iff the automaton recognizes a \(\langle 1,t\rangle\)-LTT
> -- stringset.
> isAcom :: (Ord n, Ord e) => FSA n e -> Bool
> isAcom = isAcomM . syntacticMonoid

> -- |True iff the monoid is aperiodic and commutative
> isAcomM :: (Ord n, Ord e) => SynMon n e -> Bool
> isAcomM = both isSFM (\m -> comTest m (states m))

> -- |True iff the specified elements commute.
> comTest :: (Ord n, Ord e) =>
>           SynMon n e -> Set (State (S [Maybe n] e)) -> Bool
> comTest m qs
>     | Set.size (initials m) /= 1 = Set.null (initials m)
>     | otherwise = all commutes $ Set.toList p
>     where p = pairs $ tmap (snd . nodeLabel) qs
>           i = Set.findMin $ initials m
>           commutes x = follow m (uncurry (++) x) i
>                        == follow m (uncurry (flip (++)) x) i

> pairs :: Ord a => Set a -> Set (a, a)
> pairs xs = collapse (union . f) empty xs
>     where f x = Set.mapMonotonic ((,) x) xs
