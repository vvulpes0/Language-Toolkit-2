> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.DotDepth
> Copyright : (c) 2021-2024 Dakotah Lambert
> License   : MIT

> This module implement algorithms to decide whether a given FSA
> has a given dot depth.  Currently, only dot depth one is testable,
> using the equations presented by Knast's 1983 "A semigroup
> characterization of dot-depth one languages"
> https://doi.org/10.1051/ita/1983170403211
>
> @since 1.2
> -}
> module LTK.Decide.DotDepth (isDot1, isDot1M, isDot1s) where

> import Data.Representation.FiniteSemigroup
> import qualified Data.IntSet as IntSet

> import LTK.FSA
> import LTK.Algebra(SynMon)

> -- |True iff the automaton recognizes a dot-depth one stringset.
> isDot1 :: (Ord n, Ord e) => FSA n e -> Bool
> isDot1 = isDot1s . syntacticSemigroup

> -- |True iff the monoid recognizes a dot-depth one stringset.
> isDot1M :: (Ord n, Ord e) => SynMon n e -> Bool
> isDot1M = isDot1

> -- |True iff the semigroup recognizes a dot-depth one stringset.
> -- That is, for idempotents \(e\) and \(f\) and elements \(a\),
> -- \(b\), \(c\) and \(d\), it holds that
> -- \((eafb)^{\omega}eafde(cfde)^{\omega}
> -- = (eafb)^{\omega}e(cfde)^{\omega}\).
> isDot1s :: FiniteSemigroupRep s => s -> Bool
> isDot1s s = all go [ (e,f,a,b,c,d)
>                    | e <- is, f <- is, a <- xs
>                    , b <- xs, c <- xs, d <- xs]
>     where t = fstable s
>           is = IntSet.toList $ idempotents t
>           xs = [0 .. fssize t - 1]
>           eval = foldr1 (fsappend t)
>           go ~(e,f,a,b,c,d)
>               = let p1 = eval [omega t $ eval [e,a,f,b], e]
>                     p2 = eval [e, omega t $ eval [c,f,d,e]]
>                 in eval [p1,a,f,d,p2] == eval [p1,p2]
