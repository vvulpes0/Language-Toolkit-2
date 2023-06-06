> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.Multitier
> Copyright : (c) 2022 Dakotah Lambert
> License   : MIT

> The Boolean closure of tier-based locally V is a subclass
> of the Meification of V.  For instance, multiple-tier-based
> definite is a proper subclass of the L-trivial languages.
> This module includes decision algorithms for some classes
> of multiple-tier-based languages.
>
> The equations given here are adapted from Almeida's (1995)
> "Finite Semigroups and Universal Algebra"
> https://doi.org/10.1142/2481
> as they are simpler than the equivalent ones I had found independently.
> -}
> module LTK.Decide.Multitier
>     ( isMTF, isMTDef, isMTRDef, isMTGD
>     , isMTFM, isMTDefM, isMTRDefM, isMTGDM
>     ) where

> import qualified Data.Set as Set

> import LTK.FSA
> import LTK.Algebra

> -- |True iff the given language is multiple-tier-based definite.
> isMTDef :: (Ord n, Ord e) => FSA n e -> Bool
> isMTDef = isMTDefM . syntacticMonoid

> -- |True iff the given language is multiple-tier-based reverse-definite.
> isMTRDef :: (Ord n, Ord e) => FSA n e -> Bool
> isMTRDef = isMTRDefM . syntacticMonoid

> -- |True iff the given language is multiple-tier-based (co)finite.
> isMTF :: (Ord n, Ord e) => FSA n e -> Bool
> isMTF = isMTFM . syntacticMonoid

> -- |True iff the given language is multiple-tier-based
> -- generalized-definite.
> isMTGD :: (Ord n, Ord e) => FSA n e -> Bool
> isMTGD = isMTGDM . syntacticMonoid

> -- |True iff the monoid satisfies \(xyx^{\omega}=yx^{\omega}\).
> isMTDefM :: (Ord n, Ord e) => SynMon n e -> Bool
> isMTDefM s = and [f x y | x <- q, y <- q]
>     where q = Set.toList $ states s
>           f x y = let ye = follow s (h $ omega s x) y
>                   in case Set.toList ye
>                      of (z:[])  ->  ye == follow s (h z) x
>                         _       ->  False
>           h = snd . nodeLabel

> -- |True iff the monoid satisfies \(x^{\omega}yx=x^{\omega}y\).
> isMTRDefM :: (Ord n, Ord e) => SynMon n e -> Bool
> isMTRDefM s = and [f x y | x <- q, y <- q]
>     where q = Set.toList $ states s
>           f x y = let ey = follow s (h y) (omega s x)
>                   in case Set.toList ey
>                      of (z:[])  ->  ey == follow s (h x) z
>                         _       ->  False
>           h = snd . nodeLabel

> -- |True iff the monoid is aperiodic and satisfies
> -- \(x^{\omega}y=yx^{\omega}\).
> isMTFM :: (Ord n, Ord e) => SynMon n e -> Bool
> isMTFM s = isMTDefM s && isMTRDefM s

> -- |True iff the monoid satisfies
> -- \(x^{\omega}uxvx^{\omega}=x^{\omega}uvx^{\omega}\)
> -- and \(x^{\omega}uxzvz^{\omega}=x^{\omega}uzxvz^{\omega}\).
> -- Thanks to Almeida (1995) for the simplification.
> isMTGDM :: (Ord n, Ord e) => SynMon n e -> Bool
> isMTGDM s = and [f u v x | u <- q, v <- q, x <- q]
>     where q = Set.toList $ states s
>           f u v x = let e = omega s x
>                     in allS (g u v x) q
>                        && follow s (concatMap h [u,x,v,e]) e
>                           == follow s (concatMap h [u,v,e]) e
>           g u v x z = let x' = omega s x
>                           z' = omega s z
>                       in follow s (concatMap h [u,x,z,v,z']) x'
>                          == follow s (concatMap h [u,z,x,v,z']) x'
>           h = snd . nodeLabel
