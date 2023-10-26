> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.Multitier
> Copyright : (c) 2022-2023 Dakotah Lambert
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
>
> @since 1.1
> -}
> module LTK.Decide.Multitier
>     ( isMTF, isMTDef, isMTRDef, isMTGD
>     , isMTFM, isMTDefM, isMTRDefM, isMTGDM
>     , isMTFs, isMTDefs, isMTRDefs, isMTGDs
>     ) where

> import Data.Representation.FiniteSemigroup

> import LTK.FSA
> import LTK.Algebra(SynMon)

> -- |True iff the given language is multiple-tier-based definite.
> isMTDef :: (Ord n, Ord e) => FSA n e -> Bool
> isMTDef = isMTDefs . syntacticSemigroup

> -- |True iff the given language is multiple-tier-based reverse-definite.
> isMTRDef :: (Ord n, Ord e) => FSA n e -> Bool
> isMTRDef = isMTRDefs . syntacticSemigroup

> -- |True iff the given language is multiple-tier-based (co)finite.
> isMTF :: (Ord n, Ord e) => FSA n e -> Bool
> isMTF = isMTFs . syntacticSemigroup

> -- |True iff the given language is multiple-tier-based
> -- generalized-definite.
> isMTGD :: (Ord n, Ord e) => FSA n e -> Bool
> isMTGD = isMTGDs . syntacticSemigroup

> -- |True iff the monoid satisfies \(xyx^{\omega}=yx^{\omega}\).
> isMTDefM :: (Ord n, Ord e) => SynMon n e -> Bool
> isMTDefM = isMTDef

> -- |True iff the semigroup satisifes \(xyx^{\omega}=yx^{\omega}\).
> isMTDefs :: FiniteSemigroupRep s => s -> Bool
> isMTDefs s = all (uncurry go) [(a,b) | a <- xs, b <- xs]
>     where t = fstable s
>           xs = [0 .. fssize t - 1]
>           eval = foldr1 (fsappend t)
>           go x y = let yx' = eval [y,omega t x] in eval [x,yx'] == yx'

> -- |True iff the monoid satisfies \(x^{\omega}yx=x^{\omega}y\).
> isMTRDefM :: (Ord n, Ord e) => SynMon n e -> Bool
> isMTRDefM = isMTRDef

> -- |True iff the semigroup satisifes \(x^{\omega}yx=x^{\omega}y\).
> isMTRDefs :: FiniteSemigroupRep s => s -> Bool
> isMTRDefs = isMTDefs . dual

> -- |True iff the monoid is aperiodic and satisfies
> -- \(x^{\omega}y=yx^{\omega}\).
> isMTFM :: (Ord n, Ord e) => SynMon n e -> Bool
> isMTFM = isMTF

> -- |True iff the semigroup is aperiodic and satisfies
> -- \(x^{\omega}y=yx^{\omega}\).
> isMTFs :: FiniteSemigroupRep s => s -> Bool
> isMTFs = both isMTDefs isMTRDefs

> -- |True iff the monoid satisfies 'isMTGDs'.
> isMTGDM :: (Ord n, Ord e) => SynMon n e -> Bool
> isMTGDM = isMTGD

> -- |True iff the semigroup satisfies
> -- \(x^{\omega}uxvx^{\omega}=x^{\omega}uvx^{\omega}\)
> -- and \(x^{\omega}uxzvz^{\omega}=x^{\omega}uzxvz^{\omega}\).
> -- Thanks to Almeida (1995) for the simplification.
> isMTGDs :: FiniteSemigroupRep s => s -> Bool
> isMTGDs s = and [f u v x | u <- xs, v <- xs, x <- xs]
>     where t = fstable s
>           eval = foldr1 (fsappend t)
>           xs = [0 .. fssize s - 1]
>           f u v x = let x' = omega t x
>                         x'u = eval [x', u]
>                         vx' = eval [v, x']
>                     in eval [x'u,x,vx'] == eval [x'u,vx']
>                        && all (g u v x) xs
>           g u v x z = let x'u = eval [omega t x, u]
>                           vz' = eval [v, omega t z]
>                       in eval [x'u,x,z,vz'] == eval [x'u,z,x,vz']
