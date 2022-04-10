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

> -- |True iff the monoid satisfies \(yv(xyz)^{\omega}=v(xyz)^{\omega}\).
> isMTDefM :: (Ord n, Ord e) => SynMon n e -> Bool
> isMTDefM s = and [f v y e
>                  | v <- q, y <- q, e <- Set.toList (g y)]
>     where g y = primitiveIdeal2 s y `Set.intersection` idempotents s
>           q = Set.toList $ states s
>           q0 = fst . choose $ initials s
>           f v y e = follow s (concatMap h [y,v,e]) q0
>                     == follow s (concatMap h [v,e]) q0
>           h = snd . nodeLabel

> -- |True iff the monoid satisfies \((xyz)^{\omega}vy=(xyz)^{\omega}v\).
> isMTRDefM :: (Ord n, Ord e) => SynMon n e -> Bool
> isMTRDefM s = and [f v y e
>                   | v <- q, y <- q, e <- Set.toList (g y)]
>     where g y = primitiveIdeal2 s y `Set.intersection` idempotents s
>           q = Set.toList $ states s
>           q0 = fst . choose $ initials s
>           f v y e
>               | Set.null ev = True
>               | otherwise = follow s (h y) ev' == ev
>               where ev = follow s (concatMap h [e,v]) q0
>                     ev' = fst $ choose ev
>           h = snd . nodeLabel

> -- |True iff the monoid satisfies
> -- \(yv(xyz)^{\omega}u=v(xyz)^{\omega}u=v(xyz)^{\omega}uy\).
> isMTFM :: (Ord n, Ord e) => SynMon n e -> Bool
> isMTFM s = isMTDefM s && isMTRDefM s

> -- |True iff the monoid satisfies
> -- \((xyz)^{\omega}uyv(xyz)^{\omega}=(xyz)^{\omega}uv(xyz)^{\omega}\).
> isMTGDM :: (Ord n, Ord e) => SynMon n e -> Bool
> isMTGDM s = and [f u v y e
>                 | u <- q, v <- q, y <- q, e <- Set.toList (g y)]
>     where g y = primitiveIdeal2 s y `Set.intersection` idempotents s
>           q = Set.toList $ states s
>           q0 = fst . choose $ initials s
>           f u v y e
>               | Set.null eu = True
>               | otherwise   = follow s (concatMap h [y,v,e]) eu'
>                               == follow s (concatMap h [v,e]) eu'
>               where eu = follow s (concatMap h [e,u]) q0
>                     eu' = fst $ choose eu
>           h = snd . nodeLabel
