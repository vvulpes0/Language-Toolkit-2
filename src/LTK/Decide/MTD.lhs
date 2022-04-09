> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.MTD
> Copyright : (c) 2022 Dakotah Lambert
> License   : MIT

> Multiply tier-based definite languages form a superclass of
> (tier-based) definite, yet are a proper subclass of the
> L-trivial languages.  This module attempts to provide
> a classifier for this class.
> -}
> module LTK.Decide.MTD
>     ( isMTDef
>     , isMTDefM
>     ) where

> import qualified Data.Set as Set

> import LTK.FSA
> import LTK.Algebra

> isMTDef :: (Ord n, Ord e) => FSA n e -> Bool
> isMTDef = isMTDefM . syntacticMonoid

> isMTDefM :: (Ord n, Ord e) => SynMon n e -> Bool
> isMTDefM s = and [f v y e
>                  | v <- q, y <- q, e <- Set.toList (g y)]
>     where g y = primitiveIdeal2 s y `Set.intersection` idempotents s
>           q = Set.toList $ states s
>           q0 = fst . choose $ initials s
>           f v y e = follow s (concatMap h [y,v,e]) q0
>                       == follow s (concatMap h [v,e]) q0
>           h = snd . nodeLabel
