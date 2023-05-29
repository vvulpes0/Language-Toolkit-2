> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.Definite
> Copyright : (c) 2021 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is Definite (Def) or Reverse Definite (RDef) based on the classic
> semigroup characterizations summarized by Brzozowski and Fich in
> their 1984 work "On Generalized Locally Testable Languages".
>
> @since 1.0
> -}
> module LTK.Decide.Definite
>     ( -- *Plain
>       isDef
>     , isDefM
>     , isRDef
>     , isRDefM
>       -- *Tier-Based
>     , isTDef
>     , isTDefM
>     , isTRDef
>     , isTRDefM
>     ) where

> import qualified Data.Set as Set

> import LTK.FSA
> import LTK.Algebra
> import LTK.Tiers (project)

> -- |True iff the automaton recognizes a definite stringset,
> -- characterized by a set of permitted suffixes.
> isDef :: (Ord n, Ord e) => FSA n e -> Bool
> isDef = isDefM . syntacticMonoid

> -- |True iff \(Se=e\) for idempotents \(e\).
> isDefM :: (Ord n, Ord e) => SynMon n e -> Bool
> isDefM s = all ((==1) . Set.size . primitiveIdealL s)
>            . Set.toList $ idempotents s

> -- |True iff the automaton recognizes a reverse definite stringset,
> -- characterized by a set of permitted prefixes.
> isRDef :: (Ord n, Ord e) => FSA n e -> Bool
> isRDef = isRDefM . syntacticMonoid

> -- |True iff \(eS=e\) for idempotents \(e\).
> isRDefM :: (Ord n, Ord e) => SynMon n e -> Bool
> isRDefM s = all ((==1) . Set.size . primitiveIdealR s)
>            . Set.toList $ idempotents s

> -- |Definite on some tier.
> isTDef :: (Ord n, Ord e) => FSA n e -> Bool
> isTDef = isDef . project

> -- |Definite on the projected subsemigroup.
> isTDefM :: (Ord n, Ord e) => SynMon n e -> Bool
> isTDefM = isDefM . project

> -- |Reverse definite on some tier.
> isTRDef :: (Ord n, Ord e) => FSA n e -> Bool
> isTRDef = isRDef . project

> -- |Reverse definite on the projected subsemigroup.
> isTRDefM :: (Ord n, Ord e) => SynMon n e -> Bool
> isTRDefM = isRDefM . project
