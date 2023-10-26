> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.Definite
> Copyright : (c) 2021-2023 Dakotah Lambert
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
>     , isDefs
>     , isRDef
>     , isRDefM
>     , isRDefs
>       -- *Tier-Based
>     , isTDef
>     , isTDefM
>     , isTDefs
>     , isTRDef
>     , isTRDefM
>     , isTRDefs
>     ) where

> import Data.Representation.FiniteSemigroup

> import LTK.FSA
> import LTK.Algebra(SynMon)
> import LTK.Tiers (project)

> -- |True iff the automaton recognizes a definite stringset,
> -- characterized by a set of permitted suffixes.
> isDef :: (Ord n, Ord e) => FSA n e -> Bool
> isDef = isDefs . syntacticSemigroup

> -- |True iff \(Se=e\) for idempotents \(e\).
> isDefM :: (Ord n, Ord e) => SynMon n e -> Bool
> isDefM = isDef

> -- |True iff \(Se=e\) for idempotents \(e\).
> isDefs :: FiniteSemigroupRep s => s -> Bool
> isDefs = isRDefs . dual

> -- |True iff the automaton recognizes a reverse definite stringset,
> -- characterized by a set of permitted prefixes.
> isRDef :: (Ord n, Ord e) => FSA n e -> Bool
> isRDef = isRDefs . syntacticSemigroup

> -- |True iff \(eS=e\) for idempotents \(e\).
> isRDefM :: (Ord n, Ord e) => SynMon n e -> Bool
> isRDefM = isRDef

> -- |True iff \(eS=e\) for idempotents \(e\).
> isRDefs :: FiniteSemigroupRep s => s -> Bool
> isRDefs = both isRTrivial (locally isTrivial)

> -- |Definite on some tier.
> isTDef :: (Ord n, Ord e) => FSA n e -> Bool
> isTDef = isDef . project

> -- |Definite on the projected subsemigroup.
> isTDefM :: (Ord n, Ord e) => SynMon n e -> Bool
> isTDefM = isDefM . project

> -- |Definite on the projected subsemigroup.
> isTDefs :: FiniteSemigroupRep s => s -> Bool
> isTDefs = isDefs . projectedSubsemigroup

> -- |Reverse definite on some tier.
> isTRDef :: (Ord n, Ord e) => FSA n e -> Bool
> isTRDef = isRDef . project

> -- |Reverse definite on the projected subsemigroup.
> isTRDefM :: (Ord n, Ord e) => SynMon n e -> Bool
> isTRDefM = isRDefM . project

> -- |Reverse definite on the projected subsemigroup.
> isTRDefs :: FiniteSemigroupRep s => s -> Bool
> isTRDefs = isRDefs . projectedSubsemigroup
