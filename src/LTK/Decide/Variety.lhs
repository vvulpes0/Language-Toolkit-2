> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.Variety
> Copyright : (c) 2023 Dakotah Lambert
> License   : MIT

> This module provides a general mechanism
> for constructing decision procedures
> given an equational characterization of a pseudovariety.
> One parses the collection of equations,
> quantifies universally over the bound variables,
> and determines whether all specified relationships hold.
>
> @since 1.1
> -}

> module LTK.Decide.Variety ( isVariety
>                           , isVarietyM) where

> import qualified Data.Representation.FiniteSemigroup as F

> import LTK.FSA
> import LTK.Algebra (SynMon)

> -- |The @isVarietyM star desc@ function is equivalent to
> -- @isVariety star desc@.
> isVarietyM :: (Ord n, Ord e) => Bool -> String -> SynMon n e
>            -> Maybe Bool
> isVarietyM star desc = isVariety star desc

> -- |Determine whether a given semigroup is in the pseudovariety
> -- described by the given equation set.
> -- Returns Nothing if and only if the equation set cannot be parsed.
> -- The Boolean operand determines whether
> -- to check for a *-variety (True) or a +-variety (False).
> -- In other words, it determines whether the class containing
> -- the empty string is included
> -- if that is the only string in the class.
> isVariety :: (Ord n, Ord e) => Bool -> String -> FSA n e -> Maybe Bool
> isVariety star desc = F.isVariety desc . mk
>     where mk = if star then syntacticOMonoid else syntacticOSemigroup
