> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Extract.TSL
> Copyright : (c) 2019 Dakotah Lambert
> License   : MIT
> 
> Generalize Extract.SL for tier-local constraints.
> -}
> module LTK.Extract.TSL (forbiddenTierSubstrings) where

> import LTK.FSA
> import LTK.Extract.SL (ForbiddenSubstrings, forbiddenSubstrings)
> import LTK.Tiers

> import Data.Set (Set)

> -- |Forbidden tier-substrings of the given t'FSA'.
> forbiddenTierSubstrings :: (Ord e, Ord n, Enum n) =>
>                            FSA n e -> (Set e, ForbiddenSubstrings e)
> forbiddenTierSubstrings f = (tier f, forbiddenSubstrings f)
