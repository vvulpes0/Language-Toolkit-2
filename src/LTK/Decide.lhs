> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide
> Copyright : (c) 2019 Dakotah Lambert
> License   : MIT
> 
> Functions used for deciding the complexity class of an automaton.
> Each complexity class for which these operations are implemented
> has a separate Decide.class module as well.
>
> @since 0.2
> -}
> module LTK.Decide (
>                   -- * Classes involving finiteness
>                   isFinite, isCofinite
>                   -- * Basic local classes
>                   , isSL, isLT, isLTT
>                   -- * Tier-based generalizations
>                   , isTSL, isTLT, isTLTT
>                   -- * Piecewise classes
>                   , isSP, isPT
>                   -- * Others
>                   , isFO2, isFO2B, isFO2S
>                   , isSF
>                   ) where

> import LTK.Decide.Finite
> import LTK.Decide.SL
> import LTK.Decide.LT
> import LTK.Decide.LTT
> import LTK.Decide.TSL
> import LTK.Decide.TLT
> import LTK.Decide.TLTT
> import LTK.Decide.SP
> import LTK.Decide.PT
> import LTK.Decide.SF
> import LTK.Decide.FO2
