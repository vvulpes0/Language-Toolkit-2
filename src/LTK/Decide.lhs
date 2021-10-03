> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide
> Copyright : (c) 2019-2021 Dakotah Lambert
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
>                   -- * Piecewise classes
>                   , isSP, isPT
>                   -- * Local classes
>                   , isGD, isSL, isLT, isLTT
>                   -- * Both Local and Piecewise
>                   , isCB, isGLT, isLPT, isGLPT, isSF
>                   -- * Tier-based generalizations
>                   , isTGD, isTSL, isTLT, isTLTT, isTLPT
>                   -- * Two-Variable Logics
>                   , isFO2, isFO2B, isFO2S
>                   ) where

> import LTK.Decide.Finite
> import LTK.Decide.SL
> import LTK.Decide.LT
> import LTK.Decide.LPT
> import LTK.Decide.LTT
> import LTK.Decide.TSL
> import LTK.Decide.TLT
> import LTK.Decide.TLTT
> import LTK.Decide.TLPT
> import LTK.Decide.SP
> import LTK.Decide.PT
> import LTK.Decide.SF
> import LTK.Decide.FO2
> import LTK.Decide.GLT
> import LTK.Decide.GLPT
> import LTK.Decide.GD
> import LTK.Decide.CB
