> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide
> Copyright : (c) 2019-2023 Dakotah Lambert
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
>                   isTrivial
>                   , isFinite, isCofinite
>                   , isTFinite, isTCofinite
>                   -- * Piecewise classes
>                   , isSP, isPT
>                   -- * Local classes
>                   , isDef, isRDef, isGD
>                   , isSL, isLT, isLTT, isLAcom
>                   -- * Both Local and Piecewise
>                   , isAcom
>                   , isCB, isGLT, isLPT, isGLPT, isSF
>                   , isDot1
>                   -- * Tier-based generalizations
>                   , isTDef, isTRDef, isTGD
>                   , isTSL, isTLT, isTLTT, isTLAcom, isTLPT
>                   , isMTF, isMTDef, isMTRDef, isMTGD
>                   -- * Others between CB and G
>                   , isB, isLB, isTLB
>                   -- * Two-Variable Logics
>                   , isFO2, isFO2B, isFO2BF, isFO2S
>                   -- * Generic Algebra
>                   , isVariety
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
> import LTK.Decide.B
> import LTK.Decide.Acom
> import LTK.Decide.LAcom
> import LTK.Decide.TLAcom
> import LTK.Decide.Definite
> import LTK.Decide.DotDepth
> import LTK.Decide.Trivial
> import LTK.Decide.Multitier
> import LTK.Decide.Variety
