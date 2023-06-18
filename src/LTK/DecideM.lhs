> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.DecideM
> Copyright : (c) 2021-2023 Dakotah Lambert
> License   : MIT
>
> Functions used for deciding the complexity class of a monoid.
> Each complexity class for which these operations are implemented
> has a separate Decide.classM module as well.  Many of the functions
> in @LTK.Decide@ use these functions internally, so using these
> directly prevents rederiving the monoid when many tests are desired.
>
> One may note that @LTK.Decide@ contains strictly more tests.
> The classes not closed under complementation are not classified
> by their syntactic monoids or semigroups, but by properties of
> the automaton from which it was derived.
>
> @since 1.0
> -}
> module LTK.DecideM (
>                    -- * Classes involving finiteness
>                    isFiniteM, isCofiniteM
>                    , isTFiniteM, isTCofiniteM
>                    -- * Piecewise classes
>                    , isPTM
>                    -- * Local classes
>                    , isDefM, isRDefM, isGDM
>                    , isLTM, isLTTM, isLAcomM
>                    -- * Both Local and Piecewise
>                    , isAcomM
>                    , isCBM, isGLTM, isLPTM, isGLPTM, isSFM
>                    -- * Tier-based generalizations
>                    , isTDefM, isTRDefM, isTGDM
>                    , isTLTM, isTLTTM, isTLAcomM, isTLPTM
>                    , isMTFM, isMTDefM, isMTRDefM, isMTGDM
>                   -- * Others between CB and G
>                   , isBM, isLBM, isTLBM
>                    -- * Two-Variable Logics
>                    , isFO2M, isFO2BM, isFO2BFM, isFO2SM
>                    -- * Generic Algebra
>                    , isVarietyM
>                   ) where

> import LTK.Decide.Finite
> import LTK.Decide.LT
> import LTK.Decide.LPT
> import LTK.Decide.LTT
> import LTK.Decide.TLT
> import LTK.Decide.TLTT
> import LTK.Decide.TLPT
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
> import LTK.Decide.Multitier
> import LTK.Decide.Variety
