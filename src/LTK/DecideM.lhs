> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.DecideM
> Copyright : (c) 2021 Dakotah Lambert
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
> -}
> module LTK.DecideM (
>                    -- * Piecewise classes
>                      isPTM
>                    -- * Local classes
>                    , isDefM, isRDefM, isGDM
>                    , isLTM, isLTTM
>                    -- * Both Local and Piecewise
>                    , isCBM, isGLTM, isLPTM, isGLPTM, isSFM
>                    -- * Tier-based generalizations
>                    , isTDefM, isTRDefM, isTGDM
>                    , isTLTM, isTLTTM, isTLPTM
>                   -- * Others between CB and G
>                   , isBM, isLBM, isTLBM
>                    -- * Two-Variable Logics
>                    , isFO2M, isFO2BM, isFO2SM
>                   ) where

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
> import LTK.Decide.Definite
