> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.DecideS
> Copyright : (c) 2023 Dakotah Lambert
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
> @since 1.2
> -}
> module LTK.DecideS (
>                    -- * Piecewise classes
>                      isPTs
>                    -- * Local classes
>                    , isDefs, isRDefs, isGDs
>                    , isLTs, isLTTs, isLAcoms
>                    -- * Both Local and Piecewise
>                    , isAcoms
>                    , isCBs, isGLTs, isLPTs, isGLPTs, isSFs
>                    , isDot1s
>                    -- * Tier-based generalizations
>                    , isTDefs, isTRDefs, isTGDs
>                    , isTLTs, isTLTTs, isTLAcoms, isTLPTs
>                    , isMTFs, isMTDefs, isMTRDefs, isMTGDs
>                   -- * Others between CB and G
>                   , isBs, isLBs, isTLBs
>                    -- * Two-Variable Logics
>                    , isFO2s, isFO2Bs, isFO2Ss
>                   ) where

> --import LTK.Decide.Finite
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
> import LTK.Decide.DotDepth
> import LTK.Decide.Multitier
> --import LTK.Decide.Variety
