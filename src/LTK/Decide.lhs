> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide
> Copyright : (c) 2019 Dakotah Lambert
> License   : BSD-style, see LICENSE
> 
> Functions used for extracting constraints from automata.
> Each complexity class for which these operations are implemented
> has a separate Extract.<Class> module as well.
> -}
> module LTK.Decide (isSL, isLT, isTSL, isTLT, isSP, isPT, isSF) where
> import LTK.Decide.SL
> import LTK.Decide.LT
> import LTK.Decide.TSL
> import LTK.Decide.TLT
> import LTK.Decide.SP
> import LTK.Decide.PT
> import LTK.Decide.SF