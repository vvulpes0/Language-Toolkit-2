> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.SF
> Copyright : (c) 2019 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is Star-Free (SF) based on the semigroup characterization
> of Schutzenberger as reported by Pin in his chapter
> "Syntactic Semigroups" of "Handbook of Formal Languages"
> -}
> module LTK.Decide.SF (isSF) where

> import LTK.FSA

> -- |True iff the automaton recognizes a Star-Free stringset.
> isSF :: (Ord n, Ord e) => FSA n e -> Bool
> isSF = trivialUnder hEquivalence . syntacticMonoid
