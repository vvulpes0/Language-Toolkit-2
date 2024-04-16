> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.FO2
> Copyright : (c) 2021-2024 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is representable in two-variable logic based on the semigroup
> characterization as reported by Thérien and Wilke in their 1998
> STOC article: https://doi.org/10.1145/276698.276749

> Two-variable logic with general precedence is a strict superclass
> of PT while still being a strict subclass of star-free.  It
> represents exactly the class of properties expressible in temporal
> logic using only the "eventually in the future/past" operators.

> The section regarding betweenness is built on Krebs et al. (2020):
> https://doi.org/10.23638/LMCS-16(3:16)2020
>
> @since 1.0
> -}
> module LTK.Decide.FO2 (isFO2, isFO2B, isFO2BF, isFO2S,
>                        isFO2M, isFO2BM, isFO2BFM, isFO2SM,
>                        isFO2s, isFO2Bs, isFO2Ss) where

> import Data.Representation.FiniteSemigroup

> import LTK.FSA
> import LTK.Algebra(SynMon,emblock)

> -- |True iff the automaton recognizes a stringset
> -- representable in \(\mathrm{FO}^{2}[<]\).
> isFO2 :: (Ord n, Ord e) => FSA n e -> Bool
> isFO2 = isFO2s . syntacticSemigroup

> -- |True iff the monoid represents a language in \(\mathrm{FO}^{2}[<]\).
> isFO2M :: (Ord n, Ord e) => SynMon n e -> Bool
> isFO2M = isFO2

> -- |True iff the monoid represents a language in \(\mathrm{FO}^{2}[<]\).
> --
> -- @since 1.2
> isFO2s :: FiniteSemigroupRep s => s -> Bool
> isFO2s = isDA

A language is FO2[<,+1]-definable iff
for all idempotents e of its semigroup (not monoid) S,
the subsemigroup eSe corresponds to something FO2[<]-definable

> -- |True iff the automaton recognizes a stringset
> -- representable in \(\mathrm{FO}^{2}[<,+1]\).
> isFO2S :: (Ord n, Ord e) => FSA n e -> Bool
> isFO2S = isFO2Ss . syntacticSemigroup

> -- |True iff the local submonoids are in \(\mathrm{FO}^{2}[<]\).
> -- This means the whole is in \(\mathrm{FO}^{2}[<,+1]\).
> isFO2SM :: (Ord n, Ord e) => SynMon n e -> Bool
> isFO2SM = isFO2S

> -- |True iff the local submonoids are in \(\mathrm{FO}^{2}[<]\).
> -- This means the whole is in \(\mathrm{FO}^{2}[<,+1]\).
> --
> -- @since 1.2
> isFO2Ss :: FiniteSemigroupRep s => s -> Bool
> isFO2Ss = locally isDA


A syntactic monoid represents an FO2[<]-definable language
iff for all elements x, y, and z it is the case that
(xyz)^{\omega}*y*(xyz)^{\omega} = (xyz)^{\omega}, where
s^{\omega} is the unique element where s^{\omega}*s = s^{\omega}.


For betweenness:

A language is representable in FO2[<,bet] iff its syntactic monoid
is in MeDA.

> -- |True iff the automaton recognizes a stringset
> -- representable in \(\mathrm{FO}^{2}[<,\mathrm{bet}]\).
> -- Labelling relations come in the typical unary variety
> -- \(\sigma(x)\) meaning a \(\sigma\) appears at position \(x\),
> -- and also in a binary variety
> -- \(\sigma(x,y)\) meaning a \(\sigma\) appears strictly between
> -- the positions \(x\) and \(y\).
> isFO2B :: (Ord n, Ord e) => FSA n e -> Bool
> isFO2B = isFO2Bs . syntacticSemigroup

> -- |True iff the monoid represents a stringset that satisfies @isFO2B@.
> isFO2BM :: (Ord n, Ord e) => SynMon n e -> Bool
> isFO2BM = isFO2B

> -- |True iff the semigroup represents a stringset
> -- that satisfies @isFO2B@.
> --
> -- @since 1.2
> isFO2Bs :: FiniteSemigroupRep s => s -> Bool
> isFO2Bs = all isDA . emee


> -- |True iff the automaton recognizes a stringset
> -- representable in \(\mathrm{FO}^{2}[<,\mathrm{betfac}]\).
> -- This is like \(\mathrm{FO}^{2}[<,\mathrm{bet}]\)
> -- except betweenness is of entire factors.
> --
> -- @since 1.1
> isFO2BF :: (Ord n, Ord e) => FSA n e -> Bool
> isFO2BF = isFO2BFM . syntacticMonoid

> -- |True iff the monoid lies in MeDA*D
> --
> -- @since 1.1
> isFO2BFM :: (Ord n, Ord e) => SynMon n e -> Bool
> isFO2BFM = isFO2BM . emblock
