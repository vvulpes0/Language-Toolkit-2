> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.FO2
> Copyright : (c) 2021 Dakotah Lambert
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
>                        isFO2M, isFO2BM, isFO2BFM, isFO2SM) where

> import Data.Set (Set)
> import qualified Data.Set as Set

> import LTK.FSA
> import LTK.Algebra

> type S n e = (n, [Symbol e])

> -- |True iff the automaton recognizes a stringset
> -- representable in \(\mathrm{FO}^{2}[<]\).
> isFO2 :: (Ord n, Ord e) => FSA n e -> Bool
> isFO2 = isFO2M . syntacticMonoid

> -- |True iff the monoid represents a language in \(\mathrm{FO}^{2}[<]\).
> isFO2M :: (Ord n, Ord e) => SynMon n e -> Bool
> isFO2M = uncurry fo2test . fmap states . (>>= id) (,)

A language is FO2[<,+1]-definable iff
for all idempotents e of its semigroup (not monoid) S,
the subsemigroup eSe corresponds to something FO2[<]-definable

> -- |True iff the automaton recognizes a stringset
> -- representable in \(\mathrm{FO}^{2}[<,+1]\).
> isFO2S :: (Ord n, Ord e) => FSA n e -> Bool
> isFO2S = isFO2SM . syntacticMonoid

> -- |True iff the local subsemigroups are in \(\mathrm{FO}^{2}[<]\).
> -- This means the whole is in \(\mathrm{FO}^{2}[<,+1]\).
> isFO2SM :: (Ord n, Ord e) => SynMon n e -> Bool
> isFO2SM s = all (fo2test s . ese s) $ Set.toList (idempotents s)



A syntactic monoid represents an FO2[<]-definable language
iff for all elements x, y, and z it is the case that
(xyz)^{\omega}*y*(xyz)^{\omega} = (xyz)^{\omega}, where
s^{\omega} is the unique element where s^{\omega}*s = s^{\omega}.
This operation is defined for all elements when the monoid comes
from something star-free.

> -- |True iff the submonoid of @monoid@ given by @xs@ is in DA.
> -- Results are unspecified if @xs@ is not actually a submonoid.
> fo2testFull :: (Ord n, Ord e) =>
>               FSA (S n e) e -> Set (State (S n e)) -> Bool
> fo2testFull monoid xs = trivialUnder hEquivalence monoid -- isSF
>                         && (all f $ triples xs) -- in DA
>     where f (x, y, z) = let xyzw = omega monoid ((x $*$ y) $*$ z)
>                         in (xyzw $*$ y) $*$ xyzw == xyzw
>           a $*$ b = Set.findMin $ follow monoid (snd (nodeLabel b)) a

There is a simpler version of this test:
a pattern is in this class iff
every regular element (an element sharing a J-class with an idempotent)
is idempotent.
As discussed in implementing the test for local J-triviality,
moving to a local subsemigroup does not affect the J-classes
(it merely removes elements not under consideration).
So the same simplification works for FO2[<] and FO2[<,+1],
although as discussed in implementing the @GLPT@ test,
the Me-classes may misbehave; so FO2[<,bet] still uses the full test.

> fo2test :: (Ord n, Ord e) =>
>           SynMon n e -> Set (State (S [Maybe n] e)) -> Bool
> fo2test monoid xs = flip Set.isSubsetOf i . Set.unions
>                     . filter (not . Set.disjoint i)
>                     . map (Set.intersection xs)
>                     . Set.toList $ jEquivalence monoid
>     where i = idempotents monoid `Set.union` initials monoid


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
> isFO2B = isFO2BM . syntacticMonoid

> -- |True iff the monoid represents a stringset that satisfies @isFO2B@.
> isFO2BM :: (Ord n, Ord e) => SynMon n e -> Bool
> isFO2BM s = all (fo2testFull s . emee s) $ Set.toList (idempotents s)


> -- |True iff the automaton recognizes a stringset
> -- representable in \(\mathrm{FO}^{2}[<,\mathrm{betfac}]\).
> -- This is like \(\mathrm{FO}^{2}[<,\mathrm{bet}]\)
> -- except betweenness is of entire factors.
> isFO2BF :: (Ord n, Ord e) => FSA n e -> Bool
> isFO2BF = isFO2BFM . syntacticMonoid

> -- |True iff the monoid lies in MeDA*D
> isFO2BFM :: (Ord n, Ord e) => SynMon n e -> Bool
> isFO2BFM = isFO2BM . emblock


Misc
====

> pairs :: Ord a => Set a -> Set (a, a)
> pairs xs = collapse (union . f) empty xs
>     where f x = Set.mapMonotonic ((,) x) xs

> triples :: Ord a => Set a -> Set (a, a, a)
> triples xs = collapse (union . f) empty (pairs xs)
>     where f (a, b) = Set.mapMonotonic (\x -> (x, a, b)) xs
