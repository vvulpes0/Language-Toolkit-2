> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.LPT
> Copyright : (c) 2021 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a syntactic
> semigroup \(S\) is locally Piecewise Testable (LPT).  This is the
> case iff each of its idempotents \(e\) satisfies the property that
> \(eSe\) is \(\mathcal{J}\)-trivial.
>
> @since 1.0
> -}
> module LTK.Decide.LPT (isLPT, isLPTM) where

> import qualified Data.Set as Set

> import LTK.FSA
> import LTK.Algebra

> -- |True iff the automaton recognizes an LPT stringset.
> isLPT :: (Ord n, Ord e) => FSA n e -> Bool
> isLPT = isLPTM . syntacticMonoid

> -- |True iff the monoid is locally \(\mathcal{J}\)-trivial.
> isLPTM :: (Ord n, Ord e) => SynMon n e -> Bool
> isLPTM m = all (jtriv . ese m) . Set.toList $ idempotents m
>     where jcs     = Set.toList $ jEquivalence m
>           jtriv x = null . filter ((>1) . Set.size)
>                     $ map (Set.intersection x) jcs

Interestingly we can avoid recomputing the J relation
for the subsemigroups, because eae J ebe iff the same
holds on the local subsemigroup.

Suppose e is an idempotent and eae J ebe.
Then S1 eae S1 = S1 ebe S1.
Because e is in S1, there exist u,v such that eae = u ebe v.
Then e eae e = e u ebe v e, and eae = eue ebe eve.
Similarly there exist x,y such that exe eae eye = ebe.
Because both are reachable from the other in this way,
they are J-related even when restricted to elements of the form eSe.

To show the reverse, suppose e is idempotent as before
and suppose that, when restricted to eSe, eae J ebe.
Then eSe eae eSe = eSe ebe eSe.
Because eee=e in eSe, there exist u,v such that eae = eue ebe eve
and similarly there exist x,y such that exe eae eye = ebe.
Because eue, eve, exe, and eye are in S1,
both are reachable from other in the entire semigroup as well.
Thus they are J-related even without the restriction.

By these implications, we need only compute the J-classes once.
Within the local subsemigroups, they are merely restricted to
the subset of elements that exist.  If any fail to be singleton
even under this restriction, then the semigroup is not locally
J-trivial.
