> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.GLPT
> Copyright : (c) 2021 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a syntactic
> semigroup \(S\) is, on certain submonoids, Piecewise Testable (MePT).
> This is the case iff for each of its idempotents \(e\) it holds that
> \(eXe\) is \(\mathcal{J}\)-trivial, where X={ege : ugv=e for some u,v}.
> -}
> module LTK.Decide.GLPT (isGLPT) where

> import Data.Set (Set)
> import qualified Data.Set as Set

> import LTK.FSA
> import LTK.Algebra

> -- |True iff the syntactic monoid of the automaton is in
> -- \(\mathbf{M_e J}\).
> -- This is a generalization of LPT in the same way that
> -- GLT is a generalization of LT.
> isGLPT :: (Ord n, Ord e) => FSA n e -> Bool
> isGLPT = mejtest . syntacticMonoid

J-trivial means M_e*e*M_e = e.
We're asking if X=e*M_e*e is J-trivial
That is, if X_e*e*X_e = e for idempotents within X_e.

It does not appear that a shortcut like that used to test for
local J-triviality is viable.  If it turns out to be, then this
file will shrink dramatically and this test will speed up quite
a bit.

> mejtest :: (Ord n, Ord e) => FSA (n, [Symbol e]) e -> Bool
> mejtest   m = all f $ Set.toList i
>     where i = idempotents m
>           f e = all (g e) . Set.toList . Set.intersection i $ emee m e
>           g e h = let x = Set.toList $ xe m (emee m e) h
>                   in (== Set.singleton h) . Set.unions
>                      . map (flip (follow m) qi)
>                      $ [label a ++ label h ++ label b | a <- x, b <- x]
>           qi = Set.findMin $ initials m
>           label = snd . nodeLabel

m  is the monoid as a whole,
x  is the set of states we are restricted to, and
e  is the idempotent we care about
xe is the set of things in x that can rewrite via x to e
   i.e. g\in x s.t. \exists u,v\in x s.t. ugv=e

> xe :: (Ord n, Ord e) =>
>       FSA (n, [Symbol e]) e ->
>       Set (State (n, [Symbol e])) ->
>       State (n, [Symbol e]) -> Set (State (n, [Symbol e]))
> xe m x e = Set.filter (contains e . xgx) x
>     where xgx g = Set.unions
>                   [follow m (label a) q
>                   | q <- Set.toList (xg g), a <- Set.toList x]
>           xg g  = Set.unions . map (follow m (label g))
>                   $ Set.toList x
>           label = snd . nodeLabel
