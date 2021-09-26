> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Decide.LT
> Copyright : (c) 2019 Dakotah Lambert
> License   : MIT

> This module implements an algorithm to decide whether a given FSA
> is Locally Testable (LT) based on the semigroup characterization
> of Brzozowski and Simon from their 1973 work
> "Characterizations of locally testable events".
>
> @since 0.2
> -}
> module LTK.Decide.LT (isLT) where

> import Data.Set (Set)
> import qualified Data.Set as Set

> import LTK.FSA
> import LTK.Algebra

> -- |True iff the automaton recognizes an LT stringset.
> isLT :: (Ord n, Ord e) => FSA n e -> Bool
> isLT = isSynMonOfLT . syntacticMonoid

A semigroup (S) [e.g. the syntactic semigroup] is locally testable iff
for all idempotent e, the generated subsemigroup eSe is an idempotent
commutative monoid.

> isSynMonOfLT :: (Ord n, Ord e) =>
>                 FSA (n, [Symbol e]) e -> Bool
> isSynMonOfLT s = all (both (isCommutative s) (isSubsetOf i) .
>                       generatedSubsemigroup s
>                      ) $ Set.toList i
>     where i = idempotents s

> generatedSubsemigroup :: (Ord n, Ord e) =>
>                          FSA (n, [Symbol e]) e -> State (n, [Symbol e]) ->
>                          Set (State (n, [Symbol e]))
> generatedSubsemigroup f x
>     = collapse (union . follow f (snd $ nodeLabel x)) empty $
>       primitiveIdealR f x
