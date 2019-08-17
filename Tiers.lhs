> module Tiers (tier, project) where

> import FSA
> import Containers
> import Data.Set (Set)
> import qualified Data.Set as Set

If a given FSA is the preprojection of some constraint,
then symbols are freely insertable and deletable
if they do not appear in the associated projection.
For a normal-form DFA, then,
these symbols are self loops on every state.

> -- |Determine the tier alphabet for which the given FSA is a preprojection.
> -- This could simply be the entire alphabet of the FSA.
> -- Precondition: the given FSA must be in normal form.
> tier :: (Ord n, Ord e) => FSA n e -> Set e
> tier fsa = Set.difference (alphabet fsa) (unsymbols tc)
>     where f q  =  Set.mapMonotonic (edgeLabel) .
>                   Set.filter (\t -> source t == q && destination t == q) $
>                   transitions fsa
>           tc   =  intersectAll (tmap f (states fsa))

> -- |Remove symbols not relevant to the given FSA's associated projection
> -- (as determined by @tier@).
> -- Precondition: the given FSA must be in normal form.
> project :: (Ord n, Ord e) => FSA n e -> FSA n e
> project fsa = contractAlphabetTo (tier fsa) fsa

If the projection is SL, the given FSA is TSL.
If the projection is LT, the given FSA is TLT.
etc.
