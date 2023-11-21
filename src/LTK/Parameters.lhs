> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Parameters
> Copyright : (c) 2023 Dakotah Lambert
> License   : MIT
> 
> Many subregular classes are parameterized.
> In some cases, we know not only how to decide membership,
> but also the values of these parameters.
> As a general interface, each parameterization function
> returns a @Maybe [Parameter e]@,
> where @Nothing@ means the language is not in the class
> and @Just xs@ indicates for which parameters this membership holds.
> The interpretation of the list differs per class;
> consult the individual functions' documentation for more information.
>
> All arguments should be given in minimal form.
> This is never checked.
> -}
> module LTK.Parameters ( Parameter(..)
>                       , pTier
>                       , pDef, pRDef, pGDef
>                       , pCB, pAcom
>                       , pSL, pSP
>                       ) where

> import Data.Representation.FiniteSemigroup
> import Data.Set (Set)
> import qualified Data.IntSet as IntSet
> import qualified Data.Set as Set

> import LTK.FSA
> import LTK.Decide
> import LTK.Extract.SL (slQ)
> import LTK.Tiers (project, tier)

> data Parameter e = PInt String Int
>                  | PSymSet String (Set e)
>                    deriving (Eq, Ord, Read, Show)

> -- |If there are neutral symbols, test a class
> -- and prepend to its parameters the set of salient symbols.
> pTier :: (Ord n, Ord e) => (FSA n e -> Maybe [Parameter e])
>       -> FSA n e -> Maybe [Parameter e]
> pTier pX f = (PSymSet "T" (tier f) :) <$> pX (project f)

> -- |Returns an empty parameter list.
> pCB :: (Ord n, Ord e) => FSA n e -> Maybe [Parameter e]
> pCB = fmap (const []) . predicated isCB

I am confident that all of the below are out there in the literature.
But it's very hard to search for these things.
So, no citations, sorry, I had to figure them out on my own.

> -- |Return the length of the longest relevant suffix.
> pDef :: (Ord n, Ord e) => FSA n e -> Maybe [Parameter e]
> pDef  = fmap (wrap "k" . pred . rchain) . predicated isDef
> -- |Return the length of the longest relevant prefix.
> pRDef :: (Ord n, Ord e) => FSA n e -> Maybe [Parameter e]
> pRDef = fmap (wrap "k" . pred . rchain) . predicated isRDef
> -- |Return the length of the longest relevant suffix or prefix,
> -- whichever is longer.
> pGDef :: (Ord n, Ord e) => FSA n e -> Maybe [Parameter e]
> pGDef = fmap (wrap "k" . pred . rchain) . predicated isGD

> -- |Return the threshold at which symbol counting saturates.
> pAcom :: (Ord n, Ord e) => FSA n e -> Maybe [Parameter e]
> pAcom f = fmap (const (wrap "t" m)) $ predicated isAcom f
>     where s = syntacticSemigroup f
>           sz = IntSet.size . subsemigroup s . IntSet.singleton
>           m = maximum $ map sz [0 .. fsnbases s]

SP is my own algorithm,
explained in "Extracting subregular constraints from regular stringsets"
(https://doi.org/10.15398/jlm.v7i2.209).
I do not believe the parameter-finding is explicitly discussed,
but it follows from the extraction procedure.

> -- |Return the length of the longest relevant subsequence.
> pSP :: (Ord n, Ord e) => FSA n e -> Maybe [Parameter e]
> pSP = fmap (wrap "k" . dagHeight . simplify) . predicated isSP
>     where deloop f = f { transitions
>                              = Set.filter
>                                (\t -> source t /= destination t)
>                                (transitions f)
>                        }
>           simplify = deloop . renameSymbolsBy (const ())

The SL algorithm is explained in the same paper as the SP one,
and is actually how we check for SL membership in the first place.

> -- |Return the length of the longest relevant substring.
> pSL :: (Ord n, Ord e) => FSA n e -> Maybe [Parameter e]
> pSL = fmap (wrap "k" . fromIntegral) . predicated (> 0)
>       . slQ . normalize


Helpers
=======

> wrap :: String -> Int -> [Parameter e]
> wrap s = pure . PInt s

> predicated :: (a -> Bool) -> a -> Maybe a
> predicated p x = if p x then Just x else Nothing

> -- |Return the length of the longest (strictly) ascending R-chain
> -- in the syntactic monoid, in terms of the number of elements.
> rchain :: (Ord n, Ord e) => FSA n e -> Int
> rchain = succ . dagHeight . sccGraph . rorder . syntacticMonoid
>     where rorder m = orderGraph (r m) m
>           r m x y = State y `Set.member` primitiveIdealR m (State x)

> -- |Return the number of edges in the longest path of a DAG.
> -- The precondition, that the graph be a DAG, is not checked.
> -- As a special case, return (-1) for a single-state (trivial) graph
> dagHeight :: Ord n => FSA n () -> Int
> dagHeight f = dagHeight' f (initials f)
> dagHeight' :: Ord n => FSA n () -> Set (State n) -> Int
> dagHeight' f xs
>     | Set.null ns = 0
>     | otherwise = 1 + dagHeight' f ns
>     where ts = transitions f
>           ns = Set.unions
>                . map (\x -> Set.map destination
>                      $ extractMonotonic source x ts)
>                $ Set.toList xs
