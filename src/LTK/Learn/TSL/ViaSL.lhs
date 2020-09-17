> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Learn.TSL.ViaSL
> Copyright : (c) 2020 Dakotah Lambert
> License   : MIT

> This module implements a string extension learner for the TSL class.
> A variant of the tier-finding algorithm of Jardine and McMullin (2017)
> is used.
> Under a Gold-style framework of learning in the limit from positive data,
> a strictly local grammar can be reinterpreted as a tier-based grammar.
> 
> For the original work, see https://doi.org/10.1007/978-3-319-53733-7_4
> -}

> module LTK.Learn.TSL.ViaSL(TSLG, fTSL) where

> import Data.Set (Set)
> import qualified Data.Set as Set

> import LTK.FSA
> import LTK.Learn.StringExt
> import LTK.Learn.SL

> -- |Extract information from a word.
> fTSL :: Ord a => Int -> [a] -> TSLG a
> fTSL k w = TSLG { tslGK = fSL k w, tslGK1 = fSL (k + 1) w }

> tslgTier :: Ord a => TSLG a -> Set a
> tslgTier g = Set.filter (not . n) (alphabet g)
>     where n   = both r p
>           r x = isSubsetOf (slg $ tslGK g) $ gDrop x (slg $ tslGK1 g)
>           p x = isSubsetOf (slg $ tslGK1 g) $ gIn x (slg $ tslGK g)

> slgFromTslg :: Ord a => TSLG a -> SLG a
> slgFromTslg g = SLG { slgAlpha = t
>                     , slgK = slgK gk
>                     , slg = keep f (slg gk)
>                     }
>     where gk = tslGK g
>           t = tslgTier g
>           f (_, a, _) = all (isIn t) a



> -- |A representation of a TSL grammar.
> data TSLG a = TSLG { tslGK :: SLG a, tslGK1 :: SLG a }
>               deriving (Eq, Ord, Read, Show)

> instance HasAlphabet TSLG
>     where alphabet = alphabet . tslGK1

> instance Grammar TSLG
>     where emptyG = TSLG emptyG emptyG
>           augmentG g1 g2
>               = TSLG { tslGK   =  augmentG (tslGK g1)  (tslGK g2)
>                      , tslGK1  =  augmentG (tslGK1 g1) (tslGK1 g2)}
>           isSubGOf g1 g2 = isSubGOf (tslGK g1) (tslGK g2)
>                            && isSubGOf (tslGK1 g1) (tslGK1 g2)
>           genFSA g = normalize . desemantify .
>                      tierify (tslgTier g) .
>                      renameSymbolsBy Just .
>                      extendAlphabetTo (alphabet g) .
>                      genFSA $ slgFromTslg g



> gIn :: Ord a => a -> Set (Bool, [a], Bool) -> Set (Bool, [a], Bool)
> gIn x = gSet (putIn x)

> putIn :: Ord a => a -> [a] -> Set [a]
> putIn a = Set.fromList . putIn' a

> putIn' :: a -> [a] -> [[a]]
> putIn' a xs = (a : xs) :
>               case xs
>               of []      ->  []
>                  (y:ys)  ->  map (y :) $ putIn' a ys

> gDrop :: Ord a => a -> Set (Bool, [a], Bool) -> Set (Bool, [a], Bool)
> gDrop x = gSet (dropOneOf x)

> dropOneOf :: Ord a => a -> [a] -> Set [a]
> dropOneOf x = Set.fromList . dropOneOf' x

> dropOneOf' :: Eq a => a -> [a] -> [[a]]
> dropOneOf' _ [] = []
> dropOneOf' a (x:xs)
>     | x /= a = ns
>     | otherwise = xs : ns
>     where ns = map (x :) $ dropOneOf' a xs

> gSet :: (Ord a, Ord b, Ord x, Ord y) =>
>         (a -> Set b) -> Set (x, a, y) -> Set (x, b, y)
> gSet f = collapse (\w -> union (gDo f w)) empty

> gDo :: (Ord a, Ord b, Ord x, Ord y) =>
>        (a -> Set b) -> (x, a, y) -> Set (x, b, y)
> gDo f (h, s, t) = Set.map (\a -> (h, a, t)) $ f s
