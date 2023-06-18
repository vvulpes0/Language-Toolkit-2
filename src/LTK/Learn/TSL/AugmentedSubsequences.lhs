> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Learn.TSL.AugmentedSubsequences
> Copyright : (c) 2019-2020,2023 Dakotah Lambert
> License   : MIT

> This module implements a string extension learner for the TSL class.
> A variant of the tier-finding algorithm of Jardine and McMullin (2017)
> is used along with a notion of a potential valid tier-factor.
> This is an efficient online conversion of their algorithm.
> 
> For the original work, see https://doi.org/10.1007/978-3-319-53733-7_4
>
> @since 0.3
> -}

> module LTK.Learn.TSL.AugmentedSubsequences(TSLG, fTSL) where

> import Data.Set (Set)
> import qualified Data.Set as Set

> import LTK.FSA
> import LTK.Learn.StringExt
> import LTK.Learn.SL

> -- |Return the set of subsequence-interveners pairs
> -- of length \(k\) in a given word,
> -- as well as the adjacency factors of length \(k\) and \(k+1\).
> -- If a word is short enough to not contain any \(k\)-factors,
> -- the entire word, appropriately anchored, is included in the set.
> fTSL :: Ord a => Int -> [a] -> TSLG a
> fTSL k w = TSLG { tslgAlpha  =  as
>                 , tslgInf    =  inf
>                 , tslgK      =  k
>                 , tslgF      =  fSL k w
>                 , tslgFp1    =  fSL (k + 1) w
>                 , tslg       =  fs
>                 }
>     where fs   =  keep (\(_,b,_) -> f b) $ ssqis w
>           f (h, b, t)
>               = let a = alength (h, b, t)
>                 in (h && t && a <= k) || a == k
>           as   =  collapse (union . (\(a,_,_) -> a)) empty fs
>           inf  =  anyS (\(_,(h,_,t),_) -> not h && not t) fs

> tslgTier :: Ord a => TSLG a -> Set a
> tslgTier g = Set.filter (not . n) (alphabet g)
>     where n   = both r p
>           r x = isSubsetOf (slg $ tslgF g) $ gDrop x (slg $ tslgFp1 g)
>           p x = isSubsetOf (slg $ tslgFp1 g) $ gIn x (slg $ tslgF g)

> slgFromTslg :: Ord a => TSLG a -> SLG a
> slgFromTslg g = SLG { slgAlpha = t
>                     , slgK = tslgK g
>                     , slg = Set.map ex . Set.filter f $ tslg g
>                     }
>     where t = tslgTier g
>           f (x, _, y) = isSubsetOf t x &&
>                         Set.null (intersection y t)
>           ex (_, s, _) = s



> -- |A representation of a TSL grammar.
> data TSLG a = TSLG { tslgAlpha :: Set a
>                    , tslgInf :: Bool
>                    , tslgK :: Int
>                    , tslgF :: SLG a
>                    , tslgFp1 :: SLG a
>                    , tslg :: Set (Set a, (Bool, [a], Bool), Set a)
>                    }
>               deriving (Eq, Ord, Read, Show)

> instance HasAlphabet TSLG
>     where alphabet = tslgAlpha

> instance Grammar TSLG
>     where emptyG = TSLG empty False 0 emptyG emptyG empty
>           augmentG g1 g2
>               = TSLG { tslgAlpha  =  alphabet g1 `union` alphabet g2
>                      , tslgInf    =  tslgInf g1 || tslgInf g2
>                      , tslgK      =  max (tslgK g1) (tslgK g2)
>                      , tslgF      =  augmentG (tslgF g1) (tslgF g2)
>                      , tslgFp1    =  augmentG (tslgFp1 g1) (tslgFp1 g2)
>                      , tslg       =  tslg g1 `union` tslg g2
>                      }
>           isSubGOf g1 g2 = isSubsetOf (tslg g1) (tslg g2)
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
> gSet f = collapse (union . gDo f) empty

> gDo :: (Ord a, Ord b, Ord x, Ord y) =>
>        (a -> Set b) -> (x, a, y) -> Set (x, b, y)
> gDo f (h, s, t) = Set.map (\a -> (h, a, t)) $ f s



> alength :: (Bool, [a], Bool) -> Int
> alength (h, s, t) = f h + f t + length s
>     where f x = if x then 1 else 0

> ssqis :: Ord a => [a] -> Set (Set a, (Bool, [a], Bool), Set a)
> ssqis xs = Set.fromList . (eFF :) . (eTF :) . interleave c $ map f o
>     where f (a, (_, y, z), b) = (a, (True, y, z), b)
>           (c, o) = ssqis' xs
>           eFF = (empty, (False, empty, False), empty)
>           eTF = (empty, (True, empty, False), empty)

The output of the @ssqis'@ function is a pair, each component of which
is a triple listing the elements taken, the subsequence proper,
and the skipped elements, respectively.
The first component of the outer pair
is the complete subsequence-intervener structures,
where no elements prior to the beginning of the subsequence
are listed as skipped.
The other component lists those structures
that still need a beginning to be complete.

> ssqis' :: Ord a => [a]
>        -> ( [(Set a, (Bool, [a], Bool), Set a)]
>           , [(Set a, (Bool, [a], Bool), Set a)]
>           )
> ssqis' []      =  (tailFish, tailFish)
>     where tailFish = [(empty, (False, [], True), empty)]
> ssqis' (x:xs)  =  ( (singleton x, e x, empty) : interleave c took
>                   , (singleton x, e x, empty) : interleave skips took
>                   )
>     where (c, o) =  ssqis' xs
>           took   =  foldr f [] o
>           skips  =  foldr g [] o
>           f (r,s,t) w  =  if isIn t x
>                           then w
>                           else (insert x r, h x s, t) : w
>           g (r,s,t) w  =  if isIn r x
>                           then w
>                           else (r, s, insert x t) : w
>           h a (r,s,t)  =  (r, a : s, t)
>           e a = (False, [a], False)
