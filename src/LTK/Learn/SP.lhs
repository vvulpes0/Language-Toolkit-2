> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Learn.SP
> Copyright : (c) 2019 Dakotah Lambert
> License   : MIT

> This module implements a string extension learner for the SP class.
> -}

> module LTK.Learn.SP (SPG, fSP) where

> import Data.Set (Set)
> import qualified Data.Set as Set

> import LTK.Factors
> import LTK.FSA
> import LTK.Learn.StringExt

When gathering subsequences of words to build a positive grammar,
we should keep in mind that if a given subsequence is considered
acceptable, the definition of SP guarantees that in turn all of
its subsequences are also acceptable.  Therefore unlike for SL, it
makes sense to also gather the factors of width less than \(k\)
when generating a grammar from positive data.

> -- |Return the set of factors under precedence of length \(k\) or less
> -- in the given word.
> fSP :: Ord a => Int -> [a] -> SPG a
> fSP k = f . fSP' True k
>     where f (s, g) = SPG { spgAlpha  =  s
>                          , spgK      =  k
>                          , spg       =  g
>                          }

> -- |Auxiliary function to gather subsequences.
> -- If the first argument is True,
> -- gather those of length less than or equal to \(k\).
> -- Otherwise, only gather those of length exactly \(k\).
> fSP' :: Ord a => Bool -> Int -> [a] -> (Set a, Set [a])
> fSP' lt k = foldr g (empty, empty) . ssqs
>     where f = if lt then null . drop k else (==) k . length
>           g x (xs, ys)
>             = ( case x
>                 of (s:[]) -> Set.insert s xs
>                    _      -> xs
>               , (if f x then Set.insert x else id) ys
>               )

> -- |A representation of an SP grammar.
> data SPG a = SPG { spgAlpha :: Set a
>                  , spgK :: Int
>                  , spg :: Set [a]
>                  }
>              deriving (Eq, Ord, Read, Show)

> instance HasAlphabet SPG
>     where alphabet = spgAlpha

> instance Grammar SPG
>     where emptyG = SPG empty 0 empty
>           augmentG g1 g2
>               = SPG { spgAlpha = union (alphabet g1) (alphabet g2)
>                     , spgK = max (spgK g1) (spgK g2)
>                     , spg = union (spg g1) (spg g2)
>                     }
>           isSubGOf g1 g2 = isSubsetOf (spg g1) (spg g2)
>           genFSA g = n . intersectAll .
>                      map (buildLiteral (alphabet g) . forbidden . f) .
>                      Set.toList $ complG g
>               where f = Subsequence . map singleton
>                     n x = normalize x `asTypeOf` x

> complG :: Ord a => SPG a -> Set [a]
> complG g = difference (allFs (spgK g) (alphabet g)) (spg g)

> allFs :: Ord a => Int -> Set a -> Set [a]
> allFs k = Set.fromList . takeWhile ((<= k) . length)
>           . sequencesOver . Set.toList


Efficient subsequence finding for omega-words
=============================================

The @ssqs'@ function computes non-empty subsequences with multiplicity.
For example, the sequence "a" appears twice for "aba".
We then add in the empty subsequence for @ssqs@

> ssqs' :: [a] -> [[a]]
> ssqs' [] = []
> ssqs' (x:xs) = [x] : interleave (map (x:) ys) ys
>     where ys = ssqs' xs

> ssqs :: [a] -> [[a]]
> ssqs = ([]:) . ssqs'
