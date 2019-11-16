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
> import LTK.FSA hiding (reverse)
> import LTK.Learn.StringExt

For SL, it suffices to gather the factors of width exactly \(k\),
except in the case of shorter words, because the markedness of words
of length less than \(k\) is arbitrary.  The same does not hold for SP,
where closure under deletion guarantees that any subsequence of
a permitted subsequence is also permitted.

> -- |Return the set of factors under precedence of length \(k\) or less
> -- in the given word.
> fSP :: Ord a => Int -> [a] -> SPG a
> fSP k = f . fSP' True empty empty empty k
>     where f (s, g) = SPG { spgAlpha  =  s
>                          , spgK      =  k
>                          , spg       =  g
>                          }

> -- |Auxiliary function to gather subsequences.
> -- If the first argument is True,
> -- gather those of length less than or equal to \(k\).
> -- Otherwise, only gather those of length exactly \(k\).
> fSP' :: Ord a =>
>         Bool -> Set a -> Set [a] -> Set [a] -> Int -> [a] ->
>         (Set a, Set [a])
> fSP' lt as o c _ []     =  if lt
>                            then (as, insert [] . union c $ tmap reverse o)
>                            else (as, c)
> fSP' lt as o c k (x:v)  =  fSP' lt (insert x as) (insert [x] o') c' k v
>     where (o', c') = collapse f (o, c) o
>           f s (a, b)
>               | null (drop (k - 2) s) = (Set.insert (x : s) a, b)
>               | otherwise             = (a, Set.insert (reverse (x : s)) b)

The function fSP' is written in a more complicated way
than one might expect.  This is to prevent having to generate
the same set of subsequences repeatedly in longer words.
In a naive implementation, finding the 3-factors of the string
"abcdefghijkl" might require finding the 2-factors of "jkl"
a total of nine times: once for each prior potential initial symbol.

The modified function as provided here avoids this situation
and is tail-recursive.

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
> allFs k s = allFs' k s (singleton []) empty 0

> allFs' :: Ord a => Int -> Set a -> Set [a] -> Set [a] -> Int -> Set [a]
> allFs' k s o c n
>     | n == k     =  union c o
>     | otherwise  =  allFs' k s o' (union c o) (n + 1)
>     where f x  =  union (Set.mapMonotonic (x :) o)
>           o'   =  collapse f empty s
