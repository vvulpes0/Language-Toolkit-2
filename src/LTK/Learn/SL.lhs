> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Learn.SL
> Copyright : (c) 2019 Dakotah Lambert
> License   : MIT

> This module implements a string extension learner for the SL class.
> -}

> module LTK.Learn.SL (SLG(..), fSL) where

> import Data.Set (Set)
> import qualified Data.Set as Set

> import LTK.Factors
> import LTK.FSA
> import LTK.Learn.StringExt

> -- |Return the set of \(k\)-factors under successor in the given word.
> -- Factors are triples, where the first and last components are
> -- Booleans that indicate whether the factor is anchored at
> -- its head or tail, respectively, and the central component is
> -- the factor itself.
> -- If a word is short enough to not contain any \(k\)-factors,
> -- the entire word, appropriately anchored, is included in the set.
> fSL :: Ord a => Int -> [a] -> SLG a
> fSL = fSL' True

> fSL' :: Ord a => Bool -> Int -> [a] -> SLG a
> fSL' h k w
>     | null (drop (k' - 1) w)  =  mkSLG k (h, w, True)
>     | otherwise               =  augmentG (mkSLG k (h, take k' w, False)) $
>                                  fSL' False k w'
>     where k' = if h then k - 1 else k
>           w' = if h then w else drop 1 w

> -- |A representation of an SL grammar.
> data SLG a = SLG { slgAlpha :: Set a
>                  , slgK :: Int
>                  , slg :: Set (Bool, [a], Bool)
>                  }
>              deriving (Eq, Ord, Read, Show)

> mkSLG :: Ord a => Int -> (Bool, [a], Bool) -> SLG a
> mkSLG k x@(_,b,_) = SLG { slgAlpha  =  Set.fromList b
>                         , slgK      =  k
>                         , slg       =  singleton x
>                         }

> instance HasAlphabet SLG
>     where alphabet = slgAlpha

> instance Grammar SLG
>     where emptyG = SLG empty 0 empty
>           augmentG g1 g2
>               = SLG { slgAlpha = union (alphabet g1) (alphabet g2)
>                     , slgK = max (slgK g1) (slgK g2)
>                     , slg = union (slg g1) (slg g2)
>                     }
>           isSubGOf g1 g2 = isSubsetOf (slg g1) (slg g2)
>           genFSA g = n . intersectAll .
>                      map (buildLiteral (alphabet g) . forbidden . f) .
>                      Set.toList $ complG g
>               where f (h, b, t) = Substring (map singleton b) h t
>                     n x = normalize x `asTypeOf` x

> complG :: Ord a => SLG a -> Set (Bool, [a], Bool)
> complG g = difference (allFs (slgK g) (alphabet g)) (slg g)

> -- |All possible factors of width \(k\) under adjacency,
> -- as well as shorter fully-anchored factors.
> allFs :: Ord a => Int -> Set a -> Set (Bool, [a], Bool)
> allFs k s = allFs' k s (singleton []) empty 0

> allFs' :: Ord a =>
>           Int -> Set a -> Set [a] -> Set (Bool, [a], Bool) -> Int ->
>           Set (Bool, [a], Bool)
> allFs' k s o c n
>     | n == k     =  union c g
>     | otherwise  =  allFs' k s o' (union c g) (n + 1)
>     where f x  =  union (Set.mapMonotonic (x :) o)
>           o'   =  collapse f empty s
>           g
>               | n == k      =  g' False False
>               | n == k - 1  =  union (g' False True) (g' True False)
>               | otherwise   =  g' True True
>           g' h t = Set.mapMonotonic (\b -> (h, b, t)) o
