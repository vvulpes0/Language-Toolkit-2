> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module    : LTK.Learn.TSL
> Copyright : (c) 2019 Dakotah Lambert
> License   : MIT

> This module implements a string extension learner for the TSL class.
> A variant of the tier-finding algorithm of Jardine and McMullin (2017)
> is used along with a notion of a potential valid tier-factor.
> This is an efficient online conversion of their algorithm.
> 
> For the original work, see https://doi.org/10.1007/978-3-319-53733-7_4
> -}

> module LTK.Learn.TSL(TSLG, fTSL) where

> import Data.Set (Set)
> import qualified Data.Set as Set

> import LTK.FSA hiding (reverse)
> import LTK.Learn.StringExt
> import LTK.Learn.SL

> -- |Return the set of subsequence-interveners pairs
> -- of length \(k\) in a given word,
> -- as well as the adjacency factors of length \(k\) and \(k+1\).
> -- If a word is short enough to not contain any \(k\)-factors,
> -- the entire word, appropriately anchored, is included in the set.
> fTSL :: Ord a => Int -> [a] -> TSLG a
> fTSL k w = let (as, inf, fs) = fTSL' empty False empty empty k w
>            in TSLG { tslgAlpha  =  as
>                    , tslgInf    =  inf
>                    , tslgK      =  k
>                    , tslgF      =  fSL k w
>                    , tslgFp1    =  fSL (k + 1) w
>                    , tslg       =  fs
>                    }

> fTSL' :: Ord a =>
>          Set a -> Bool ->
>          Set (Set a, Bool, Set a, [a], Set a) ->
>          Set (Set a, (Bool, [a], Bool), Set a) ->
>          Int -> [a] ->
>          (Set a, Bool, Set (Set a, (Bool, [a], Bool), Set a))
> fTSL' as inf o c k [] = (as, inf, c')
>     where c' = collapse f c o
>           f (p, z, s', s, i) x = (if z && sh then gb else id) .
>                                  (if not sh  then gt else id) $ x
>               where gb = Set.insert (s', (True, r, True), Set.union p i)
>                     gt = Set.insert (s', (False, r, True), i)
>                     r  = reverse s
>                     sh = null $ drop (k - 2) s
> fTSL' as inf o c k (x:v)
>     = fTSL' (insert x as) (inf || (not . null $ drop (k - 1) v))
>       (insert (as, isNotIn as x, singleton x, [x], empty) o')
>       c' k v
>     where (o', c') = collapse f (empty, c) o
>           f (p, z, s', s, i) (a, b)
>               | null s = (insert (insert x p, True, s', s, i) a, b)
>               | not $ null (drop (k - 2) s) -- have a (k-1)-factor
>                   = if isIn s x
>                     then ( a
>                          , insert
>                            (insert x s', (False, reverse (x:s), False), i)
>                            b
>                          )
>                     else ( flip insert a
>                            (p, z && isNotIn p x, s', s, insert x i)
>                          , (if isNotIn i x
>                             then Set.insert ( insert x s'
>                                             , (False, reverse (x:s), False)
>                                             , i
>                                             )
>                             else id
>                            ) $ b
>                          )
>               | otherwise
>                   = ( (if isNotIn i x
>                        then insert
>                             (p, isNotIn p x, Set.insert x s', x : s, i)
>                        else id
>                       ) .
>                       (if isNotIn s x
>                        then Set.insert
>                             (p, z && isNotIn p x, s', s, insert x i)
>                        else id
>                       ) $ a
>                     , (if z && isNotIn (union i p) x &&
>                           not (null $ drop (k - 3) s)
>                        then insert ( insert x s'
>                                    , (True, reverse (x : s), False)
>                                    , union i p
>                                    )
>                        else id
>                       ) $ b
>                     )

That gigantic function gets the subsequence-interveners pairs of a word.
Given a tier-alphabet T, the set of permitted tier-factors is the subset
of this set consisting of all and only those elements for which:

* the subsequence component only contains elements from T, and
* the interveners component is disjoint with T.

> tslgTier :: Ord a => TSLG a -> Set a
> tslgTier g = Set.filter (not . n) (alphabet g)
>     where n x = r x && p x
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
>               = TSLG { tslgAlpha  =  union (alphabet g1) (alphabet g2)
>                      , tslgInf    =  tslgInf g1 || tslgInf g2
>                      , tslgK      =  max (tslgK g1) (tslgK g2)
>                      , tslgF      =  augmentG (tslgF g1) (tslgF g2)
>                      , tslgFp1    =  augmentG (tslgFp1 g1) (tslgFp1 g2)
>                      , tslg       =  union (tslg g1) (tslg g2)
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
> putIn x = putIn' x Set.empty []

> putIn' :: Ord a => a -> Set [a] -> [a] -> [a] -> Set [a]
> putIn' x c r s
>     | (u:v) <- s = putIn' x c' (u : r) v
>     | otherwise  = c'
>     where c' = insert (reverse (x : r) ++ s) c

> gDrop :: Ord a => a -> Set (Bool, [a], Bool) -> Set (Bool, [a], Bool)
> gDrop x = gSet (dropOneOf x)

> dropOneOf :: Ord a => a -> [a] -> Set [a]
> dropOneOf x = dropOneOf' x Set.empty []

> dropOneOf' :: Ord a => a -> Set [a] -> [a] -> [a] -> Set [a]
> dropOneOf' _ c _ [] = c
> dropOneOf' x c r (u:v) = dropOneOf' x c' (u : r) v
>     where c' = if u == x
>                then Set.insert ((reverse r) ++ v) c
>                else c

> gSet :: (Ord a, Ord b, Ord x, Ord y) =>
>         (a -> Set b) -> Set (x, a, y) -> Set (x, b, y)
> gSet f = collapse (\w -> union (gDo f w)) empty

> gDo :: (Ord a, Ord b, Ord x, Ord y) =>
>        (a -> Set b) -> (x, a, y) -> Set (x, b, y)
> gDo f (h, s, t) = Set.map (\a -> (h, a, t)) $ f s
