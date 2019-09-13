> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module : LTK.Porters.Corpus
> Copyright : (c) 2019 Dakotah Lambert
> LICENSE : MIT
> 
> This module provides methods to construct
> prefix-trees of corpora.
> -}
> module LTK.Porters.Corpus (readCorpus) where

> import Data.Set (Set)
> import qualified Data.Set as Set

> import LTK.FSA hiding (reverse)

> -- |Construct a prefix-tree of a (finite) corpus.
> readCorpus :: Ord a => [[a]] -> FSA [a] a
> readCorpus = f . foldr addWord (empty, empty, empty)
>     where f (alpha, trans, fin)
>               = FSA
>                 { alphabet = alpha
>                 , transitions = trans
>                 , initials = singleton $ State []
>                 , finals = fin
>                 , isDeterministic = False
>                 }

> addWord :: (Ord a) =>
>            [a] -> (Set a, Set (Transition [a] a), Set (State [a])) ->
>            (Set a, Set (Transition [a] a), Set (State [a]))
> addWord w (alpha, trans, fin)
>     = ( collapse insert alpha w
>       , union trans trans'
>       , insert (State w) fin
>       )
>     where trans' = Set.fromList .
>                    map
>                    (\x ->
>                     Transition
>                     { edgeLabel = Symbol $ head x
>                     , source = State . reverse $ drop 1 x
>                     , destination = State $ reverse x
>                     }
>                    ) .
>                    takeWhile (not . null) .
>                    iterate (drop 1) $
>                    reverse w
