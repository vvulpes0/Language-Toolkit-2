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

> import LTK.FSA

> -- |Construct a prefix-tree of a (finite) corpus.
> readCorpus :: Ord a => [[a]] -> FSA [a] a
> readCorpus = f . foldr addWord (empty, empty, empty)
>     where f (alpha, trans, fin)
>               = FSA
>                 { sigma = alpha
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
>     where trans' = Set.fromList $ f (inits w) w
>           f (x:y:xs) (z:zs)
>               = Transition
>                 { edgeLabel = Symbol z
>                 , source = State x
>                 , destination = State y
>                 } : f (y:xs) zs
>           f _ _ = []
>           inits xs = [] :
>                      case xs
>                      of []      ->  []
>                         (a:as)  ->  map (a :) (inits as)
