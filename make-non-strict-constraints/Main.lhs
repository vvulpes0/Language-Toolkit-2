> module Main (main) where

> import Control.DeepSeq (NFData, ($!!))
> import System.IO (IOMode(WriteMode), hFlush, hPutStr, withFile)
> import Data.Set (Set)
> import qualified Data.Set as Set (toAscList)

> import Control.Parallel.Strategies (parListChunk, rdeepseq, using)

> import LTK.ConstraintCompiler(compile)
> import LTK.Porters(ATT(ATT), to, untransliterate)
> import LTK.Porters.ATT(extractSymbolsATT)
> import LTK.Factors ( Factor(Substring), forbidden, required )
> import LTK.FSA


> c89, c9x, c91, c145, c146 :: FSA Integer String
> c89 = compile wx [[required (Substring [wxs2] False False)]]
> c9x = compile wx [[ forbidden (Substring [wpluss0] False False)
>                   , forbidden (Substring [w1s2] False True)]
>                   ]
> c91 = compile wx [[ forbidden (Substring [wpluss1] False False)
>                   , forbidden (Substring [w1s2] False True)]
>                   ]
> c145 = desurfaceSecondary $ compile wx
>        [ [forbidden (Substring [w0plus, w0plus] False False)]
>        , [forbidden (Substring [w0s0,w0s0] False False)]
>        , [forbidden (Substring [wplus, w0plus] False False)]
>        , [forbidden (Substring [w0plus] True False)]
>        ]
> c146 = renameStates . minimize $ unionAll
>        [ compile wx [[forbidden (Substring [w0s2] False False)]]
>        , c145
>        , compile wx [[required (Substring [w0s2] True True)]]
>        ]

> desurfaceSecondary :: (Enum n1, Ord n, Ord n1) =>
>                       FSA n String -> FSA n1 String
> desurfaceSecondary
>     = renameStates . minimize . renameSymbolsBy f
>     where f x = case ( tr (Set.toAscList wxs1) (Set.toAscList wxs0)
>                      $ singleton x) of
>                   (a:_) -> a
>                   _ -> x

> nonEmptySubsets :: (Ord n, NFData e, Ord e) =>
>                    [(String, FSA n e)] -> [(String, FSA Int e)]
> nonEmptySubsets []      =  []
> nonEmptySubsets [x]     =  [fmap renameStates x]
> nonEmptySubsets (x:xs)  =  f x : map (combine (f x)) xs' ++ xs'
>     where xs'  =  nonEmptySubsets xs
>           f    =  fmap renameStates
>           combine (s1, f1) (s2, f2)
>               =  ( s1 `seq` s2 `seq` s1 ++ "_" ++ drop 1 s2
>                  , normalize' $!! intersection f1 f2)

> normalize' :: (Ord n, Ord e) => FSA n e -> FSA Int e
> normalize' = renameStates . minimize

> main :: IO ()
> main = mapM_ (uncurry write) (constraints `using` parListChunk 1 rdeepseq)
>     where prepare (a, b)  =  (a, f . to ATT $ untransliterate b)
>           f               =  (\(a,_,_) -> a) . extractSymbolsATT
>           constraints     =  map prepare $
>                              nonEmptySubsets
>                              [ ("c89",  c89)
>                              , ("c9x",  c9x)
>                              , ("c91",  c91)
>                              , ("c145", c145)
>                              , ("c146", c146)
>                              ]

> write :: FilePath -> String -> IO ()
> write fp str = withFile fp WriteMode $ \h ->
>                do hPutStr h str
>                   hFlush h


Symbols
=======

> w0s0, w0s1, w0s2, w1s0, w1s1, w1s2 :: Set String
> w2s0, w2s1, w2s2, w3s0, w3s1, w3s2 :: Set String
> w4s0, w4s1, w4s2, wxs0, wxs1, wxs2 :: Set String
> -- |Light, unstressed
> w0s0 = singleton "L"
> -- |Light, secondary stress
> w0s1 = singleton "L`"
> -- |Light, primary stress
> w0s2 = singleton "L'"
> -- |Heavy, unstressed
> w1s0 = singleton "H"
> -- |Heavy, secondary stress
> w1s1 = singleton "H`"
> -- |Heavy, primary stress
> w1s2 = singleton "H'"
> -- |Superheavy, unstressed
> w2s0 = singleton "S"
> -- |Superheavy, secondary stress
> w2s1 = singleton "S`"
> -- |Superheavy, primary stress
> w2s2 = singleton "S'"
> -- |Weight 3, unstressed
> w3s0 = singleton "X"
> -- |Weight 3, secondary stress
> w3s1 = singleton "X`"
> -- |Weight 3, primary stress
> w3s2 = singleton "X'"
> -- |Weight 4, unstressed
> w4s0 = singleton "Y"
> -- |Weight 4, secondary stress
> w4s1 = singleton "Y`"
> -- |Weight 5, primary stress
> w4s2 = singleton "Y'"
> -- |Unstressed
> wxs0 = unionAll [w0s0, w1s0, w2s0, w3s0, w4s0]
> -- |Secondary stress
> wxs1 = unionAll [w0s1, w1s1, w2s1, w3s1, w4s1]
> -- |Primary stress
> wxs2 = unionAll [w0s2, w1s2, w2s2, w3s2, w4s2]

> w0, w1, w2, w3, w4, wx :: Set String
> -- |Light, any stress
> w0 = unionAll [w0s0, w0s1, w0s2]
> -- |Heavy, any stress
> w1 = unionAll [w1s0, w1s1, w1s2]
> -- |Superheavy, any stress
> w2 = unionAll [w2s0, w2s1, w2s2]
> -- |Weight 3, any stress
> w3 = unionAll [w3s0, w3s1, w3s2]
> -- |Weight 4, any stress
> w4 = unionAll [w4s0, w4s1, w4s2]
> -- |Any weight or stress
> wx = unionAll [w0, w1, w2, w3, w4]

> w0plus :: Set String
> -- |Light, some stress
> w0plus = unionAll [w0s1, w0s2]

> wplus, wpluss0, wpluss1 :: Set String
> -- |Non-light, any stress
> wplus = wx `difference` w0
> -- |Non-light, unstressed
> wpluss0 = wxs0 `difference` w0
> -- |Non-light, secondary stress
> wpluss1 = wxs1 `difference` w0
