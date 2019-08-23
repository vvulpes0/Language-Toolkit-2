> module Main where

> import LTK.ConstraintCompiler
> import LTK.Porters

> import LTK.Factors
> import LTK.FSA

> import Control.DeepSeq
> import Control.Parallel.Strategies
> import qualified Data.Set as Set (toAscList)
> import System.IO

> c89, c9x, c91, c145, c146 :: FSA Integer String
> c89 = compileFromList' wx [[required (Substring [wxs2] False False)]]
> c9x = compileFromList' wx [[forbidden (Substring [wpluss0] False False), forbidden (Substring [w1s2] False True)]]
> c91 = compileFromList' wx [[forbidden (Substring [wpluss1] False False), forbidden (Substring [w1s2] False True)]]
> c145 = desurfaceSecondary $ compileFromList' wx
>        [[forbidden (Substring [w0plus, w0plus] False False)],
>         [forbidden (Substring [w0s0,w0s0] False False)],
>         [forbidden (Substring [wplus, w0plus] False False)],
>         [forbidden (Substring [w0plus] True False)]]
> c146 = renameStates . minimize . determinize $ unionAll
>        [compileFromList' wx [[forbidden (Substring [w0s2] False False)]],
>         c145,
>         compileFromList' wx [[required (Substring [w0s2] True True)]]]

> desurfaceSecondary :: (Enum n1, Ord n, Ord n1) => FSA n String -> FSA n1 String
> desurfaceSecondary = renameStates . minimize . determinize . renameSymbolsBy f
>     where f = head . tr (Set.toAscList wxs1) (Set.toAscList wxs0) . singleton

> nonEmptySubsets :: (Ord n, NFData e, Ord e) =>
>                    [(String, FSA n e)] -> [(String, FSA Int e)]
> nonEmptySubsets [] = []
> nonEmptySubsets (x:[]) = [fmap renameStates x]
> nonEmptySubsets (x:xs) = f x : map (combine (f x)) xs' ++ xs'
>     where xs'                        =  nonEmptySubsets xs
>           f                          =  fmap renameStates
>           combine (s1, f1) (s2, f2)  =  (s1 `seq` s2 `seq` s1 ++ "_" ++ tail s2,
>                                          normalize' $!! intersection f1 f2)

> normalize' :: (Ord n, Ord e) => FSA n e -> FSA Int e
> normalize' = renameStates . minimize . determinize

> main :: IO ()
> main = do
>   --putStrLn (header "CompiledConstraints")
>   let constraints = map prepare $
>                     nonEmptySubsets
>                     [("c89",c89),
>                      ("c9x",c9x),
>                      ("c91",c91),
>                      ("c145",c145),
>                      ("c146",c146)]
>       pconstraints = constraints `using` parListChunk 1 rdeepseq
>   mapM_ (uncurry write) pconstraints
>       where prepare (a, b) = (a, to Jeff $ untransliterate b)

> write :: FilePath -> String -> IO ()
> write fp str = withFile fp WriteMode $ \h -> do
>                  hPutStr h str
>                  hFlush h