
> module ConstraintCompiler where
> 
> import Factors
> import FSA
> 
> import Control.DeepSeq (NFData)
> import Data.Set (Set)
> 
> header :: String -> String
> header x = unlines [
>             "module " ++ x ++ " where",
>             "import Data.Set (fromList)",
>             "import FSA",
>             ""]
> 
> compile :: (NFData e, Ord e, Show e) =>
>            String -> Set e -> Conjunction e -> String
> compile name alpha constraint = name ++ "=" ++ show (compile' alpha constraint)
> compile' :: (NFData e, Ord e) =>
>             Set e -> Conjunction e -> FSA Integer e
> compile' alpha constraint = normalize' $ build alpha (singleton constraint)
>     where normalize' a = (renameStates . minimize . determinize) a `asTypeOf` a
> compileFromList :: (NFData e, Ord e, Show e) =>
>                    String -> Set e -> [[Literal e]] -> String
> compileFromList = fmap (fmap (. makeConstraint)) compile
> compileFromList' :: (NFData e, Ord e, Show e) =>
>                     Set e -> [[Literal e]] -> FSA Integer e
> compileFromList' = fmap (. makeConstraint) compile'
> 
> substring :: (Ord e) => [e] -> Bool -> Bool -> Factor e
> substring = Substring . tmap singleton
> 
> subsequence :: (Ord e) => [e] -> Factor e
> subsequence = Subsequence . tmap singleton
> 
> makeAlphabet :: (Ord e) => [e] -> Set e
> makeAlphabet = unionAll . tmap singleton

