> module ConstraintCompiler where

> import Data.Set (Set)
> import Factors
> import FSA
> import LogicClasses

> header :: String -> String
> header x = unlines [
>             "module " ++ x ++ " where",
>             "import Data.Set (fromList)",
>             "import FSA",
>             ""]

> compile :: (NFData e, Ord e, Show e) =>
>            String -> Set (Symbol e) -> Conjunction e -> String
> compile name alpha constraint = name ++ "=" ++ show (compile' alpha constraint)
> compile' :: (NFData e, Ord e) =>
>             Set (Symbol e) -> Conjunction e -> FSA Integer e
> compile' alpha constraint = normalize' $ buildConjunction alpha constraint
>     where normalize' a = (renameStates . minimize . determinize) a `asTypeOf` a
> compileFromList :: (NFData e, Ord e, Show e) =>
>                    String -> Set (Symbol e) -> [[Literal e]] -> String
> compileFromList = fmap (fmap (. makeConstraint)) compile
> compileFromList' :: (NFData e, Ord e, Show e) =>
>                     Set (Symbol e) -> [[Literal e]] -> FSA Integer e
> compileFromList' = fmap (. makeConstraint) compile'

> substring :: (Ord e) => [e] -> Bool -> Bool -> Factor e
> substring = Substring . tmap (singleton . Symbol)

> subsequence :: (Ord e) => [e] -> Factor e
> subsequence = Subsequence . tmap (singleton . Symbol)

> makeAlphabet :: (Ord e) => [e] -> Set (Symbol e)
> makeAlphabet = unionAll . tmap (singleton . Symbol)
