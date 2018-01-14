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

> compile :: (Ord e, Show e) => String -> Set (Symbol e) -> Conjunction e -> String
> compile name alpha constraint = name ++ "=" ++ show (compile' alpha constraint)
> compile' :: (Ord x) => Set (Symbol x) -> Conjunction x -> FSA Integer x
> compile' alpha constraint = normalize' $ buildConjunction alpha constraint
>     where normalize' a = (renameStates . minimize . determinize) a `asTypeOf` a
> compileFromList :: (Ord e, Show e) => String -> Set (Symbol e) -> [[Literal e]] -> String
> compileFromList = fmap (fmap (. makeConstraint)) compile
> compileFromList' :: (Ord e, Show e) => Set (Symbol e) -> [[Literal e]] -> FSA Integer e
> compileFromList' = fmap (. makeConstraint) compile'

> substring :: (Ord e) => [e] -> Bool -> Bool -> Factor e
> substring = Substring . tmap (singleton . Symbol)

> subsequence :: (Ord e) => [e] -> Factor e
> subsequence = Subsequence . tmap (singleton . Symbol)

> makeAlphabet :: (Ord e) => [e] -> Set (Symbol e)
> makeAlphabet = unionAll . tmap (singleton . Symbol)
