> module LTK.ConstraintCompiler (compile) where

> import Control.DeepSeq (NFData)
> import Data.Set (Set)

> import LTK.Factors (Conjunction, Literal, build, makeConstraint)
> import LTK.FSA (FSA, determinize, minimize, renameStates, singleton)

> compile :: (NFData e, Ord e, Show e) =>
>            Set e -> [[Literal e]] -> FSA Integer e
> compile = fmap (. makeConstraint) compile'
> compile' :: (NFData e, Ord e) =>
>             Set e -> Conjunction e -> FSA Integer e
> compile' alpha constraint = normalize' $ build alpha (singleton constraint)
>     where normalize' a = (renameStates . minimize . determinize) a
>                          `asTypeOf` a
