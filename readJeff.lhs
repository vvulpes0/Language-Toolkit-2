> {-# Language
>   UnicodeSyntax
>   #-}
> module Main (main) where

> import FSA
> import LogicClasses
> import Data.Set (Set)
> import qualified Data.Set as Set
> import System.IO

Reading Data From Jeff's Format
===============================

An FSA in Jeff's format consists of three parts separated by `!':

* Initial states: a line of comma-separated names
* Transitions: lines of state,state,symbol
* Final states: a line of comma-separated names

To start, we'll define a function to split a string on a delimiter

> splitOn ∷ Eq a ⇒ a → [a] → [[a]]
> splitOn _ [] = [[]]
> splitOn b (a:as)
>     | a == b = []:x
>     | otherwise = (a:head x):tail x
>     where x = splitOn b as

Then use that to parse a string in Jeff format and generate an FSA

> readJeffStateList ∷ (Monad m) ⇒ [String] → m (Set State)
> readJeffStateList [] = return (∅)
> readJeffStateList (x:xs)
>     | not (null xs) = parseFail "state list" (x:xs) "Invalid separator"
>     | otherwise = return . Set.fromList . tmap State $ splitOn ',' x

> readJeffTransitionList ∷ (Monad m) ⇒ [String] → m (Set (Transition String))
> readJeffTransitionList [] = return (∅)
> readJeffTransitionList (a:as) = do
>                                 x  ← readJeffTransition a
>                                 xs ← readJeffTransitionList as
>                                 return (Set.insert x xs)

> readJeffTransition ∷ (Monad m) ⇒ String → m (Transition String)
> readJeffTransition s 
>     | length xs < 3 = parseFail "Transition" s "Not enough components"
>     | length xs > 3 = parseFail "Transition" s "Too many components"
>     | otherwise = return (Transition (Symbol (xs!!2))
>                           (State (xs!!0)) (State (xs!!1)))
>     where xs = splitOn ',' s

> readJeff ∷ (Monad m) ⇒ String → m (FSA String)
> readJeff s 
>     | length initialParse /= 3 = parseFail "FSA" s "Not a Jeff"
>     | otherwise = do
>                   initialStates ← readJeffStateList (initialParse!!0)
>                   finalStates   ← readJeffStateList (initialParse!!2)
>                   transitions   ← readJeffTransitionList (initialParse!!1)
>                   let alphabet  = tmap path transitions in
>                       return (FSA alphabet transitions
>                                   initialStates finalStates False)
>     where initialParse = (tmap (keep (not . null) . splitOn '\n')
>                          . splitOn '!') s

Sometimes users give us input that is not what we expect.  Tell them
that, and what we think may have gone wrong:

> parseFail ∷ (Show a, Monad m) ⇒ String → a → String → m b
> parseFail target input reason = fail message
>     where message = ("Failed to parse " ++ target ++ ": " ++
>                      show input ++ ".  " ++ reason ++ ".")

> main = getContents >>= readJeff >>= return . show . renameStates >>= print
