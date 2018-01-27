> module ReadJeff where

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

> splitOn :: Eq a => a -> [a] -> [[a]]
> splitOn _ [] = [[]]
> splitOn b (a:as)
>     | a == b = []:x
>     | otherwise = (a:head x):tail x
>     where x = splitOn b as

Then use that to parse a string in Jeff format and generate an FSA

> readJeffStateList :: [String] -> Set (State String)
> readJeffStateList [] = empty
> readJeffStateList (x:xs)
>     | not (null xs)  = parseFail "state list" (x:xs) "Invalid separator"
>     | otherwise      = Set.fromList . tmap State $ splitOn ',' x

> readJeffTransitionList :: [String] -> Set (Transition String String)
> readJeffTransitionList []      = empty
> readJeffTransitionList (a:as)  = insert
>                                  (readJeffTransition a)
>                                  (readJeffTransitionList as)

> readJeffTransition :: String -> Transition String String
> readJeffTransition s 
>     | length xs < 3  = parseFail "Transition" s "Not enough components"
>     | length xs > 3  = parseFail "Transition" s "Too many components"
>     | otherwise      = Transition (Symbol (xs!!2))
>                        (State (xs!!0)) (State (xs!!1))
>     where xs = splitOn ',' s

> readJeff :: String -> FSA String String
> readJeff s 
>     | length initialParse /= 3  = parseFail "FSA" s "Not a Jeff"
>     | otherwise                 = FSA alphabet trans inits fins False
>     where initialParse  = (tmap (keep (not . null) . splitOn '\n')
>                           . splitOn '!') s
>           alphabet      = tmap edgeLabel trans
>           trans         = readJeffTransitionList $ initialParse!!1
>           inits         = readJeffStateList $ initialParse!!0
>           fins          = readJeffStateList $ initialParse!!2

Sometimes users give us input that is not what we expect.  Tell them
that, and what we think may have gone wrong:

> parseFail :: Show a => String -> a -> String -> b
> parseFail target input reason = error message
>     where message = ("Failed to parse " ++ target ++ ": " ++
>                      show input ++ ".  " ++ reason ++ ".")

> readAndRelabelJeff :: String -> FSA Int String
> readAndRelabelJeff = renameStates . readJeff

Transliterating Jeff's FSAs into the form used by my compiler:

> makeStress :: String -> String
> makeStress str  =  case digits of 
>                      "0" -> ""
>                      "1" -> "`"
>                      "2" -> "'"
>                      _   -> str
>     where digits = filter (isIn "0123456789") str

> makeWeight :: String -> String
> makeWeight str  =  case digits of
>                      "0" -> "L"
>                      "1" -> "H"
>                      "2" -> "S"
>                      "3" -> "X"
>                      "4" -> "Y"
>                      _   -> str
>     where digits = filter (isIn "0123456789") str

> mapEvenOdd :: (a -> b) -> (a -> b) -> [a] -> [b]
> mapEvenOdd f g (a1:a2:xs)  =  f a1 : g a2 : mapEvenOdd f g xs
> mapEvenOdd f _ (a1:[])     =  f a1 : []
> mapEvenOdd _ _ []          =  []

> transliterateString :: String -> String
> transliterateString = concat . mapEvenOdd makeWeight makeStress . splitOn '.'

> transliterateTransition :: (Ord n) => Transition n String -> Transition n String
> transliterateTransition (Transition x q1 q2) =
>     Transition (fmap transliterateString x) q1 q2

> transliterate :: (Ord n) => FSA n String -> FSA n String
> transliterate (FSA a t i f d) = FSA (tmap (fmap transliterateString) a)
>                                 (tmap transliterateTransition t)
>                                 i f d

< main = interact ((++ "\n") . show . readAndRelabelJeff)
