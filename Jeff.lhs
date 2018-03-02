> {-# OPTIONS_HADDOCK hide,show-extensions #-}
> {-|
> Module : Jeff
> Copyright : (c) 2016-2018 Dakotah Lambert
> LICENSE : BSD-style, see LICENSE
> 
> This module provides methods to convert automata to and from
> Jeff's format.
> -}
> module Jeff ( -- *Importing
>               readJeff
>             , transliterate
>             , transliterateString
>               -- *Exporting
>             , exportJeff
>             , untransliterate
>             , untransliterateString
>             ) where

> import FSA
> import Data.Functor ((<$>))
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

> -- |Import an 'FSA' from its representation in Jeff's format.
> -- The resulting @Int@ node labels may have nothing to do with the
> -- node labels in the source.
> readJeff :: String -> FSA Int String
> readJeff = renameStates . readJeffWithoutRelabeling

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

> readJeffWithoutRelabeling :: String -> FSA String String
> readJeffWithoutRelabeling s 
>     | length initialParse /= 3  = parseFail "FSA" s "Not a Jeff"
>     | otherwise                 = FSA alphabet trans inits fins False
>     where initialParse  = (tmap (keep (not . null) . splitOn '\n')
>                           . splitOn '!') s
>           alphabet      = unsymbols $ tmap edgeLabel trans
>           trans         = readJeffTransitionList $ initialParse!!1
>           inits         = readJeffStateList $ initialParse!!0
>           fins          = readJeffStateList $ initialParse!!2

Sometimes users give us input that is not what we expect.  Tell them
that, and what we think may have gone wrong:

> parseFail :: Show a => String -> a -> String -> b
> parseFail target input reason = error message
>     where message = ("Failed to parse " ++ target ++ ": " ++
>                      show input ++ ".  " ++ reason ++ ".")

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

> -- |See 'transliterate'.  This function operates directly on the
> -- representation of the edge label.
> transliterateString :: String -> String
> transliterateString = concat . mapEvenOdd makeWeight makeStress . splitOn '.'

> transliterateTransition :: (Ord n) => Transition n String -> Transition n String
> transliterateTransition (Transition x q1 q2) =
>     Transition (fmap transliterateString x) q1 q2

> -- |Automata in Jeff's format use edge labels of the form
> -- &#x201c;w0.s1&#x201d;.
> -- This function converts the edge labels of an automaton from this
> -- form to the
> -- &#x201c;L\`&#x201d;
> -- form that we tend to use.
> transliterate :: (Ord n) => FSA n String -> FSA n String
> transliterate (FSA a t i f d) = FSA (tmap transliterateString a)
>                                 (tmap transliterateTransition t)
>                                 i f d


Reading Data From Jeff's Format
===============================

> -- |Convert an 'FSA' to its representation in Jeff's format.
> exportJeff :: (Ord e, Ord n, Show e) => FSA n e -> String
> exportJeff f = unlines (inits : trans ++ [fins])
>     where list = keep (/= ' ') . commaSeparateList . tmap nodeLabel
>           fins = list (finals f')
>           inits = list (initials f') ++ "!"
>           trans = bangTerminate . Set.toAscList .
>                   tmap exportJeffTransition $ transitions f'
>           f' = normalize f

> bangTerminate :: [String] -> [String]
> bangTerminate [] = []
> bangTerminate (x:[]) = [x ++ "!"]
> bangTerminate (x:xs) = x : bangTerminate xs

> exportJeffTransition :: (Show e, Show n) => Transition n e -> String
> exportJeffTransition t = nl (source t) ++ "," ++
>                          nl (destination t) ++ "," ++
>                          el (edgeLabel t)
>     where nl = nq . show . nodeLabel
>           el (Symbol a) = nq $ show a
>           el Epsilon    = "\x03B5"
>           nq = keep (/= '"')

> -- |The inverse of 'transliterate'.
> untransliterate :: (Ord n) => FSA n String -> FSA n String
> untransliterate f = FSA (tmap untransliterateString (alphabet f))
>                     (tmap untransliterateTransition (transitions f))
>                     (initials f) (finals f) (isDeterministic f)

> untransliterateTransition :: Transition n String -> Transition n String
> untransliterateTransition t = Transition
>                               (untransliterateString <$> edgeLabel t)
>                               (source t)
>                               (destination t)

> -- |The inverse of 'transliterateString'.
> untransliterateString :: String -> String
> untransliterateString ('L':xs) = "w0." ++ untransliterateStress xs
> untransliterateString ('H':xs) = "w1." ++ untransliterateStress xs
> untransliterateString ('S':xs) = "w2." ++ untransliterateStress xs
> untransliterateString ('X':xs) = "w3." ++ untransliterateStress xs
> untransliterateString ('Y':xs) = "w4." ++ untransliterateStress xs
> untransliterateString xs       = xs

> untransliterateStress :: String -> String
> untransliterateStress [] = "s0"
> untransliterateStress "`" = "s1"
> untransliterateStress "'" = "s2"
> untransliterateStress xs  = xs

> commaSeparateList :: (Collapsible c, Show b) => c b -> String
> commaSeparateList xs
>     | size xs == 0  = ""
>     | size xs == 1  = show x
>     | otherwise     = show x ++ ", " ++ commaSeparateList xs'
>     where (x, xs') = choose xs
