> {-# OPTIONS_HADDOCK hide,show-extensions #-}
> {-# Language CPP #-}

#if !defined(MIN_VERSION_base)
# define MIN_VERSION_base(a,b,c) 0
#endif

> {-|
> Module : LTK.Porters.Jeff
> Copyright : (c) 2016-2019,2021,2023 Dakotah Lambert
> LICENSE : MIT
> 
> This module provides methods to convert automata to and from
> Jeff's format.
> -}
> module LTK.Porters.Jeff
>        ( -- *Importing
>          readJeff
>        , transliterate
>        , transliterateString
>        -- *Exporting
>        , exportJeff
>        , untransliterate
>        , untransliterateString
>        ) where

#if !MIN_VERSION_base(4,8,0)
> import Control.Applicative ((<*>))
> import Data.Functor ((<$>))
#endif
> import Data.List (intercalate)
> import Data.List.NonEmpty (NonEmpty(..))
> import Data.Set (Set)
> import qualified Data.Set as Set
> import qualified Data.List.NonEmpty as NE

> import LTK.FSA


Reading from Jeff's format
==========================

An FSA in Jeff's format consists of three parts separated by `!':

* Initial states: a line of comma-separated names
* Transitions: lines of state,state,symbol
* Final states: a line of comma-separated names

To start, we'll define a function to split a string on a delimiter

> splitOn :: Eq a => a -> [a] -> NonEmpty [a]
> splitOn _ [] = [] :| []
> splitOn b (a:as)
>     | a == b = [] :| NE.toList x
>     | otherwise = (a:NE.head x) :| NE.tail x
>     where x = splitOn b as

Then use that to parse a string in Jeff format and generate an FSA

> -- |Import an t'FSA' from its representation in Jeff's format.
> -- The resulting @Int@ node labels may have nothing to do with the
> -- node labels in the source.
> readJeff :: String -> Either String (FSA Int String)
> readJeff s = transliterate . renameStates
>              <$> readJeffWithoutRelabeling s

> readJeffStateList :: [String] -> Either String (Set (State String))
> readJeffStateList [] = Right empty
> readJeffStateList (x:xs)
>     | not (null xs)  =  parseFail "state list" (x:xs) "Invalid separator"
>     | otherwise      =  Right . Set.fromList . tmap State
>                         . NE.toList $ splitOn ',' x

> readJeffTransitionList :: [String] ->
>                           Either String (Set (Transition String String))
> readJeffTransitionList
>     = foldr (\a -> (<*>) (insert <$> readJeffTransition a))
>             (Right empty)

> readJeffTransition :: String -> Either String (Transition String String)
> readJeffTransition s
>     = case xs of
>         (x:y:z:[]) -> Right
>                       $ Transition (Symbol z) (State x) (State y)
>         (_:_:_:_:_) -> parseFail "Transition" s "Too many components"
>         _ -> parseFail "Transition" s "Not enough components"
>     where xs = NE.toList $ splitOn ',' s

> readJeffWithoutRelabeling :: String -> Either String (FSA String String)
> readJeffWithoutRelabeling s
>     = case initialParse of
>         (x:y:z:[]) -> let inits = readJeffStateList x
>                           trans = readJeffTransitionList y
>                           fins  = readJeffStateList z
>                           alpha = unsymbols . tmap edgeLabel <$> trans
>                       in FSA <$> alpha <*> trans <*> inits <*> fins
>                          <*> Right False
>         _ -> parseFail "FSA" s "Not a Jeff"
>     where initialParse
>               = map (keep (not . null) . NE.toList . splitOn '\n')
>                 . NE.toList $ splitOn '!' s

Sometimes users give us input that is not what we expect.  Tell them
that, and what we think may have gone wrong:

> parseFail :: Show a => String -> a -> String -> Either String b
> parseFail target input reason = Left message
>     where message = "Failed to parse " ++ target ++ ": "
>                     ++ show input ++ ".  " ++ reason ++ "."

Transliterating Jeff's FSAs into the form used by my compiler:

> makeStress :: String -> String
> makeStress str = case digits
>                  of "0" -> ""
>                     "1" -> "`"
>                     "2" -> "'"
>                     _   -> str
>     where digits = filter (isIn "0123456789") str

> makeWeight :: String -> String
> makeWeight str = case digits
>                  of "0" -> "L"
>                     "1" -> "H"
>                     "2" -> "S"
>                     "3" -> "X"
>                     "4" -> "Y"
>                     _   -> str
>     where digits = filter (isIn "0123456789") str

> mapEvenOdd :: (a -> b) -> (a -> b) -> [a] -> [b]
> mapEvenOdd f g (a1:a2:xs)  =  f a1 : g a2 : mapEvenOdd f g xs
> mapEvenOdd f _ [a1]        =  [f a1]
> mapEvenOdd _ _ []          =  []

> -- |See 'transliterate'.  This function operates directly on the
> -- representation of the edge label.
> transliterateString :: String -> String
> transliterateString = concat . mapEvenOdd makeWeight makeStress
>                       . NE.toList . splitOn '.'

> -- |Automata in Jeff's format use edge labels of the form
> -- &#x201c;w0.s1&#x201d;.
> -- This function converts the edge labels of an automaton from this
> -- form to the
> -- &#x201c;L\`&#x201d;
> -- form that we tend to use.
> transliterate :: (Ord n) => FSA n String -> FSA n String
> transliterate = renameSymbolsBy transliterateString


Writing to Jeff's format
========================

> -- |Convert an t'FSA' to its representation in Jeff's format.
> exportJeff :: (Ord e, Ord n, Show e) => FSA n e -> String
> exportJeff f = unlines (inits : trans ++ [fins])
>     where list   =  keep (/= ' ') . intercalate ", " . Set.toAscList .
>                     tmap (show . nodeLabel)
>           fins   =  list (finals f')
>           inits  =  list (initials f') ++ "!"
>           trans  =  bangTerminate . Set.toAscList .
>                     tmap exportJeffTransition $ transitions f'
>           f'     =  normalize f

> bangTerminate :: [String] -> [String]
> bangTerminate []      =  []
> bangTerminate [x]     =  [x ++ "!"]
> bangTerminate (x:xs)  =  x : bangTerminate xs

> exportJeffTransition :: (Show e, Show n) => Transition n e -> String
> exportJeffTransition t = nl (source t) ++ "," ++
>                          nl (destination t) ++ "," ++
>                          el (edgeLabel t)
>     where nl = nq . show . nodeLabel
>           el (Symbol a) = untransliterateString . nq $ show a
>           el Epsilon    = "\x03B5"
>           nq = keep (/= '"')

> -- |The inverse of 'transliterate'.
> untransliterate :: (Ord n) => FSA n String -> FSA n String
> untransliterate = renameSymbolsBy untransliterateString

> -- |The inverse of 'transliterateString'.
> untransliterateString :: String -> String
> untransliterateString ('L':xs)  =  "w0." ++ untransliterateStress xs
> untransliterateString ('H':xs)  =  "w1." ++ untransliterateStress xs
> untransliterateString ('S':xs)  =  "w2." ++ untransliterateStress xs
> untransliterateString ('X':xs)  =  "w3." ++ untransliterateStress xs
> untransliterateString ('Y':xs)  =  "w4." ++ untransliterateStress xs
> untransliterateString xs        =  xs

> untransliterateStress :: String -> String
> untransliterateStress []   =  "s0"
> untransliterateStress "`"  =  "s1"
> untransliterateStress "'"  =  "s2"
> untransliterateStress xs   =  xs
