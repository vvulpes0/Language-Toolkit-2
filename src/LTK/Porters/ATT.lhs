> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module : LTK.Porters.ATT
> Copyright : (c) 2019 Dakotah Lambert
> LICENSE : MIT
> 
> This module provides methods to convert automata to and from the
> AT&T FSM format.  Generally there will be up to three text files,
> the contents of which can be merged via 'embedSymbolsATT'.  When
> exporting, you should similarly use 'extractSymbolsATT' to unmerge
> the resulting files.
> -}
> module LTK.Porters.ATT ( embedSymbolsATT
>                        , extractSymbolsATT
>                        , invertATT
>                        -- *Importing
>                        , readATT
>                        -- *Exporting
>                        , exportATT
>                        ) where

> import LTK.FSA

> import Data.List (intercalate)
> import Data.Set (Set)
> import qualified Data.Set as Set

> separator :: String
> separator = "* * *"

> defaultEpsilon :: String
> defaultEpsilon = "<EPS>"

> -- |Take three strings and merge them in such a way that @(from ATT)@
> -- can understand the result.
> -- The three strings should represent the transitions,
> -- input symbols, and output symbols, respectively.
> embedSymbolsATT :: String -> Maybe String -> Maybe String -> String
> embedSymbolsATT x mi mo = unlines .
>                           (++) (lines x) . maybe [] id . m mi $ m mo Nothing
>     where presep   = (:) separator
>           multisep = maybe
>                      (fmap presep)
>                      (\a ->
>                       maybe (Just (presep a)) (Just . (++) (presep a)))
>           m = multisep . fmap lines

> -- |Convert the output of @(to ATT)@ into strings suitable for inclusion.
> -- The result represents the transitions, input symbols, and output symbols
> -- in that order.
> extractSymbolsATT :: String -> (String, String, String)
> extractSymbolsATT = (\(a:b:c:_) -> (a, b, c)) . flip (++) [[],[],[]] .
>                     map unlines . splitOn separator . lines

> -- |Convert an AT&T format string into one where input and output symbols
> -- have been reversed.
> invertATT :: String -> String
> invertATT s = embedSymbolsATT ts' (Just o) (Just i)
>     where (ts, i, o)      =  extractSymbolsATT s
>           ts'             =  unlines . map invertSingle $ lines ts
>           invertSingle t  =  intercalate "\t" . maybeInvert $ words t
>           maybeInvert (a:b:c:d:xs)
>               =  a:b:d:c:xs -- swap in and out
>           maybeInvert xs  =  xs


Reading an AT&T format automaton
================================

> -- |Import an FSA from its representation in AT&T format.
> -- Note that this import is not perfect;
> -- it discards weights and returns only the input projection.
> readATT :: String -> FSA Integer String
> readATT x = renameStates $
>             FSA { alphabet         =  union al as
>                 , transitions      =  ts
>                 , initials         =  singleton qi
>                 , finals           =  fs
>                 , isDeterministic  =  False
>                 }
>     where (es, i, _)     =  extractSymbolsATT x
>           (al, eps)      =  makeAlphabet (lines i)
>           (ts,as,qi,fs)  =  makeTransitions (lines es) eps

> makeAlphabet :: [String] -> (Set (String), Maybe String)
> makeAlphabet ss = findEps (Set.empty, Nothing) ps
>     where ps = foldr maybeInsert [] (map words ss)
>           maybeInsert (a:b:_) = (:) (a, b)
>           maybeInsert _       = id
>           findEps (l, x) []   = (l, x)
>           findEps (l, x) ((s, t):as)
>               = flip findEps as $
>                 if t == "0" then (l, Just s) else (Set.insert s l, x)

> makeTransitions :: [String] -> Maybe String ->
>                    ( Set (Transition String String)  -- transitions
>                    , Set String                      -- alphabet
>                    , State String                    -- initial state
>                    , Set (State String))             -- final states
> makeTransitions ss meps = foldr update
>                           (Set.empty, Set.empty, State "", Set.empty)
>                           (map words ss)
>     where eps = maybe "" id meps
>           update (a:[])    (ts, as, qi, fs)
>               = (ts, as, qi, Set.insert (State a) fs)
>           update (s:d:l:_) (ts, as, _, fs)
>               = ( Set.insert (Transition { source      = State s
>                                          , destination = State d
>                                          , edgeLabel   = if l == eps
>                                                          then Epsilon
>                                                          else Symbol l
>                                          }
>                              ) ts
>                 , if l == eps then as else Set.insert l as
>                 , State s -- the first line updates this last in foldr
>                 , fs
>                 )
>           update _ partial = partial


Creating an AT&T format automaton
=================================

> -- |Convert an 'FSA' into its AT&T format, with one caveat:
> -- The LTK internal format allows for symbols that the AT&T format
> -- does not understand, and no attempt is made to work around this.
> exportATT :: (Ord n, Ord e, Show e) => FSA n e -> String
> exportATT f = unlines $
>               dumpInitials (initials f')  ++
>               dumpTransitions ts          ++
>               dumpFinals (finals f')      ++
>               syms ++ syms
>     where syms = separator : dumpAlphabet (alphabet f')
>           f'   = if (Set.size (initials f) == 1)
>                  then renameStatesBy (subtract (1::Integer)) $ renameStates f
>                  else renameStates f
>           ts   = Set.map (\t -> (source t, destination t, edgeLabel t)) $
>                  transitions f'

> dumpAlphabet :: (Ord e, Show e) => Set e -> [String]
> dumpAlphabet as = p defaultEpsilon 0 :
>                   (map (uncurry p) . flip zip [1..] $ Set.toAscList as)
>     where p a t = showish a ++ "\t" ++ show (t + (0 :: Integer))

> dumpInitials :: (Ord n, Show n, Num n) => Set (State n) -> [String]
> dumpInitials qis
>     | Set.size qis < 2 = []
>     | otherwise        = map (\q -> dumpTr (State 0, q, eps)) $
>                          Set.toAscList qis
>     where eps = Epsilon :: Symbol String

> dumpTransitions :: (Ord n, Ord e, Show n, Show e) =>
>                    Set (State n, State n, Symbol e) -> [String]
> dumpTransitions ts = map dumpTr $ Set.toAscList ts

> dumpTr :: (Ord n, Ord e, Show n, Show e) =>
>           (State n, State n, Symbol e) -> String
> dumpTr (s, d, l) = intercalate "\t" $
>                    [show $ nodeLabel s, show $ nodeLabel d, l', l']
>     where l' = case l of
>                  Symbol e -> showish e
>                  _        -> defaultEpsilon

> dumpFinals :: (Ord n, Show n) => Set (State n) -> [String]
> dumpFinals = map (show . nodeLabel) . Set.toAscList


Helpers
=======

> splitOn :: Eq a => a -> [a] -> [[a]]
> splitOn _ [] = [[]]
> splitOn b (a:as)
>     | a == b = []:x
>     | otherwise = (a:head x):tail x
>     where x = splitOn b as

> showish :: Show a => a -> String
> showish = f . show
>     where f  xs     = if take 1 xs == "\"" then f' (drop 1 xs) else xs
>           f' ""     = ""
>           f' "\""   = ""
>           f' (x:xs) = x : f' xs
