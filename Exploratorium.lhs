> module Exploratorium where

> import FSA
> import ExtractSP
> import Porters
> import Data.List (sortBy)
> import Data.Set (Set)
> import qualified Data.Set as Set
> import Control.Parallel.Strategies

My wording here may not be the best, but for right now, I'm going to
say that a language "satisfies" a constraint if every word in the
language satisfies the constraint, and a language "has" a constraint
if there exists some word in the language that satisfies the
constraint.  So "satisfies" is universal, and "has" is existential.

> makeInt :: (Ord n, Ord e) => FSA n e -> FSA Integer e
> makeInt = renameStates

> satisfies :: (Ord n1, Ord n2, Ord e) =>
>              FSA n1 e -> FSA n2 e -> Bool
> satisfies constraint fsa = isNull $ intersection
>                            (makeInt fsa) (makeInt constraint')
>     where constraint' = complement $
>                         contractAlphabetTo (alphabet fsa) constraint

> has :: (Ord n1, Ord n2, Ord e) =>
>        FSA n1 e -> FSA n2 e -> Bool
> has constraint fsa =  not . isNull $ intersection
>                       (makeInt fsa) (makeInt constraint')
>     where constraint' = contractAlphabetTo (alphabet fsa) constraint

> obligatoriness :: FSA Integer String
> obligatoriness = FSA (Set.fromList ["w0.s0","w0.s1","w0.s2","w1.s0","w1.s1","w1.s2","w2.s0","w2.s1","w2.s2","w3.s0","w3.s1","w3.s2","w4.s0","w4.s1","w4.s2"]) (Set.fromList [Transition (Symbol "w0.s0") (State 0) (State 0),Transition (Symbol "w0.s0") (State 1) (State 1),Transition (Symbol "w0.s1") (State 0) (State 0),Transition (Symbol "w0.s1") (State 1) (State 1),Transition (Symbol "w0.s2") (State 0) (State 1),Transition (Symbol "w0.s2") (State 1) (State 1),Transition (Symbol "w1.s0") (State 0) (State 0),Transition (Symbol "w1.s0") (State 1) (State 1),Transition (Symbol "w1.s1") (State 0) (State 0),Transition (Symbol "w1.s1") (State 1) (State 1),Transition (Symbol "w1.s2") (State 0) (State 1),Transition (Symbol "w1.s2") (State 1) (State 1),Transition (Symbol "w2.s0") (State 0) (State 0),Transition (Symbol "w2.s0") (State 1) (State 1),Transition (Symbol "w2.s1") (State 0) (State 0),Transition (Symbol "w2.s1") (State 1) (State 1),Transition (Symbol "w2.s2") (State 0) (State 1),Transition (Symbol "w2.s2") (State 1) (State 1),Transition (Symbol "w3.s0") (State 0) (State 0),Transition (Symbol "w3.s0") (State 1) (State 1),Transition (Symbol "w3.s1") (State 0) (State 0),Transition (Symbol "w3.s1") (State 1) (State 1),Transition (Symbol "w3.s2") (State 0) (State 1),Transition (Symbol "w3.s2") (State 1) (State 1),Transition (Symbol "w4.s0") (State 0) (State 0),Transition (Symbol "w4.s0") (State 1) (State 1),Transition (Symbol "w4.s1") (State 0) (State 0),Transition (Symbol "w4.s1") (State 1) (State 1),Transition (Symbol "w4.s2") (State 0) (State 1),Transition (Symbol "w4.s2") (State 1) (State 1)]) (Set.fromList [State 0]) (Set.fromList [State 1]) True

> culminativity :: FSA Integer String
> culminativity = FSA (Set.fromList ["w0.s0","w0.s1","w0.s2","w1.s0","w1.s1","w1.s2","w2.s0","w2.s1","w2.s2","w3.s0","w3.s1","w3.s2","w4.s0","w4.s1","w4.s2"]) (Set.fromList [Transition (Symbol "w0.s0") (State 0) (State 0),Transition (Symbol "w0.s0") (State 1) (State 1),Transition (Symbol "w0.s0") (State 2) (State 2),Transition (Symbol "w0.s1") (State 0) (State 0),Transition (Symbol "w0.s1") (State 1) (State 1),Transition (Symbol "w0.s1") (State 2) (State 2),Transition (Symbol "w0.s2") (State 0) (State 1),Transition (Symbol "w0.s2") (State 1) (State 2),Transition (Symbol "w0.s2") (State 2) (State 2),Transition (Symbol "w1.s0") (State 0) (State 0),Transition (Symbol "w1.s0") (State 1) (State 1),Transition (Symbol "w1.s0") (State 2) (State 2),Transition (Symbol "w1.s1") (State 0) (State 0),Transition (Symbol "w1.s1") (State 1) (State 1),Transition (Symbol "w1.s1") (State 2) (State 2),Transition (Symbol "w1.s2") (State 0) (State 1),Transition (Symbol "w1.s2") (State 1) (State 2),Transition (Symbol "w1.s2") (State 2) (State 2),Transition (Symbol "w2.s0") (State 0) (State 0),Transition (Symbol "w2.s0") (State 1) (State 1),Transition (Symbol "w2.s0") (State 2) (State 2),Transition (Symbol "w2.s1") (State 0) (State 0),Transition (Symbol "w2.s1") (State 1) (State 1),Transition (Symbol "w2.s1") (State 2) (State 2),Transition (Symbol "w2.s2") (State 0) (State 1),Transition (Symbol "w2.s2") (State 1) (State 2),Transition (Symbol "w2.s2") (State 2) (State 2),Transition (Symbol "w3.s0") (State 0) (State 0),Transition (Symbol "w3.s0") (State 1) (State 1),Transition (Symbol "w3.s0") (State 2) (State 2),Transition (Symbol "w3.s1") (State 0) (State 0),Transition (Symbol "w3.s1") (State 1) (State 1),Transition (Symbol "w3.s1") (State 2) (State 2),Transition (Symbol "w3.s2") (State 0) (State 1),Transition (Symbol "w3.s2") (State 1) (State 2),Transition (Symbol "w3.s2") (State 2) (State 2),Transition (Symbol "w4.s0") (State 0) (State 0),Transition (Symbol "w4.s0") (State 1) (State 1),Transition (Symbol "w4.s0") (State 2) (State 2),Transition (Symbol "w4.s1") (State 0) (State 0),Transition (Symbol "w4.s1") (State 1) (State 1),Transition (Symbol "w4.s1") (State 2) (State 2),Transition (Symbol "w4.s2") (State 0) (State 1),Transition (Symbol "w4.s2") (State 1) (State 2),Transition (Symbol "w4.s2") (State 2) (State 2)]) (Set.fromList [State 0]) (Set.fromList [State 0,State 1]) True

> filesToRead :: IO [FilePath]
> filesToRead = fmap lines $ readFile "to_read"

> readAndTag :: FilePath -> IO (FilePath, FSA Integer String)
> readAndTag file = fmap ((,) file . from Jeff) $ readFile file

> readAll :: IO [(FilePath, FSA Integer String)]
> readAll = sequence . map readAndTag =<< filesToRead

> lacking :: (Eq x, Ord a1, Ord a2, Ord b) =>
>            FSA a1 b -> [(x, FSA a2 b)] -> [x]
> lacking constraint = tmap fst . filter (not . satisfies constraint . snd)

> having :: (Eq x, Ord a1, Ord a2, Ord b) =>
>           FSA a1 b -> [(x, FSA a2 b)] -> [x]
> having constraint = tmap fst . filter (has constraint . snd)

> languages :: (t1 -> [(FilePath, FSA Integer String)] -> [String]) -> t1 -> IO ()
> languages f c = mapM_ putStrLn =<< fmap (f c) readAll

> checkPT :: IO [FilePath]
> checkPT = fmap (tmap fst) . fmap (keep (isPT . snd)) $ readAll

> isPT :: (Ord n, Ord e) => FSA n e -> Bool
> isPT m = makeInt m' == (makeInt $ minimizeOver jEquivalence m')
>     where m' = syntacticMonoid m

< spConstraints :: IO ()
< spConstraints  =  mapM_ (\(a,b) ->
<                          putStrLn a >>
<                          mapM_ print (extractForbiddenSSQs b)) =<< readAll

> spConstraints :: IO ()
> spConstraints = do
>                 taggedFSAs <- readAll
>                 let fssqs = map (fmap extract) taggedFSAs
>                 let pfssqs = fssqs `using` parListChunk 10 rdeepseq
>                 mapM_ (\(a,(b,c)) ->
>                        putStrLn ("# " ++ showName a) >>
>                        putStrLn ("# alphabet: " ++
>                                  showSymList (Set.toAscList b)) >>
>                        mapM_ (putStrLn . showSymList) (sortBy comp $ Set.toList c) >>
>                        putStrLn "") pfssqs
>     where showSymList = concatMap showSym
>           showSym     = take 2 . (++ "  ") . filter (/= '"') . show .
>                         transliterateString
>           showName [] = []
>           showName ('_':xs) = ' ' : showName xs
>           showName ('.':'f':'s':'a':xs) = []
>           showName (x:xs) = x : showName xs
>           extract f = (alphabet f, extractForbiddenSSQs f)
>           comp xs ys
>                | length xs < length ys = LT
>                | length xs > length ys = GT
>                | otherwise             = compare xs ys
