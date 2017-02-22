> module Exploratorium where

> import LogicClasses
> import FSA
> import ReadJeff
> import Data.Set (Set)
> import qualified Data.Set as Set

> extendAlphabetTo :: (Ord a, Ord b) => Set (Symbol b) -> FSA a b ->
>                   FSA (Maybe Integer, Maybe a) b
> extendAlphabetTo syms = autUnion (emptyWithAlphabet syms)

> contractAlphabetTo :: (Ord a, Ord b) => Set (Symbol b) -> FSA a b ->
>                       FSA a b
> contractAlphabetTo syms fsa = trimUnreachables $
>                               FSA syms trans
>                               (initials fsa)
>                               (finals fsa)
>                               (isDeterministic fsa)
>     where trans = keep
>                   (isIn (insert Epsilon syms) . edgeLabel) $
>                   transitions fsa

> forceAlphabetTo :: (Ord a, Ord b) => Set (Symbol b) -> FSA a b ->
>                    FSA (Maybe Integer, Maybe a) b
> forceAlphabetTo syms = contractAlphabetTo syms . extendAlphabetTo syms

My wording here may not be the best, but for right now, I'm going to
say that a language "satisfies" a constraint if every word in the
language satisfies the constraint, and a language "has" a constraint
if there exists some word in the language that satisfies the
constraint.  So "satisfies" is universal, and "has" is existential.

> satisfies :: (Ord a1, Ord a2, Ord b) =>
>              FSA a1 b -> FSA a2 b -> Bool
> satisfies constraint fsa = isNull $ autIntersection fsa constraint'
>     where constraint' = complement $
>                         contractAlphabetTo (alphabet fsa) constraint

> has :: (Ord a1, Ord a2, Ord b) =>
>        FSA a1 b -> FSA a2 b -> Bool
> has constraint fsa =  not . isNull $ autIntersection fsa constraint'
>     where constraint' = contractAlphabetTo (alphabet fsa) constraint

> obligatoriness :: FSA Integer String
> obligatoriness = FSA (Set.fromList [Symbol "w0.s0",Symbol "w0.s1",Symbol "w0.s2",Symbol "w1.s0",Symbol "w1.s1",Symbol "w1.s2",Symbol "w2.s0",Symbol "w2.s1",Symbol "w2.s2",Symbol "w3.s0",Symbol "w3.s1",Symbol "w3.s2",Symbol "w4.s0",Symbol "w4.s1",Symbol "w4.s2"]) (Set.fromList [Transition (Symbol "w0.s0") (State 0) (State 0),Transition (Symbol "w0.s0") (State 1) (State 1),Transition (Symbol "w0.s1") (State 0) (State 0),Transition (Symbol "w0.s1") (State 1) (State 1),Transition (Symbol "w0.s2") (State 0) (State 1),Transition (Symbol "w0.s2") (State 1) (State 1),Transition (Symbol "w1.s0") (State 0) (State 0),Transition (Symbol "w1.s0") (State 1) (State 1),Transition (Symbol "w1.s1") (State 0) (State 0),Transition (Symbol "w1.s1") (State 1) (State 1),Transition (Symbol "w1.s2") (State 0) (State 1),Transition (Symbol "w1.s2") (State 1) (State 1),Transition (Symbol "w2.s0") (State 0) (State 0),Transition (Symbol "w2.s0") (State 1) (State 1),Transition (Symbol "w2.s1") (State 0) (State 0),Transition (Symbol "w2.s1") (State 1) (State 1),Transition (Symbol "w2.s2") (State 0) (State 1),Transition (Symbol "w2.s2") (State 1) (State 1),Transition (Symbol "w3.s0") (State 0) (State 0),Transition (Symbol "w3.s0") (State 1) (State 1),Transition (Symbol "w3.s1") (State 0) (State 0),Transition (Symbol "w3.s1") (State 1) (State 1),Transition (Symbol "w3.s2") (State 0) (State 1),Transition (Symbol "w3.s2") (State 1) (State 1),Transition (Symbol "w4.s0") (State 0) (State 0),Transition (Symbol "w4.s0") (State 1) (State 1),Transition (Symbol "w4.s1") (State 0) (State 0),Transition (Symbol "w4.s1") (State 1) (State 1),Transition (Symbol "w4.s2") (State 0) (State 1),Transition (Symbol "w4.s2") (State 1) (State 1)]) (Set.fromList [State 0]) (Set.fromList [State 1]) True

> culminativity :: FSA Integer String
> culminativity = FSA (Set.fromList [Symbol "w0.s0",Symbol "w0.s1",Symbol "w0.s2",Symbol "w1.s0",Symbol "w1.s1",Symbol "w1.s2",Symbol "w2.s0",Symbol "w2.s1",Symbol "w2.s2",Symbol "w3.s0",Symbol "w3.s1",Symbol "w3.s2",Symbol "w4.s0",Symbol "w4.s1",Symbol "w4.s2"]) (Set.fromList [Transition (Symbol "w0.s0") (State 0) (State 0),Transition (Symbol "w0.s0") (State 1) (State 1),Transition (Symbol "w0.s0") (State 2) (State 2),Transition (Symbol "w0.s1") (State 0) (State 0),Transition (Symbol "w0.s1") (State 1) (State 1),Transition (Symbol "w0.s1") (State 2) (State 2),Transition (Symbol "w0.s2") (State 0) (State 1),Transition (Symbol "w0.s2") (State 1) (State 2),Transition (Symbol "w0.s2") (State 2) (State 2),Transition (Symbol "w1.s0") (State 0) (State 0),Transition (Symbol "w1.s0") (State 1) (State 1),Transition (Symbol "w1.s0") (State 2) (State 2),Transition (Symbol "w1.s1") (State 0) (State 0),Transition (Symbol "w1.s1") (State 1) (State 1),Transition (Symbol "w1.s1") (State 2) (State 2),Transition (Symbol "w1.s2") (State 0) (State 1),Transition (Symbol "w1.s2") (State 1) (State 2),Transition (Symbol "w1.s2") (State 2) (State 2),Transition (Symbol "w2.s0") (State 0) (State 0),Transition (Symbol "w2.s0") (State 1) (State 1),Transition (Symbol "w2.s0") (State 2) (State 2),Transition (Symbol "w2.s1") (State 0) (State 0),Transition (Symbol "w2.s1") (State 1) (State 1),Transition (Symbol "w2.s1") (State 2) (State 2),Transition (Symbol "w2.s2") (State 0) (State 1),Transition (Symbol "w2.s2") (State 1) (State 2),Transition (Symbol "w2.s2") (State 2) (State 2),Transition (Symbol "w3.s0") (State 0) (State 0),Transition (Symbol "w3.s0") (State 1) (State 1),Transition (Symbol "w3.s0") (State 2) (State 2),Transition (Symbol "w3.s1") (State 0) (State 0),Transition (Symbol "w3.s1") (State 1) (State 1),Transition (Symbol "w3.s1") (State 2) (State 2),Transition (Symbol "w3.s2") (State 0) (State 1),Transition (Symbol "w3.s2") (State 1) (State 2),Transition (Symbol "w3.s2") (State 2) (State 2),Transition (Symbol "w4.s0") (State 0) (State 0),Transition (Symbol "w4.s0") (State 1) (State 1),Transition (Symbol "w4.s0") (State 2) (State 2),Transition (Symbol "w4.s1") (State 0) (State 0),Transition (Symbol "w4.s1") (State 1) (State 1),Transition (Symbol "w4.s1") (State 2) (State 2),Transition (Symbol "w4.s2") (State 0) (State 1),Transition (Symbol "w4.s2") (State 1) (State 2),Transition (Symbol "w4.s2") (State 2) (State 2)]) (Set.fromList [State 0]) (Set.fromList [State 0,State 1]) True

> filesToRead :: IO [FilePath]
> filesToRead = fmap lines $ readFile "to_read"

> readAndTag :: FilePath -> IO (FilePath, FSA Int String)
> readAndTag file = fmap ((,) file . readAndRelabelJeff) $ readFile file

> readAll :: IO [(FilePath, FSA Int String)]
> readAll = sequence . map readAndTag =<< filesToRead

> lacking :: (Eq x, Ord a1, Ord a2, Ord b) =>
>            FSA a1 b -> [(x, FSA a2 b)] -> [x]
> lacking constraint = tmap fst . filter (not . satisfies constraint . snd)

> having :: (Eq x, Ord a1, Ord a2, Ord b) =>
>           FSA a1 b -> [(x, FSA a2 b)] -> [x]
> having constraint = tmap fst . filter (has constraint . snd)

> languages :: (t1 -> [(FilePath, FSA Int String)] -> [String]) -> t1 -> IO ()
> languages f c = mapM_ putStrLn =<< fmap (f c) readAll
