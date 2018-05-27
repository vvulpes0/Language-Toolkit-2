> module Main where

> import ExtractSL
> import ExtractSP
> import Factors
> import FSA
> import Porters

> import Control.Concurrent ( MVar
>                           , ThreadId
>                           , forkFinally
>                           , newEmptyMVar
>                           , newMVar
>                           , putMVar
>                           , takeMVar
>                           )
> import Control.DeepSeq (NFData, ($!!))
> import Data.Functor ((<$>))
> import Data.List (sortBy)
> import Data.Ord (comparing)
> import Data.Set (Set)
> import qualified Data.Set as Set
> import System.Directory (createDirectoryIfMissing, doesFileExist)
> import System.Environment (getArgs)
> import System.Exit (die)
> import System.FilePath ((</>), (<.>), takeBaseName)
> import System.IO ( IOMode (..)
>                  , hGetContents
>                  , hPutStrLn
>                  , stderr
>                  , withFile
>                  )

> import Debug.Trace (trace)
> import System.IO (hFlush, stdout)

> continue :: IO ()
> continue = pure () -- do nothing; carry on

vvvvv From Haskell documentation on Control.Concurrent vvvvv
https://hackage.haskell.org/package/base-4.10.1.0/docs/Control-Concurrent.html

> waitForChildren :: MVar [MVar ()] -> IO ()
> waitForChildren children = do
>   cs <- takeMVar children
>   case cs of
>     []    ->  return ()
>     m:ms  ->  do
>             putMVar children ms
>             takeMVar m
>             waitForChildren children

> forkChild :: MVar [MVar ()] -> IO () -> IO ThreadId
> forkChild children io = do
>   mvar <- newEmptyMVar
>   childs <- takeMVar children
>   putMVar children (mvar : childs)
>   forkFinally io (\_ -> putMVar mvar ())

^^^^^ From Haskell documentation on Control.Concurrent ^^^^^

> hypothesesFile :: FilePath
> hypothesesFile = "Compiled" </> "constraints"

> outputDirectory :: FilePath
> outputDirectory = "Results"

> main :: IO ()
> main = do
>   children <- newMVar []
>   filesToRead <- getArgs
>   haveHypotheses <- doesFileExist hypothesesFile
>   if not haveHypotheses
>   then die "Cannot factor without hypotheses.  Exiting."
>   else continue
>   existence <- sequence (map doesFileExist filesToRead)
>   let nonexistentFiles = tmap fst . keep (not . snd) $
>                          zip filesToRead existence
>   if not (isEmpty nonexistentFiles)
>   then do
>     mapM_ (hPutStrLn stderr . (++ ".") . ("Cannot find " ++)) nonexistentFiles
>     die "Exiting."
>   else continue
>   createDirectoryIfMissing True outputDirectory
>   -- Files to be factored, hypotheses, and output directory all exist
>   withFile hypothesesFile ReadMode $ \h -> do
>          hypotheses <- mapM get =<< lines <$> hGetContents h
>          mapM_ (forkChild children . processFile hypotheses) filesToRead
>          waitForChildren children
>       where get fp = (withFile fp ReadMode $ \h -> do
>                         fsa <- from Jeff <$> hGetContents h
>                         return $!! (fp, fsa)
>                      )

> processFile :: [(FilePath, FSA Integer String)] -> FilePath -> IO ()
> processFile hypotheses fp =
>     withFile fp ReadMode $ \h -> do
>       fsa <- normalize <$> from Jeff <$> hGetContents h
>       withFile (outputDirectory </> lect) WriteMode $ \out ->
>           hPutStrLn out (output name fsa (factorization hypotheses fsa))
>     where bn = takeBaseName fp
>           lect = takeWhile (isIn "0123456789") bn
>           name = tr "_" " " $ dropWhile (isIn "0123456789_") bn
>           getFSA (a,_,_) = a
>           getFFs (_,b,_) = unlines $ formatForbiddenSubstrings b
>           getFQs (_,_,c) = unlines $ formatForbiddenSubsequences c


Return type of factorization is (Strict Approximation, Costrict Approximation, X)
where X is either () if the factorization is incomplete,
                  Nothing if factorization is complete below testable level, or
                  A FilePath of the necessary compiled higher constraints

> factorization :: (Ord n, Ord e, NFData e) =>
>                  [(FilePath, FSA Integer e)]
>               -> FSA n e
>               -> ( ( FSA Integer e
>                    , ForbiddenSubstrings e
>                    , ForbiddenSubsequences e
>                    )
>                  , ( FSA Integer e
>                    , ForbiddenSubstrings e
>                    , ForbiddenSubsequences e
>                    )
>                  , Either () (Maybe FilePath)
>                  )
> factorization hypotheses fsa' = ( strict
>                                 , costrict
>                                 , if scs == fsa
>                                   then Right Nothing
>                                   else if isEmpty workingHypotheses
>                                        then Left ()
>                                        else Right . Just . fst $
>                                             chooseOne workingHypotheses
>                                 ) 
>     where fsa                =  renameStates fsa' `asTypeOf` normalize fsa'
>           strict             =  strictApproximation fsa
>           costrict           =  costrictApproximation fsa strict
>           getFSA (a, _, _)   =  a
>           scs                =  intersection (getFSA strict) (getFSA costrict)
>           workingHypotheses  =  keep
>                                 ((== fsa) . intersection scs .
>                                  contractAlphabetTo (alphabet fsa) . snd)
>                                 hypotheses


Constructing approximations
===========================

The strict approximation of an FSA is simply the intersection of its
SL and SP approximations.  The complexity comes from the fact that
factorizations can favor either local or piecewise factors.

In this work, we favor local factors.  In order to construct a minimal
set, we first find all strictly local and strictly piecewise factors
of the source automaton, then filter away any piecewise factors
implied by the local ones, then finally filter away any local factors
implied by the remaining piecewise ones.

> strictApproximation :: (Ord e, NFData e) =>
>                        FSA Integer e 
>                     -> ( FSA Integer e
>                        , ForbiddenSubstrings e
>                        , ForbiddenSubsequences e
>                        )
> strictApproximation fsa
>     | isSL fsa   =  (renameStates fsa, fs, empty)
>     | otherwise  =  (normalize (intersection sl sp), fs2, fq2)
>     where fs = forbiddenSubstrings fsa
>           sl = buildFSA fs
>           fq = forbiddenSubsequences fsa
>           sp = renameStates (subsequenceClosure fsa)
>           fq2 = difference fq (forbiddenSubsequences sl)
>           fs2 = if isEmpty fq2
>                 then fs
>                 else difference fs . forbiddenSubstrings . normalize $
>                      fsaFromForbiddenSubsequences fq2

If we wanted to instead favor piecewise factors, we could swap the
order of computation of fq2 and fs2 above.

The costrict approximation is formed from the residue of the strict
approximation and the original FSA.  Its computation is a bit more
involved, because we must remove potentially-required factors that are
not, in fact, required.  It seems to me that the best way to do that
is to find the smallest subset of factors such that all of them are
actually required.

> costrictApproximation :: (Ord e, NFData e) =>
>                          FSA Integer e
>                       -> ( FSA Integer e
>                          , ForbiddenSubstrings e
>                          , ForbiddenSubsequences e
>                          )
>                       -> ( FSA Integer e
>                          , ForbiddenSubstrings e
>                          , ForbiddenSubsequences e
>                          )
> costrictApproximation fsa (strict, fs, fq)
>     | strict == fsa  =  (totalWithAlphabet (alphabet fsa), empty, empty)
>     | otherwise      =  reformApproximation (alphabet fsa)  .
>                         trueRequireds fsa                   .
>                         literalsFromApproximation           .
>                         removeForbidden                     .
>                         strictApproximation                 .
>                         normalize $ residue strict fsa
>     where removeForbidden (a, b, c) = (a, difference b fs, difference c fq)

> literalsFromApproximation :: Ord e =>
>                              ( a
>                              , ForbiddenSubstrings e
>                              , ForbiddenSubsequences e)
>                           -> Set (Literal e)
> literalsFromApproximation (_, fs, fq) = unionAll [lfr, lin, lfi, lwo, lq]
>     where lq       =  tmap
>                       (forbidden . Subsequence . tmap singleton) $
>                       getSubsequences fq
>           f :: Ord x => Bool -> Bool -> Set [x] -> Set (Literal x)
>           f h t x  =  tmap
>                       (\a -> forbidden (Substring (tmap singleton a) h t))
>                       x
>           lfr      =  f False False (forbiddenFrees fs)
>           lin      =  f True False (forbiddenInitials fs)
>           lfi      =  f False True (forbiddenFinals fs)
>           lwo      =  f True True (forbiddenWords fs)

> subsets :: (Eq (c a), Collapsible c, Container (c a) a) => c a -> [c a]
> subsets xs
>     | isEmpty xs  =  singleton empty
>     | otherwise   =  union (tmap (insert x) xs') xs'
>     where (x, as)  =  choose xs
>           xs'      =  subsets as

> trueRequireds :: (Ord e, NFData e) =>
>                  FSA Integer e
>               -> Set (Literal e)
>               -> Set (Literal e)
> trueRequireds fsa literals = fromCollapsible . head   .
>                              (++ [empty])             .
>                              Prelude.reverse          .
>                              findGoodSubsets          .
>                              tmap f                   .
>                              Prelude.reverse          .
>                              sortBy (comparing size)  .
>                              subsets $ literals
>     where f ls  =  ( ls
>                    , isEmpty               .
>                      intersection fsa      .
>                      build (alphabet fsa)  .
>                      singleton             .
>                      makeConstraint        .
>                      fromCollapsible       $
>                      tmap singleton ls
>                    )

> findGoodSubsets :: (Ord e, NFData e) =>
>                    [(Set (Literal e), Bool)]
>                 -> [Set (Literal e)]
> findGoodSubsets [] = empty
> findGoodSubsets ((ls, isGood) : xs)
>     | isGood = ls : findGoodSubsets xs
>     | otherwise = findGoodSubsets (keep (not . isSubsetOf ls . fst) xs)

> reformApproximation :: (Ord e, NFData e) =>
>                        Set e
>                     -> Set (Literal e)
>                     -> ( FSA Integer e
>                        , ForbiddenSubstrings e
>                        , ForbiddenSubsequences e
>                        )
> reformApproximation alphabet literals
>     | isEmpty literals  =  (totalWithAlphabet alphabet, empty, empty)
>     | otherwise         =
>         ( complementDeterministic .
>           build alphabet . singleton .
>           makeConstraint .
>           tmap singleton $
>           Set.toAscList literals
>         , collapse (insert . makeTag)
>           (empty {attestedUnits = alphabet}) substrings
>         , ForbiddenSubsequences {
>                 attestedAlphabet = alphabet
>               , getSubsequences  = tmap (\(Subsequence xs) -> singlify xs) $
>                 difference factors substrings
>               }
>         )
>     where factors = tmap (\(Literal _ f) -> f) literals
>           isSubstring (Substring _ _ _) = True
>           isSubstring _                 = False
>           substrings = keep isSubstring factors
>           singlify = tmap chooseOne
>           makeTag (Substring xs False False)  =  Free (singlify xs)
>           makeTag (Substring xs False True)   =  Final (singlify xs)
>           makeTag (Substring xs True False)   =  Initial (singlify xs)
>           makeTag (Substring xs True True)    =  Word (singlify xs)


Formatting output
=================

> output :: FilePath
>        -> FSA Integer String
>        -> ( ( FSA Integer String
>             , ForbiddenSubstrings String
>             , ForbiddenSubsequences String
>             )
>           , ( FSA Integer String
>             , ForbiddenSubstrings String
>             , ForbiddenSubsequences String
>             )
>           , Either () (Maybe FilePath)
>           )
>        -> String
> output name fsa ((strictFSA, ffs, fssqs), (_, rfs, rssqs), higher) =
>     concatMap unlines $ [ [ "[metadata]"
>                         , "name=" ++ show name
>                         , "alphabet=" ++ formatAlphabet (alphabet strictFSA)
>                         , "is_sl=" ++ show (formatBool (strictFSA == fsa &&
>                                                         isEmpty fssqs))
>                         , "k_sl=" ++ show (kFromFFs ffs)
>                         , "k_sp=" ++ show (kFromFSSQs fssqs)
>                         , "k_cosl=" ++ show (kFromFFs rfs)
>                         , "k_cosp=" ++ show (kFromFSSQs rssqs)
>                         , ""
>                         , "[forbidden substrings]"
>                         ]
>                       , formatForbiddenSubstrings ffs
>                       , ["", "[forbidden subsequences]"]
>                       , formatForbiddenSubsequences fssqs
>                       , ["", "[required substrings (at least one)]"]
>                       , formatForbiddenSubstrings rfs
>                       , ["", "[required subsequences (at least one)]"]
>                       , formatForbiddenSubsequences rssqs
>                       , [ ""
>                         , "[nonstrict constraints]"
>                         , "complete=" ++ show (formatBool (higher /= Left ()))
>                         , "file=" ++ either (const "") (maybe "" show) higher
>                         ]
>                       ]
>     where formatBool True = "yes"
>           formatBool _    = "no"
>           f a = trace a a

> formatForbiddenSubsequences :: ForbiddenSubsequences String -> [String]
> formatForbiddenSubsequences = formatSequences . getSubsequences

> formatForbiddenSubstrings :: ForbiddenSubstrings String -> [String]
> formatForbiddenSubstrings = formatSequences . makeSequences
>     where makeSequences fs = unionAll [ k False False (forbiddenFrees fs)
>                                       , k False True (forbiddenFinals fs)
>                                       , k True False (forbiddenInitials fs)
>                                       , k True True (forbiddenWords fs)
>                                       ]
>           k :: Bool -> Bool -> Set [String] -> Set [String]
>           k x y = let p = if x then prependFish else id
>                       a = if y then appendFish  else id
>                   in tmap (p . a)

> formatSequence :: [String] -> String
> formatSequence = concatMap (take 2 . (++ " ") . transliterateString)

> formatAlphabet :: Set String -> String
> formatAlphabet = formatSequence . Set.toAscList . tmap untransliterateString

> appendFish, prependFish :: [String] -> [String]
> prependFish  =  ("%|" :)
> appendFish   =  (++ ["|%"])

> factorSort :: [String] -> [String] -> Ordering
> factorSort x y
>     | size x < size y = LT
>     | size x > size y = GT
>     | otherwise       = compare
>                         (tmap untransliterateString x)
>                         (tmap untransliterateString y)

> formatSequences :: Collapsible s => s [String] -> [String]
> formatSequences = tmap formatSequence . sortBy factorSort . fromCollapsible

> kFromFFs :: ForbiddenSubstrings e -> Integer
> -- ignored alphabet in calculating k
> -- to unignore, use ``maximum [1, mw, mi, mr, mf]'' instead
> kFromFFs ffs = maximum [0, mw, mi, mr, mf]
>     where fm x = Set.findMax . insert 0 . tmap ((+ x) . size)
>           mw = fm 2 (forbiddenWords ffs)
>           mi = fm 1 (forbiddenInitials ffs)
>           mr = fm 0 (forbiddenFrees ffs)
>           mf = fm 1 (forbiddenFinals ffs)

> kFromFSSQs :: ForbiddenSubsequences e -> Integer
> kFromFSSQs = Set.findMax . insert 0 . tmap size . getSubsequences
