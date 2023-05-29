> {-# Language CPP #-}

#if !defined(MIN_VERSION_base)
# define MIN_VERSION_base(a,b,c) 0
#endif

> module Main (main) where

> import Control.Concurrent ( MVar
>                           , ThreadId
>                           , forkFinally
>                           , newEmptyMVar
>                           , newMVar
>                           , putMVar
>                           , takeMVar
>                           )
> import Control.DeepSeq (NFData)
#if !MIN_VERSION_base(4,8,0)
> import Data.Functor ((<$>))
#endif
> import Data.List (sortBy)
> import Data.Maybe (fromMaybe)
> import Data.Set (Set)
> import System.Directory (createDirectoryIfMissing, doesFileExist)
> import System.Environment (getArgs)
> import System.Exit (die)
> import System.FilePath ((</>), takeBaseName)
> import System.IO ( IOMode(WriteMode)
>                  , hPutStrLn
>                  , stderr
>                  , withFile
>                  )
> import qualified Data.Set as Set

> import LTK.Decide
> import LTK.Extract
> import LTK.Factors
> import LTK.FSA
> import LTK.Porters

vvvvv Adapted from Haskell documentation on Control.Concurrent vvvvv
https://hackage.haskell.org/package/base-4.10.1.0/docs/Control-Concurrent.html

> waitForChildren :: MVar [MVar ()] -> IO ()
> waitForChildren children = f =<< takeMVar children
>     where f []      =  return ()
>           f (m:ms)  =  putMVar children ms >>
>                        takeMVar m >>
>                        waitForChildren children

> forkChild :: MVar [MVar ()] -> IO () -> IO ThreadId
> forkChild children io
>     = do mvar <- newEmptyMVar
>          childs <- takeMVar children
>          putMVar children (mvar : childs)
>          forkFinally io (\_ -> putMVar mvar ())

^^^^^ Adapted from Haskell documentation on Control.Concurrent ^^^^^

> hypothesesFile :: FilePath
> hypothesesFile = "Compiled" </> "constraints"

> outputDirectory :: FilePath
> outputDirectory = "Results"

> main :: IO ()
> main = do children <- newMVar []
>           filesToRead <- getArgs
>           createDirectoryIfMissing True outputDirectory
>           eHypotheses <- collectErrs "\n" <$> getHypotheses hypothesesFile
>           either (const . die) (f children) eHypotheses filesToRead
>           waitForChildren children
>     where f c h = mapM_ (forkChild c . processFile h)

> collectErrs :: Monoid m => m -> [Either m a] -> Either m [a]
> collectErrs x = foldr (either mkErr (fmap . (:))) (Right [])
>     where mkErr m = either
>                     (Left . mappend m . mappend x)
>                     (const $ Left m)

> getHypotheses :: FilePath ->
>                  IO [Either String (FilePath, FSA Integer String)]
> getHypotheses fp = f =<< doesFileExist fp
>     where f True  =  mapM getHypothesis . lines =<< readFile fp
>           f _     =  hPutStrLn stderr
>                      (fp ++ " not found, continuing without"
>                       ++ " nonstrict constraints")
>                      >> return []

> getHypothesis :: FilePath ->
>                  IO (Either String (FilePath, FSA Integer String))
> getHypothesis fp = f =<< doesFileExist fp
>     where f True  =  Right . (,) fp . from ATTO <$> readFile fp
>           f _     =  pure . Left $ "Could not find '" ++ fp ++ "'."

> processFile :: [(FilePath, FSA Integer String)] -> FilePath -> IO ()
> processFile hypotheses fp = f . (normalize . from ATTO) =<< readFile fp
>     where bn = takeBaseName fp
>           f x = writeFile
>                 (outputDirectory </> res)
>                 (output name x (factorization hypotheses x) ++ "\n")
>           lect = takeWhile (isIn "0123456789") bn
>           name = tr "_" " " $ dropWhile (isIn "0123456789_") bn
>           res  = if null lect then bn else lect


Return type of factorization is
(Strict Approximation, Costrict Approximation, X)
where X is either () if the factorization is incomplete,
                  Nothing if factorization is complete below testable level, or
                  A FilePath of the necessary compiled higher constraints

> factorization :: (Ord n, Ord e, NFData e) =>
>                  [(FilePath, FSA Integer e)] ->
>                  FSA n e ->
>                  ( ( FSA Integer e
>                    , ForbiddenSubstrings e
>                    , ForbiddenSubsequences e
>                    )
>                  , ( FSA Integer e
>                    , ForbiddenSubstrings e
>                    , ForbiddenSubsequences e
>                    )
>                  , Either () (Maybe FilePath)
>                  )
> factorization hypotheses fsa'
>     = ( strict
>       , costrict
>       , if scs == fsa
>         then Right Nothing
>         else if isEmpty workingHypotheses
>              then Left ()
>              else Right . Just . fst $
>                   chooseOne workingHypotheses
>       ) 
>     where fsa       =  renameStates fsa' `asTypeOf` normalize fsa'
>           strict    =  strictApproximation fsa
>           costrict  =  costrictApproximation fsa strict
>           scs       =  intersection (getFSA strict) $ getFSA costrict
>           getFSA (a, _, _) =  a
>           workingHypotheses
>               =  keep
>                  ((== fsa) . intersection scs .
>                   contractAlphabetTo (alphabet fsa) . snd
>                  ) hypotheses


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
>                        FSA Integer e ->
>                        ( FSA Integer e
>                        , ForbiddenSubstrings e
>                        , ForbiddenSubsequences e
>                        )
> strictApproximation fsa
>     | isSL fsa   =  (renameStates fsa, fs, empty)
>     | otherwise  =  (normalize (intersection sl sp), fs2, fq2)
>     where fs   =  forbiddenSubstrings fsa
>           sl   =  buildFSA fs
>           fq   =  forbiddenSubsequences fsa
>           sp   =  renameStates (subsequenceClosure fsa)
>           fq2  =  difference fq (forbiddenSubsequences sl)
>           -- f x == x is not forbidden by a subsequence
>           f x  =  not $ anyS (`isSSQ` x) (getSubsequences fq2)
>           fs2  =  fs { forbiddenWords     =  keep f (forbiddenWords fs)
>                      , forbiddenInitials  =  keep f (forbiddenInitials fs)
>                      , forbiddenFrees     =  keep f (forbiddenFrees fs)
>                      , forbiddenFinals    =  keep f (forbiddenFinals fs)
>                      }

If we wanted to instead favor piecewise factors, we could swap the
order of computation of fq2 and fs2 above.

The costrict approximation is formed from the residue of the strict
approximation and the original FSA.  Its computation is a bit more
involved, because we must remove potentially-required factors that are
not, in fact, required.  It seems to me that the best way to do that
is to find the smallest subset of factors such that all of them are
actually required.

> costrictApproximation :: (Ord e, NFData e) =>
>                          FSA Integer e ->
>                          ( FSA Integer e
>                          , ForbiddenSubstrings e
>                          , ForbiddenSubsequences e
>                          ) ->
>                          ( FSA Integer e
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
>                              , ForbiddenSubsequences e
>                              ) -> Set (Literal e)
> literalsFromApproximation (_, fs, fq) = unionAll [lfr, lin, lfi, lwo, lq]
>     where lq     =  tmap
>                     (forbidden . Subsequence . tmap singleton) $
>                     getSubsequences fq
>           f :: Ord x => Bool -> Bool -> Set [x] -> Set (Literal x)
>           f h t  =  tmap
>                     (\a -> forbidden $ Substring (tmap singleton a) h t)
>           lfr    =  f False False (forbiddenFrees fs)
>           lin    =  f True False (forbiddenInitials fs)
>           lfi    =  f False True (forbiddenFinals fs)
>           lwo    =  f True True (forbiddenWords fs)

> trueRequireds :: (Ord e, NFData e) =>
>                  FSA Integer e -> Set (Literal e) -> Set (Literal e)
> trueRequireds fsa = fromMaybe empty
>                     . findGood isGood Nothing
>                     . singleton
>                     . DecreasingSize
>     where isGood = isEmpty . intersection fsa
>                    . build (alphabet fsa)
>                    . singleton . makeConstraint . fromCollapsible
>                    . tmap singleton

> findGood :: Ord a =>
>             (Set a -> Bool) -> Maybe (DecreasingSize (Set a)) ->
>             Set (DecreasingSize (Set a)) -> Maybe (Set a)
> findGood isGood current subsets
>     | isEmpty subsets = fmap getDecreasing current
>     | isEmpty s  =  fmap getDecreasing current
>     -- Note that the "max" of two "DecreasingSize" objects
>     -- is the one with fewer elements
>     | isGood s   =  findGood isGood
>                     (maybe (Just s') (Just . max s') current)
>                     (ss `union` smaller)
>     | otherwise  =  findGood isGood
>                     current
>                     (tmap (fmap (`difference` s)) ss)
>     where (s', ss)  =  choose subsets
>           s         =  getDecreasing s'
>           smaller   =  tmap (DecreasingSize . difference s . singleton) s


We view required factors as co-strict constraints.  That is, a set of
required factors {A, B} means that A must occur _or_ B must occur,
not necessarily both.  If it is inconsistent with a given automaton
to forbid all factors in a set, then that automaton requires the
occurrence of at least one factor in that set.  Of course, this set
may contain factors that are not required, and therefore not
sufficient to satisfy the actual constraints of the stringset, so we
want to find a smallest such set.

If forbidding all factors in a set is not inconsistent, then no
subsets of that set will contain a complete set of required factors.
Therefore we begin with the complete set of potentially required
factors and iteratively produce smaller subsets while discarding
those sets that are known to be non-productive.


> reformApproximation :: (Ord e, NFData e) =>
>                        Set e -> Set (Literal e) ->
>                        ( FSA Integer e
>                        , ForbiddenSubstrings e
>                        , ForbiddenSubsequences e
>                        )
> reformApproximation alpha literals
>     | isEmpty literals  =  (totalWithAlphabet alpha, empty, empty)
>     | otherwise         =
>         ( complementDeterministic .
>           build alpha . singleton .
>           makeConstraint .
>           tmap singleton $
>           Set.toAscList literals
>         , collapse (insert . makeTag)
>           (empty {attestedUnits = alpha}) substrings
>         , ForbiddenSubsequences
>           { attestedAlphabet = alpha
>           , getSubsequences  = tmap (\(Subsequence xs) -> singlify xs) $
>             difference factors substrings
>           }
>         )
>     where factors = tmap (\(Literal _ f) -> f) literals
>           isSubstring (Substring {}) = True
>           isSubstring _                 = False
>           substrings = keep isSubstring factors
>           singlify = tmap chooseOne
>           makeTag (Substring xs False False)  =  Free (singlify xs)
>           makeTag (Substring xs False True)   =  Final (singlify xs)
>           makeTag (Substring xs True False)   =  Initial (singlify xs)
>           makeTag (Substring xs True True)    =  Word (singlify xs)
>           makeTag (Subsequence _)             =  error "No subsequences here"


Formatting output
=================

> output :: FilePath -> FSA Integer String ->
>           ( ( FSA Integer String
>             , ForbiddenSubstrings String
>             , ForbiddenSubsequences String
>             )
>           , ( FSA Integer String
>             , ForbiddenSubstrings String
>             , ForbiddenSubsequences String
>             )
>           , Either () (Maybe FilePath)
>           ) -> String
> output name fsa ((strictFSA, ffs, fssqs), (_, rfs, rssqs), higher)
>     = concatMap unlines
>       [ [ "[metadata]"
>         , "name=" ++ show name
>         , "alphabet=" ++ formatAlphabet (alphabet strictFSA)
>         , "is_sl=" ++ show (formatBool (strictFSA == fsa && isEmpty fssqs))
>         , "k_sl=" ++ show (kFromFFs ffs)
>         , "k_sp=" ++ show (kFromFSSQs fssqs)
>         , "k_cosl=" ++ show (kFromFFs rfs)
>         , "k_cosp=" ++ show (kFromFSSQs rssqs)
>         , ""
>         , "[forbidden substrings]"
>         ]
>       , formatForbiddenSubstrings ffs
>       , ["", "[forbidden subsequences]"]
>       , formatForbiddenSubsequences fssqs
>       , ["", "[required substrings (at least one)]"]
>       , formatForbiddenSubstrings rfs
>       , ["", "[required subsequences (at least one)]"]
>       , formatForbiddenSubsequences rssqs
>       , [ ""
>         , "[nonstrict constraints]"
>         , "complete=" ++
>           show (formatBool (higher /= Left ()))
>         , "file=" ++ either (const "") (maybe "" show) higher
>         ]
>       ]
>     where formatBool True = "yes"
>           formatBool _    = "no"

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
>     | isize x < isize y = LT
>     | isize x > isize y = GT
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
