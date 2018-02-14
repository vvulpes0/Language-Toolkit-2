> module Main where
> import Containers
> import Exploratorium (obligatoriness, contractAlphabetTo)
> import Exporters
> import ExtractSP
> import FSA
> import ReadJeff
> import SLfactors

> import Control.Concurrent
> import Control.DeepSeq
> import Data.Set (Set)
> import qualified Data.Set as Set
> import System.Directory
> import System.IO
> import System.IO.Unsafe

> children :: MVar [MVar ()]
> children = unsafePerformIO (newMVar [])

vvvvv From Haskell documentation on Control.Concurrent vvvvv
https://hackage.haskell.org/package/base-4.10.1.0/docs/Control-Concurrent.html

> waitForChildren :: IO ()
> waitForChildren = do
>   cs <- takeMVar children
>   case cs of
>     []    ->  return ()
>     m:ms  ->  do
>             putMVar children ms
>             takeMVar m
>             waitForChildren

> forkChild :: IO () -> IO ThreadId
> forkChild io = do
>   mvar <- newEmptyMVar
>   childs <- takeMVar children
>   putMVar children (mvar : childs)
>   forkFinally io (\_ -> putMVar mvar ())

^^^^^ From Haskell documentation on Control.Concurrent ^^^^^

> main :: IO ()
> main = do
>   createDirectoryIfMissing True "Results"
>   withFile "to_read" ReadMode $ \h -> do
>          filePaths <- lines `fmap` hGetContents h
>          tagged <- mapM
>                    (\fp -> (,) (makeName fp) `fmap` readJeffFromFile fp)
>                    filePaths
>          mapM_ (forkChild . uncurry process) tagged
>          waitForChildren
>          where basename = until (null . filter (== '/'))
>                            (drop 1 . dropWhile (/= '/'))
>                noSuffix = takeWhile (/= '.') 
>                replace a b = map (\x -> if x == a then b else x)
>                makeName = replace '_' ' ' . noSuffix . basename

> readJeffFromFile :: FilePath -> IO (FSA Int String)
> readJeffFromFile fp = withFile fp ReadMode $ \h -> do
>                         fsa <- readAndRelabelJeff `fmap` hGetContents h
>                         return $!! fsa


> extract :: (Ord n, Ord e) => FSA n e -> (Set (Symbol e), Set [Symbol e])
> extract fsa = (alphabet fsa, extractForbiddenSSQs fsa)

> findKFromFFs :: (a,
>                  Set [Symbol String],
>                  Set [Symbol String],
>                  Set [Symbol String],
>                  Set [Symbol String]) -> Integer
> -- ignored alphabet in calculating k
> -- to unignore, use ``maximum [1, mw, mi, mr, mf]'' instead
> findKFromFFs (_,words, inis, frees, finals) = maximum [0, mw, mi, mr, mf]
>     where fm = Set.findMax . insert 0 . tmap size
>           tpa = tmap (prependFish . appendFish)
>           tp = tmap prependFish
>           ta = tmap appendFish
>           mw = fm (tpa words)
>           mi = fm (tp inis)
>           mr = fm frees
>           mf = fm (ta finals)

> slApproximation :: (Ord n) => FSA n String -> FSA Int String
> slApproximation f = renameStates . minimize . buildFSA $
>                     forbiddenFactors f

> format :: FilePath -> Set (Symbol String) -> Set [Symbol String] -> String
> format fp alpha fssqs = unlines
>                             ["# " ++ formatFP fp,
>                              "# " ++ formatAlphabet alpha,
>                              formatSequences fssqs]

> formatFP :: String -> String
> formatFP [] = []
> formatFP xs = formatFP' . last $ splitOn '/' xs
>     where formatFP' ('.':'f':'s':'a':xs) = []
>           formatFP' ('_':xs) = ' ':formatFP' xs
>           formatFP' (x:xs)   = x:formatFP' xs
>           formatFP' []       = []

> formatAlphabet :: (Show e) => Set (Symbol e) -> String
> formatAlphabet = concatMap formatSymbol . Set.toAscList

> formatSymbol :: (Show e) => Symbol e -> String
> formatSymbol Epsilon = []
> formatSymbol (Symbol e) = take 2 . (++ "  ") . filter (/= '"') .
>                           transliterateString $ show e

> formatSequences :: (Ord e, Show e) => Set [Symbol e] -> String
> formatSequences = unlines . map formatSequence . sortBy comp . Set.toList
>     where comp xs ys
>               | length xs < length ys = LT
>               | length xs > length ys = GT
>               | otherwise             = compare xs ys

> formatSubstrings :: (a,
>                      Set [Symbol String],
>                      Set [Symbol String],
>                      Set [Symbol String],
>                      Set [Symbol String]) -> String
> formatSubstrings (_,w,i,r,f) = formatSequences .
>                                tmap (map (fmap untransliterateString)) $
>                                unionAll [w', i', r', f']
>     where w' = tmap (prependFish . appendFish) w
>           i' = tmap prependFish i
>           r' = r
>           f' = tmap appendFish f

> prependFish, appendFish :: [Symbol String] -> [Symbol String]
> prependFish = (:) (Symbol "%|")
> appendFish = flip (++) [Symbol "|%"]

> formatSequence :: (Show e) => [Symbol e] -> String
> formatSequence = concatMap formatSymbol



> process :: String -> FSA Int String -> IO ()
> process name fsa = do
>   let (u0,w0,i0,r0,f0) = forbiddenFactors . transliterate $ fsa
>       sp = normalize (subsequenceClosure fsa)
>       (u1,w1,i1,r1,f1) = forbiddenFactors . transliterate $ spresidue fsa
>       ffs@(u2,w2,i2,r2,f2) = (union u0 u1, union w0 w1, union i0 i1,
>                               union r0 r1, union f0 f1)
>       sl = untransliterate $ buildFSA ffs
>       fssqs = extractForbiddenSSQs fsa `difference`
>               extractForbiddenSSQs sl
>       fssqs' = tmap (map (fmap transliterateString)) fssqs
>       k = keepPossible isSSQ fssqs'
>       ffs' = (u2, k w2, k i2, k r2, k f2)
>       strict = normalize $ sl `intersection` sp
>       res = normalize $ strict `difference` fsa
>       rfs = if slQ res /= 0 -- isSL res
>             then keepUseful ffs fssqs . forbiddenFactors $
>                  transliterate res
>             else (u0, empty, empty, empty, empty)
>       ccosl = normalize . union (singletonWithAlphabet alpha []) .
>               untransliterate $ buildFSA rfs
>       rssqs = if isSP res
>               then keepPossible isSSQ fssqs $ difference
>                    (extractForbiddenSSQs res)
>                    (extractForbiddenSSQs ccosl)
>               else empty
>       cosl = if isNull (complement ccosl) -- no forbidden factors in res
>              then totalWithAlphabet alpha
>              else normalize $ complement ccosl
>       cosp = if isSP res
>              then normalize . complement $ subsequenceClosure res
>              else totalWithAlphabet alpha
>       costrict = normalize (intersection cosl cosp)
>       scs = normalize $ flatIntersection [strict, cosl, cosp]
>       output = writeFFChart basename name isSL alpha ffs' fssqs rfs rssqs
>   writeJeff (basename ++ ".fsa") (normalize fsa)
>   writeDot (basename ++ ".dot") (normalize fsa)
>   writeJeff (basename ++ ".strict.fsa") strict
>   writeDot (basename ++ ".strict.dot") strict
>   writeJeff (basename ++ ".strict-costrict.fsa") scs
>   writeDot (basename ++ ".strict-costrict.dot") scs
>   if scs == fsa
>   then output (Just "")
>   else do
>     ns <- findSmallestSetOfNonStrictFactors scs fsa
>     maybe (do
>            putStrLn $ (show basename) ++ " is incomplete!"
>            output Nothing
>           ) (\a -> do
>                putStrLn $ (show basename) ++ " needs " ++ a
>                output (Just a)
>             ) ns
>   where
>     basename = filePathFromName name
>     isSL = slQ fsa /= 0
>     alpha = alphabet fsa

> findSmallestSetOfNonStrictFactors :: FSA Int String -> FSA Int String -> IO (Maybe String)
> findSmallestSetOfNonStrictFactors approx orig =
>     withFile "Compiled/constraints" ReadMode $ \h -> do
>       fsas <- mapM get =<< lines `fmap` hGetContents h
>       let xs = filter f fsas
>       if null xs
>       then return Nothing
>       else return (Just . fst $ head xs)
>     where f x = let x' = normalize $ intersection (snd x) approx
>                 in x' == orig
>           get fp = withFile fp ReadMode $ \h -> do
>                      s <- hGetContents h
>                      return $!! (fp, c (readAndRelabelJeff s))
>           c = contractAlphabetTo (alphabet orig)

> transliterateSymbols :: (Functor f, Container (s b1) (f String), Collapsible s) =>
>                         s (f String) -> s b1
> transliterateSymbols = tmap (fmap transliterateString)

> untransliterateSymbols :: (Functor f, Container (s b1) (f String), Collapsible s) =>
>                           s (f String) -> s b1
> untransliterateSymbols = tmap (fmap untransliterateString)

> writeJeff :: FilePath -> FSA Int String -> IO ()
> writeJeff fp fsa = withFile fp WriteMode $ \h -> do
>                      hPutStr h (exportJeff fsa)
>                      hFlush h

> writeDot :: FilePath -> FSA Int String -> IO ()
> writeDot fp fsa = withFile fp WriteMode $ \h -> do
>                     (hPutStr h . dotify . transliterate) fsa

> writeFFChart :: FilePath -> String -> -- filepath, name
>                 Bool -> -- is SL
>                 Set (Symbol String) -> -- alphabet
>                 (Set a, -- forbidden units
>                  Set [Symbol String],  -- forbidden words
>                  Set [Symbol String],  -- initial forbidden substrings
>                  Set [Symbol String],  -- free forbidden substrings
>                  Set [Symbol String]) -> -- final forbidden substrings
>                 Set [Symbol String] -> -- forbidden subsequences
>                 (Set a, -- required units
>                  Set [Symbol String],  -- required words
>                  Set [Symbol String],  -- initial required substrings
>                  Set [Symbol String],  -- free required substrings
>                  Set [Symbol String]) -> -- final required substrings
>                 Set [Symbol String] -> -- required subsequences
>                 Maybe String -> -- number of nonstrict subset
>                 IO ()
> writeFFChart fp name isSL alpha
>              ffs@(_,fw,fi,fr,ff) fssqs
>              rfs@(_,rw,ri,rr,rf) rssqs ns =
>     withFile fp WriteMode $ \h -> do
>       hPutStrLn h "[metadata]"
>       hPutStrLn h ("name=" ++ show realName)
>       hPutStrLn h ("alphabet=" ++ show (formatAlphabet alpha))
>       hPutStrLn h ("is_sl=" ++ if isSL then show "yes" else show "no")
>       hPutStrLn h ("k_sl=" ++ show slK)
>       hPutStrLn h ("k_sp=" ++ show spK)
>       hPutStrLn h ("k_cosl=" ++ show coslK)
>       hPutStrLn h ("k_cosp=" ++ show cospK)
>       hPutStrLn h ""
>       hPutStrLn h "[forbidden substrings]"
>       hPutStrLn h (formatSubstrings ffs)
>       hPutStrLn h "[forbidden subsequences]"
>       hPutStrLn h (formatSequences fssqs)
>       hPutStrLn h "[required substrings (at least one)]"
>       hPutStrLn h (formatSubstrings rfs)
>       hPutStrLn h "[required subsequences (at least one)]"
>       hPutStrLn h (formatSequences rssqs)
>       hPutStrLn h "[nonstrict constraints]"
>       maybe (do
>               hPutStrLn h ("complete=" ++ show "no")
>               hPutStrLn h "file="
>             ) (\a -> do
>                  hPutStrLn h ("complete=" ++ show "yes")
>                  hPutStrLn h ("file=" ++ if null a then "" else show a)
>               ) ns
>     where realName = dropWhile (== ' ') $
>                      dropWhile (isIn "0123456789") name
>           g h = hPutStrLn h . formatSequences . tmap (map (fmap untransliterateString))
>           slK = findKFromFFs ffs
>           spK = (maximum . insert 0 . tmap size) fssqs
>           coslK = findKFromFFs rfs
>           cospK = (maximum . insert 0 . tmap size) rssqs

> filePathFromName = (++) "Results/" . takeWhile (isIn "0123456789")



> keepPossible :: (Ord e) => ([Symbol e] -> [Symbol e] -> Bool) ->
>                 Set [Symbol e] -> Set [Symbol e] -> Set [Symbol e]
> keepPossible f fssqs potential =
>     keep (\a -> allS (not . flip f a) fssqs) potential

> isPrefix, isSuffix :: Eq a => [a] -> [a] -> Bool
> isPrefix x y
>     | null $ drop (length x - 1) y = False
>     | otherwise = and (zipWith (==) x y)
> isSuffix x y = isPrefix (Prelude.reverse x) (Prelude.reverse y)

> isSubstring :: Eq a => [a] -> [a] -> Bool
> isSubstring x = any (isPrefix x) . takeWhile (not . null) . iterate (drop 1)

> keepUseful :: (Set a, -- forbidden units
>                  Set [Symbol String],  -- forbidden words
>                  Set [Symbol String],  -- initial forbidden substrings
>                  Set [Symbol String],  -- free forbidden substrings
>                  Set [Symbol String]) -> -- final forbidden substrings
>                 Set [Symbol String] -> -- forbidden subsequences
>                 (Set a, -- potential required units
>                  Set [Symbol String],  -- potential required words
>                  Set [Symbol String],  -- potential initial required substrings
>                  Set [Symbol String],  -- potential free required substrings
>                  Set [Symbol String]) -> -- potential final required substrings
>                 (Set a,
>                  Set [Symbol String],
>                  Set [Symbol String],
>                  Set [Symbol String],
>                  Set [Symbol String])
> keepUseful ffs@(u,w,i,r,f) fssqs potential@(_,pw,pi,pr,pf) = (u,nw,ni,nr,nf)
>     where fssqs' = tmap (map (fmap transliterateString)) fssqs
>           k = keepPossible isSSQ fssqs'
>           fpa = prependFish . appendFish
>           fp  = prependFish
>           fa  = appendFish
>           ffs' = unionAll [tmap fpa w, tmap fp i, r, tmap fa f]
>           x g = (\a b -> isSubstring a (g b))
>           nw = k $ keepPossible (x fpa) ffs' pw
>           ni = k $ keepPossible (x fp) ffs' pi
>           nr = k $ keepPossible (x id) ffs' pr
>           nf = k $ keepPossible (x fa) ffs' pf
