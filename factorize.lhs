> module Main where
> import Exploratorium (obligatoriness, contractAlphabetTo)
> import Exporters
> import ExtractSP
> import FSA
> import LogicClasses
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
> main = withFile "to_read" ReadMode $ \h -> do
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

> findKFromFFs :: (Set [Symbol String],
>                  Set [Symbol String],
>                  Set [Symbol String],
>                  Set [Symbol String]) -> Integer
> findKFromFFs (words, inis, frees, finals) = maximum [1, mw, mi, mr, mf]
>     where fm = Set.findMax . insert 0 . tmap size
>           mw = fm words + 2
>           mi = fm inis + 1
>           mr = fm frees
>           mf = fm finals + 1

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

> formatSequence :: (Show e) => [Symbol e] -> String
> formatSequence = concatMap formatSymbol



> process :: String -> FSA Int String -> IO ()
> process name fsa = do
>   let spsl0 = (normalize (intersection sp sl0)) `isomorphic` normalize fsa
>       spsl1 = (normalize (intersection sp sl1)) `isomorphic` normalize fsa
>       spsl2 = spl `isomorphic` normalize fsa
>   createDirectoryIfMissing True "Results"
>   writeJeff (basename ++ ".sp.fsa") sp
>   writeDot (basename ++ ".sp.dot") sp
>   writeJeff (basename ++ ".sp.res.fsa") spr
>   writeDot (basename ++ ".sp.res.dot") spr
>   writeJeff (basename ++ ".sl0.fsa") sl0
>   writeDot (basename ++ ".sl0.dot") sl0
>   writeJeff (basename ++ ".sl1.fsa") sl1
>   writeDot (basename ++ ".sl1.dot") sl1
>   if spl /= fsa
>   then do
>     ns <- findSmallestSetOfNonStrictFactors spl fsa
>     maybe (
>            writeFFChart basename name isSL alpha (w2, i2, r2, f2) fssqs Nothing
>           ) (\a -> do
>                putStrLn $ (show basename) ++ " needs " ++ a
>                f <- normalize `fmap` intersection spl `fmap` get a
>                let y = renameStates (complement f)
>                    ffs3@(_,w3,i3,r3,f3) = forbiddenFactors
>                                           (normalize $ union y fsa)
>                    sl3 = untransliterate $ buildFSA ffs3
>                    ffs4 = (union w2 w3, union i2 i3,
>                            union r2 r3, union f2 f3)
>                writeJeff (basename ++ ".sl3.dot") sl3
>                writeDot (basename ++ ".sl3.dot") sl3
>                writeFFChart basename name isSL alpha ffs4 fssqs (Just a)
>             ) ns
>   else writeFFChart basename name isSL alpha (w2, i2, r2, f2) fssqs (Just "")
>     where sp = normalize $ subsequenceClosure fsa
>           fssqs = extractForbiddenSSQs fsa
>           spr = renameStates $ spresidue fsa
>           basename = filePathFromName name
>           ffs0@(u0,w0,i0,r0,f0) = forbiddenFactors (transliterate fsa)
>           sl0 = untransliterate $ buildFSA ffs0
>           isSL = slQ fsa /= 0
>           ffs1@(u1,w1,i1,r1,f1) = forbiddenFactors (transliterate spr)
>           sl1 = untransliterate $ buildFSA ffs1
>           ffs2@(u2,w2,i2,r2,f2) = (union u0 u1,
>                                    union w0 w1,
>                                    union i0 i1,
>                                    union r0 r1,
>                                    union f0 f1)
>           sl2 = untransliterate $ buildFSA ffs2
>           spl = normalize (intersection sp sl2)
>           get fp = withFile fp ReadMode $ \h -> do
>                      s <- hGetContents h
>                      return $!! c (readAndRelabelJeff s)
>           c = contractAlphabetTo alpha
>           alpha = alphabet fsa

> findSmallestSetOfNonStrictFactors :: FSA Int String -> FSA Int String -> IO (Maybe String)
> findSmallestSetOfNonStrictFactors approx orig =
>     withFile "Compiled/constraints" ReadMode $ \h -> do
>       fsas <- mapM get =<< lines `fmap` hGetContents h
>       let xs = filter f fsas
>       if null xs
>       then return Nothing
>       else return (Just . fst $ head xs)
>     where f x
>               | x' == orig = True
>               | otherwise  = slQ (normalize $ union y orig) /= 0
>                 where x' = normalize $ intersection (snd x) approx
>                       y  = renameStates (complement x')
>           get fp = withFile fp ReadMode $ \h -> do
>                      s <- hGetContents h
>                      return $!! (fp, c (readAndRelabelJeff s))
>           c = contractAlphabetTo (alphabet orig)

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
>                 (Set [Symbol String],  -- forbidden words
>                  Set [Symbol String],  -- initial forbidden substrings
>                  Set [Symbol String],  -- free forbidden substrings
>                  Set [Symbol String]) -> -- final forbidden substrings
>                 Set [Symbol String] -> -- forbidden subsequences
>                 Maybe String -> -- number of nonstrict subset
>                 IO ()
> writeFFChart fp name isSL alpha ffs@(w,i,r,f) fssqs ns =
>     withFile fp WriteMode $ \h -> do
>       hPutStrLn h "[metadata]"
>       hPutStrLn h ("name=" ++ show realName)
>       hPutStrLn h ("alphabet=" ++ show (formatAlphabet alpha))
>       hPutStrLn h ("is_sl=" ++ if isSL then show "yes" else show "no")
>       hPutStrLn h ("k_sl=" ++ show slK)
>       hPutStrLn h ("k_sp=" ++ show spK)
>       hPutStrLn h ""
>       hPutStrLn h "[forbidden words]" >> g h w
>       hPutStrLn h "[forbidden initial substrings]" >> g h i
>       hPutStrLn h "[forbidden free substrings]" >> g h r
>       hPutStrLn h "[forbidden final substrings]" >> g h f
>       hPutStrLn h "[forbidden subsequences]"
>       hPutStrLn h (formatSequences fssqs)
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

> writeForbiddenAdjacencyFactors :: String ->
>                                   (Set [Symbol String],
>                                    Set [Symbol String],
>                                    Set [Symbol String],
>                                    Set [Symbol String]) ->
>                                   IO ()
> writeForbiddenAdjacencyFactors name (w,i,r,f) =
>     withFile (filePathFromName name) AppendMode $ \h -> do
>       hPutStrLn h "[forbidden words]"
>       g h w
>       hPutStrLn h "[initial forbidden factors]"
>       g h i
>       hPutStrLn h "[free forbidden factors]"
>       g h r
>       hPutStrLn h "[final forbidden factors]"
>       g h f
>       hPutStrLn h ""
>     where g h = hPutStr h . formatSequences . tmap untransliterateSymbols

> filePathFromName = (++) "Results/" . takeWhile (isIn "0123456789")
