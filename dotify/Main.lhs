> {-# Language CPP #-}

#if !defined(MIN_VERSION_base)
# define MIN_VERSION_base(a,b,c) 0
#endif

> module Main (main) where

#if !MIN_VERSION_base(4,8,0)
> import Data.Functor ((<$>))
#endif
> import System.Console.GetOpt ( ArgDescr(NoArg, ReqArg)
>                              , ArgOrder(RequireOrder)
>                              , OptDescr(Option)
>                              , getOpt
>                              , usageInfo
>                              )
> import System.Environment (getArgs)
> import System.Exit (exitFailure)
> import System.IO ( IOMode(ReadMode, WriteMode)
>                  , hFlush, hGetContents, hPutStr, stdin, stdout, withFile
>                  )

> import LTK.FSA (difference, renameSymbolsBy, tr)
> import LTK.Porters (Dot(Dot), Jeff(Jeff), from, to, untransliterateString)

> data Options = Options
>     { optShowVersion    ::  Bool
>     , optShowUsage      ::  Bool
>     , optTransliterate  ::  String -> String
>     , optOutput         ::  Maybe FilePath
>     }

> main :: IO ()
> main = uncurry act =<< compilerOpts =<< getArgs

> act :: Options -> [String] -> IO ()
> act opts files
>     | optShowVersion opts        =  printVersion
>     | optShowUsage opts          =  printUsage
>     | not . null $ drop 1 files  =  printUsage >> exitFailure
>     | otherwise                  =  printDot (optTransliterate opts)
>                                     file (optOutput opts)
>     where printUsage = putStr $ usageInfo usageHeader options
>           file       = case files of
>                          []       ->  Nothing
>                          ("-":_)  ->  Nothing
>                          (x:_)    ->  Just x

> printDot :: (String -> String) -> Maybe FilePath -> Maybe FilePath -> IO ()
> printDot tf infile outfile
>     = maybe ($ stdin) (flip withFile ReadMode) infile $ \h ->
>       output outfile      =<<
>       to Dot              <$>
>       renameSymbolsBy tf  <$>
>       from Jeff           <$>
>       hGetContents h

> output :: Maybe FilePath -> String -> IO ()
> output file s = maybe ($ stdout) (\f -> withFile f WriteMode) file $ \h ->
>                 hPutStr h s >> hFlush h

> usageHeader :: String
> usageHeader = "Usage: dotify [OPTION...] [file]"

> printVersion :: IO ()
> printVersion = putStrLn "Version 1.1"

> defaultOptions :: Options
> defaultOptions = Options
>                  { optShowVersion    =  False
>                  , optShowUsage      =  False
>                  , optTransliterate  =  untransliterateString
>                  , optOutput         =  Nothing
>                  }

> options :: [OptDescr (Options -> Options)]
> options
>     = [ Option ['c'] []
>         (NoArg (\opts -> opts { optTransliterate = compactString }))
>         "use compact symbols, e.g. 0/2"
>       , Option ['h','?'] []
>         (NoArg (\opts -> opts { optShowUsage = True }))
>         "show this help"
>       , Option ['o'] []
>         (ReqArg (\f opts ->
>                  opts { optOutput = if f == "-"
>                                     then Nothing
>                                     else Just f
>                       }
>                 ) "FILE"
>         )
>         "output FILE"
>       , Option ['t'] []
>         (NoArg (\opts -> opts { optTransliterate = id }))
>         "use transliterated symbols, e.g. L'"
>       , Option ['v'] []
>         (NoArg (\opts -> opts { optShowVersion = True }))
>         "show version number"
>       , Option ['w'] []
>         (NoArg (\opts -> opts { optTransliterate = untransliterateString }))
>         "use wide symbols, e.g. w0.s0"
>       ]

> compilerOpts :: [String] -> IO (Options, [String])
> compilerOpts argv
>     = case getOpt RequireOrder options argv
>       of (o, n, []  ) -> return (foldl (flip id) defaultOptions o, n)
>          (_, _, errs) -> ioError . userError $
>                          concat errs ++ usageInfo usageHeader options

> compactString :: String -> String
> compactString = flip difference "ws" . tr "." "/" . untransliterateString
