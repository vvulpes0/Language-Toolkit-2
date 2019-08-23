> module Main where

> import LTK.FSA
> import LTK.Porters (to, from, Dot(Dot), Jeff(Jeff), untransliterateString)

> import System.Console.GetOpt
> import System.Environment (getArgs)
> import System.Exit (exitFailure)
> import System.IO (Handle, IOMode(ReadMode, WriteMode),
>                   hFlush, hGetContents, hPutStr, stdin, stdout, withFile)

> import Data.Functor ((<$>))

> data Options = Options
>     { optShowVersion   :: Bool
>     , optShowUsage     :: Bool
>     , optTransliterate :: String -> String
>     , optOutput        :: Maybe FilePath
>     }

> main = uncurry act =<< compilerOpts =<< getArgs

> act :: Options -> [String] -> IO ()
> act opts files
>     | optShowVersion opts       = printVersion
>     | optShowUsage opts         = printUsage
>     | not . null $ drop 1 files = printUsage >> exitFailure
>     | otherwise                 = printDot (optTransliterate opts)
>                                   file (optOutput opts)
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

> usageHeader = "Usage: dotify [OPTION...] [file]"

> printVersion :: IO ()
> printVersion = putStrLn "Version 1.1"
> 
> defaultOptions = Options
>                  { optShowVersion   = False
>                  , optShowUsage     = False
>                  , optTransliterate = untransliterateString
>                  , optOutput        = Nothing
>                  }

> options :: [OptDescr (Options -> Options)]
> options =
>     [ Option ['c'] []
>       (NoArg (\opts -> opts { optTransliterate = compactString }))
>       "use compact symbols, e.g. 0/2"
>     , Option ['h','?'] []
>       (NoArg (\opts -> opts { optShowUsage = True }))
>       "show this help"
>     , Option ['o'] []
>       (ReqArg (\f opts -> opts { optOutput = if f == "-" then Nothing else Just f }) "FILE")
>       "output FILE"
>     , Option ['t'] []
>       (NoArg (\opts -> opts { optTransliterate = id }))
>       "use transliterated symbols, e.g. L'"
>     , Option ['v'] []
>       (NoArg (\opts -> opts { optShowVersion = True }))
>       "show version number"
>     , Option ['w'] []
>       (NoArg (\opts -> opts { optTransliterate = untransliterateString }))
>       "use wide symbols, e.g. w0.s0"
>     ]

> compilerOpts :: [String] -> IO (Options, [String])
> compilerOpts argv =
>     case getOpt RequireOrder options argv of
>       (o, n, []  ) -> return (foldl (flip id) defaultOptions o, n)
>       (_, _, errs) -> ioError . userError $
>                       concat errs ++ usageInfo usageHeader options

> compactString = flip difference "ws" . tr "." "/" . untransliterateString
