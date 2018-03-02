> module Main where

> import Porters (to, from, Dot(Dot), Jeff(Jeff), transliterate)

> import System.Console.GetOpt
> import System.Environment (getArgs)
> import System.Exit (exitFailure)
> import System.IO (Handle, IOMode(ReadMode, WriteMode),
>                   hFlush, hGetContents, hPutStr, stdin, stdout, withFile)

> data Options = Options
>     { optShowVersion   :: Bool
>     , optShowUsage     :: Bool
>     , optTransliterate :: Bool
>     , optOutput        :: Maybe FilePath
>     } deriving (Show)

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
>                          []      ->  Nothing
>                          ("-":_) -> Nothing
>                          (x:_)   ->  Just x

> printDot :: Bool -> Maybe FilePath -> Maybe FilePath -> IO ()
> printDot trp infile outfile
>     = maybe ($ stdin) (\f -> withFile f ReadMode) infile $ \h ->
>       output outfile  =<<
>       to Dot          <$>
>       transform       <$>
>       from Jeff       <$>
>       hGetContents h
>     where transform = if trp
>                       then transliterate
>                       else id

> output :: Maybe FilePath -> String -> IO ()
> output file s = maybe ($ stdout) (\f -> withFile f WriteMode) file $ \h ->
>                 hPutStr h s >> hFlush h

> usageHeader = "Usage: dotify [OPTION...] [file]"

> printVersion :: IO ()
> printVersion = putStrLn "Version 1.0"

> defaultOptions = Options
>                  { optShowVersion   = False
>                  , optShowUsage     = False
>                  , optTransliterate = False
>                  , optOutput        = Nothing
>                  }

> options :: [OptDescr (Options -> Options)]
> options =
>     [ Option ['h','?'] []
>       (NoArg (\opts -> opts { optShowUsage = True }))
>       "show this help",
>       Option ['o'] []
>       (ReqArg (\f opts -> opts { optOutput = if f == "-" then Nothing else Just f }) "FILE")
>       "output FILE",
>       Option ['t'] []
>       (NoArg (\opts -> opts { optTransliterate = True }))
>       "use transliterated symbols",
>       Option ['v'] []
>       (NoArg (\opts -> opts { optShowVersion = True }))
>       "show version number"
>     ]

> compilerOpts :: [String] -> IO (Options, [String])
> compilerOpts argv =
>     case getOpt RequireOrder options argv of
>       (o, n, []  ) -> return (foldl (flip id) defaultOptions o, n)
>       (_, _, errs) -> ioError . userError $
>                       concat errs ++ usageInfo usageHeader options
