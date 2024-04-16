> {-# Language CPP #-}

#if !defined(MIN_VERSION_base)
# define MIN_VERSION_base(a,b,c) 0
#endif

> module Main (main) where

> import Control.Monad ((<=<))
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

> import LTK.FSA (FSA(), difference, renameSymbolsBy, tr)
> import LTK.Porters (Dot(Dot), ATT(ATT), ATTO(ATTO),
>                     from, to, transliterateString)

> data Options = Options
>     { optShowVersion    ::  Bool
>     , optShowUsage      ::  Bool
>     , optTransliterate  ::  String -> String
>     , optType           ::  String -> FSA Integer String
>     , optOutput         ::  Maybe FilePath
>     }

> main :: IO ()
> main = uncurry act =<< compilerOpts =<< getArgs

> act :: Options -> [String] -> IO ()
> act opts files
>     | optShowVersion opts        =  printVersion
>     | optShowUsage opts          =  printUsage
>     | not . null $ drop 1 files  =  printUsage >> exitFailure
>     | otherwise                  =  printDot
>                                     (optType opts)
>                                     (optTransliterate opts)
>                                     file (optOutput opts)
>     where printUsage = putStr $ usageInfo usageHeader options
>           file       = case files of
>                          []       ->  Nothing
>                          ("-":_)  ->  Nothing
>                          (x:_)    ->  Just x

> printDot :: (String -> FSA Integer String) -> (String -> String) ->
>             Maybe FilePath -> Maybe FilePath -> IO ()
> printDot convert tf infile outfile
>     = maybe ($ stdin) (`withFile` ReadMode) infile
>       $ (output outfile . ((to Dot <$> renameSymbolsBy tf) . convert))
>         <=< hGetContents

> output :: Maybe FilePath -> String -> IO ()
> output file s = maybe ($ stdout) (`withFile` WriteMode) file $ \h ->
>                 hPutStr h s >> hFlush h

> usageHeader :: String
> usageHeader = "Usage: dotify [OPTION...] [file]"

> printVersion :: IO ()
> printVersion = putStrLn "Version 1.2"

> defaultOptions :: Options
> defaultOptions = Options
>                  { optShowVersion    =  False
>                  , optShowUsage      =  False
>                  , optTransliterate  =  id
>                  , optOutput         =  Nothing
>                  , optType           =  from ATTO
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
>         (NoArg (\opts -> opts { optTransliterate = transliterateString }))
>         "use transliterated symbols, e.g. L'"
>       , Option ['v'] []
>         (NoArg (\opts -> opts { optShowVersion = True }))
>         "show version number"
>       , Option ['w'] []
>         (NoArg (\opts -> opts { optTransliterate = id }))
>         "use wide symbols, e.g. w0.s0"
>       , Option ['l'] []
>         (NoArg (\opts -> opts { optType = from ATT }))
>         "use the input projection"
>       , Option ['r'] []
>         (NoArg (\opts -> opts { optType = from ATTO }))
>         "use the output projection"
>       ]

> compilerOpts :: [String] -> IO (Options, [String])
> compilerOpts argv
>     = case getOpt RequireOrder options argv
>       of (o, n, []  ) -> return (foldl (flip id) defaultOptions o, n)
>          (_, _, errs) -> ioError . userError $
>                          concat errs ++ usageInfo usageHeader options

> compactString :: String -> String
> compactString = flip difference "ws" . tr "." "/"
