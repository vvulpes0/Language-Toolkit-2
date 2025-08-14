> {-# Language CPP #-}

#if !defined(MIN_VERSION_base)
# define MIN_VERSION_base(a,b,c) 0
#endif

> module Main (main) where

> import Data.Representation.FiniteSemigroup (FSMult, fstable)

> import System.Console.GetOpt ( ArgDescr(NoArg, ReqArg)
>                              , ArgOrder(RequireOrder)
>                              , OptDescr(Option)
>                              , getOpt
>                              , usageInfo
>                              )
> import System.Environment (getArgs)
> import System.Exit (exitFailure, exitSuccess)
> import System.IO ( IOMode(ReadMode)
>                  , hGetContents, hPutStrLn, stderr, withFile
>                  )

#if !MIN_VERSION_base(4,8,0)
> import Control.Applicative ((<*>), pure)
> import Data.Traversable (sequenceA)
#endif

> import Data.List (intercalate, nub)
> import Data.Map.Strict (Map)
> import qualified Data.Map.Strict as Map

> import LTK
> import LTK.DecideS
> import LTK.Porters.ATT (embedSymbolsATT)

> data Options = Options
>     { optShowVersion  ::  Bool
>     , optShowUsage    ::  Bool
>     , optQuiet        ::  Bool
>     , optNormalize    ::  Bool
>     , optReduce       ::  [Bool] -> Bool
>     , optType         ::  String -> FSA Integer String
>     , optSymbols      ::  Maybe FilePath
>     }

> defaultOptions :: Options
> defaultOptions
>     = Options
>       { optShowVersion  =  False
>       , optShowUsage    =  False
>       , optQuiet        =  False
>       , optNormalize    =  True
>       , optReduce       =  or
>       , optType         =  from ATT
>       , optSymbols      =  Nothing
>       }

> options :: [OptDescr (Options -> Options)]
> options
>     = [ Option ['a'] []
>         (NoArg (\opts -> opts { optType = from ATT }))
>         "format: AT&T (input) [default]"
>       , Option ['A'] []
>         (NoArg (\opts -> opts { optType = from ATTO }))
>         "format: AT&T (output)"
>       , Option ['j'] []
>         (NoArg (\opts -> opts { optType = from Jeff }))
>         "format: Jeff"
>       , Option ['p'] []
>         (NoArg (\opts -> opts { optType = from Pleb }))
>         "format: PLEB"
>       , Option ['e'] []
>         (NoArg (\opts -> opts { optReduce = or }))
>         "success if ANY class membership holds [default]"
>       , Option ['h','?'] []
>         (NoArg (\opts -> opts { optShowUsage = True }))
>         "show this help"
>       , Option ['n'] []
>         (NoArg (\opts -> opts { optNormalize = True }))
>         "normalize the automaton before classification [default]"
>       , Option ['N'] []
>         (NoArg (\opts -> opts { optNormalize = False }))
>         "do not normalize the automaton before classification"
>       , Option ['q'] []
>         (NoArg (\opts -> opts { optQuiet = True }))
>         "operate silently"
>       , Option ['s'] []
>         (ReqArg (\f opts -> opts { optSymbols = Just f }) "SYMBOLS")
>         "for AT&T-format files, read the symbol table from SYMBOLS"
>       , Option ['u'] []
>         (NoArg (\opts -> opts { optReduce = and }))
>         "success if ALL class memberships holds"
>       , Option ['v'] []
>         (NoArg (\opts -> opts { optShowVersion = True }))
>         "show version number"
>       ]

> main :: IO ()
> main = do
>   opts <- compilerOpts =<< getArgs
>   s <- getContents
>   uncurry (act s) opts


The main meat:
* if an unknown class was provided: die with sadness
* if version or usage information was requested: just give that and leave
* read the standard input for a machine, and the symbol table if given
* normalize it if requested, and produce a transition monoid
* if we're not acting in "quiet" mode:
  output pairs of requested classes and memberships
* exit with a status indicating success: ALL or ANY membership succeeded

> act :: String -> Options -> [String] -> IO ()
> act input opts classes
>     | optShowVersion opts  =   printVersion
>     | optShowUsage opts    =   printUsage
>     | null classes         =   printUsage >> exitFailure
>     | not $ null unknowns
>         = hPutStrLn stderr
>           ("unknown classes: " ++ intercalate ", " unknowns)
>           >> exitFailure
>     | otherwise
>         = do c <- classified
>              (if optQuiet opts then void else f) c
>              if optReduce opts c then exitSuccess else exitFailure
>     where printUsage = putStr $ usageInfo usageHeader options
>           unknowns = filter (`notElem` toCheck) classes
>           aut = readAut opts input
>           void = const (return ())
>           toCheck = filter (`elem` classes) $ topo inclusion
>           classified :: IO [Bool]
>           classified = fmap (mkChecklist toCheck) aut
>           f xs = putStr . display $ zip toCheck xs

> display, display' :: Show a => [a] -> String
> display [] = ""
> display xs = "[ " ++ display' xs
> display' [] = "]"
> display' (x:xs) = unlines (show x : map ((", " ++) . show) xs ++ ["]"])

> mkChecklist :: [String] -> FSA Integer String -> [Bool]
> mkChecklist toCheck aut = map (classify aut m) toCheck
>     where m = fstable $ syntacticSemigroup aut

> readAut :: Options -> String -> IO (FSA Integer String)
> readAut opts b = fmap
>                  ((if optNormalize opts then normalize else id)
>                   . optType opts)
>                  str
>     where str :: IO String
>           str = maybe (return b)
>                 (\fp -> withFile fp ReadMode embed)
>                 (optSymbols opts)
>           embed h = do s <- hGetContents h
>                        let e = uncurry (embedSymbolsATT b)
>                                . join (,) $ Just s
>                        force e `seq` return e

> classify :: (Ord n, Ord e) =>
>             FSA n e -> FSMult -> String -> Bool
> classify aut mon cls = maybe False f (classmap Map.!? cls)
>     where f = either ($ aut) ($ mon) . fst

The classmap maps strings representing classes
to the functions that decide membership;
these may be either monoid-based or acceptor-based.
Additionally the list of next-higher classes is provided,
and one could in theory use this information to do less work
if a query succeeds.
Here the higher-class list is included only
so that results may be listed in topographic order.

> classmap :: (Ord n, Ord e) =>
>             Map String
>             ( Either (FSA n e -> Bool) (FSMult -> Bool)
>             , [String])
> classmap = Map.fromList
>            [ ("1", (Left isTrivial, ["Trivial","Fin","CB","SP"]))
>            , ("Acom", (Right isAcoms, ["LTT","MTF"]))
>            , ("B", (Right isBs, ["FO2"]))
>            , ("CB", (Right isCBs, ["B","LT","Acom"]))
>            , ("Def", (Right isDefs, ["GD", "SL", "TDef"]))
>            , ("Dot1", (Right isDot1s, ["LPT"]))
>            , ("FO2", (Right isFO2s, ["FO2S", "GLT"]))
>            , ("FO2BF", (Left isFO2BF, ["SF"]))
>            , ("FO2B", (Right isFO2Bs, ["FO2BF"]))
>            , ("FO2S", (Right isFO2Ss, ["FO2B"]))
>            , ("Fin", (Left isFinite, ["Finite","Def", "PT", "RDef"]))
>            , ("Finite", (Left isFinite, ["Def", "PT", "RDef"]))
>            , ("GD", (Right isGDs, ["LT", "SPL", "TGD"]))
>            , ("GLPT", (Right isGLPTs, ["FO2B"]))
>            , ("GLT", (Right isGLTs, ["GLPT"]))
>            , ("LAcom", (Right isLAcoms, ["LPT", "TLAcom"]))
>            , ("LB", (Right isLBs, ["FO2S"]))
>            , ("LPT", (Right isLPTs, ["GLPT"]))
>            , ("LT", (Right isLTs, ["LB", "LTT", "TLT"]))
>            , ("LTT", (Right isLTTs, ["Dot1", "LAcom", "TLTT"]))
>            , ("MTDef", (Right isMTDefs, ["MTGD"]))
>            , ("MTF", (Right isMTFs, ["MTDef","MTRdef","PT"]))
>            , ("MTGD", (Right isMTGDs, ["FO2"]))
>            , ("MTRDef", (Right isMTRDefs, ["MTGD"]))
>            , ("PT", (Right isPTs, ["Dot1","FO2"]))
>            , ("RDef", (Right isRDefs, ["GD", "SL", "TRDef"]))
>            , ("SF", (Right isSFs, []))
>            , ("SL", (Left isSL, ["LT", "SPL","TSL"]))
>            , ("SP", (Left isSP, ["PT","SPL"]))
>            , ("SPL", (Left isSP, ["Dot1"]))
>            , ("TDef", (Right isTDefs, ["TGD", "TSL", "MTDef"]))
>            , ("TGD", (Right isTGDs, ["MTGD", "TLT"]))
>            , ("TLAcom", (Right isTLAcoms, ["TLPT"]))
>            , ("TLB", (Right isTLBs, ["FO2B"]))
>            , ("TLPT", (Right isTLPTs, ["GLPT"]))
>            , ("TLT", (Right isTLTs, ["GLT", "TLB", "TLTT"]))
>            , ("TLTT", (Right isTLTTs, ["TLAcom"]))
>            , ("TRDef", (Right isTRDefs, ["TGD", "TSL", "MTRDef"]))
>            , ("Trivial", (Left isTrivial, ["Fin","CB","SP"]))
>            , ("TSL", (Left isTSL, ["TLT"]))
>            ]


> inclusion :: [(String, String)]
> inclusion = foldr (expand . fmap snd) [] $ Map.assocs cm
>     where expand (x, ss) a = map ((,) x) ss ++ a
>           cm :: Map String
>             ( Either (FSA () () -> Bool) (FSMult -> Bool)
>             , [String])
>           cm = classmap

topographic sort:
output the nodes of a graph in an order
such if there is a path from A to B and no path from B to A,
then A comes before B.

> topo :: Eq a => [(a,a)] -> [a]
> topo xs = topo' (nub (map fst xs ++ map snd xs)) xs

> topo' :: Eq a => [a] -> [(a,a)] -> [a]
> topo' s [] = s
> topo' s xs
>     = case s of
>         [] -> []
>         (s1:sr) -> case p of
>                      [] -> s1 : topo' sr xs
>                      _ -> p ++ topo' (filter (`notElem` p) s) next
>     where ins = filter (`elem` s) . nub $ map fst xs
>           outs = nub $ map snd xs
>           p = filter (`notElem` outs) ins -- in-degree 0
>               ++ filter (`notElem` (ins ++ outs)) s -- lost
>           noi f = filter ((`elem` s) . f) . filter ((`notElem` p) . f)
>           next = noi snd $ noi fst xs

Version numbers are no longer per utility

> printVersion :: IO ()
> printVersion = putStrLn "Version 1.3"

> usageHeader :: String
> usageHeader = "usage: classify [OPTION...] class ..."

> compilerOpts :: [String] -> IO (Options, [String])
> compilerOpts argv
>     = case getOpt RequireOrder options argv
>       of (o, n, []  ) -> return (foldl (flip id) defaultOptions o, n)
>          (_, _, errs) -> ioError . userError $
>                          concat errs ++ usageInfo usageHeader options

> join :: Monad m => m (m b) -> m b
> join = (>>= id)

> force :: [a] -> [a]
> force [] = []
> force (x:xs) = force xs `seq` x : xs
