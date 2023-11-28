> {-# Language CPP #-}

#if !defined(MIN_VERSION_base)
# define MIN_VERSION_base(a,b,c) 0
#endif

> module Main (main) where

#if !MIN_VERSION_base(4,8,0)
> import Control.Applicative (pure, (<*>))
> import Data.Functor ((<$>))
#endif
> import Control.Monad.Trans.Class (lift)
> import Data.Char (isSpace, toLower)
> import Data.List (intercalate, nub)
> import Data.Maybe (fromMaybe)
> import Data.Set (Set)
> import System.Console.Haskeline ( InputT
>                                 , Interrupt(..)
>                                 , withInterrupt
>                                 , defaultSettings
>                                 , getInputLine
>                                 , haveTerminalUI
>                                 , outputStr
>                                 , outputStrLn
>                                 , runInputT
>                                 )
> import System.Environment (getEnvironment)
> import System.Directory ( XdgDirectory(XdgConfig)
>                         , createDirectoryIfMissing
>                         , doesFileExist
>                         , getHomeDirectory
>                         , getXdgDirectory
>                         )
> import System.FilePath ( (</>)
>                        , isPathSeparator
>                        , joinPath
>                        , splitDirectories
>                        , takeDirectory
>                        )
> import System.IO ( hClose
>                  , hGetContents
>                  , hPutStr
>                  , hPutStrLn
>                  , hSetBinaryMode
>                  , stderr
>                  , stdout
>                  )
> import Control.Monad.Catch (handle)
#if MIN_VERSION_base(4,4,0)
> import System.IO.Error (catchIOError)
#else
> import System.IO.Error (IOError, catch) -- We'll make our own
#endif

> import qualified Data.Set as Set

> import LTK.Decide       ( isLT
>                         , isLTT
>                         , isLPT
>                         , isDot1
>                         , isPT
>                         , isFO2, isFO2B, isFO2BF, isFO2S
>                         , isSF
>                         , isGLT, isGLPT
>                         , isFinite
>                         , isLAcom
>                         , isB, isLB
>                         , isTrivial
>                         , isMTF, isMTDef, isMTRDef, isMTGD
>                         , isVariety
>                         )
> import LTK.FSA
> import LTK.Learn.SL  (fSL)
> import LTK.Learn.SP  (fSP)
> import LTK.Learn.TSL (fTSL)
> import LTK.Learn.StringExt (Grammar(..), learn)
> import LTK.Parameters   ( Parameter(..)
>                         , pTier
>                         , pDef, pRDef, pGDef
>                         , pCB, pAcom
>                         , pSL, pSP
>                         )
> import LTK.Porters      ( ATT(ATT), ATTO(ATTO), Dot(Dot)
>                         , EggBox(EggBox)
>                         , SyntacticOrder(SyntacticOrder)
>                         , Jeff(Jeff)
>                         , formatSet, fromE, to
>                         )
> import LTK.Porters.ATT  (embedSymbolsATT, extractSymbolsATT)
> import LTK.Porters.Pleb ( Env
>                         , Expr
>                         , compileEnv
>                         , doParse
>                         , doStatements
>                         , doStatementsWithError
>                         , fromAutomaton
>                         , fromSemanticAutomaton
>                         , groundEnv
>                         , insertExpr
>                         , makeAutomaton
>                         , makeAutomatonE
>                         , parseExpr
>                         , restrictUniverse
>                         , tokenize
>                         )
> import LTK.Tiers     (project)


#if !MIN_VERSION_base(4,4,0)
> catchIOError :: IO a -> (IOError -> IO a) -> IO a
> catchIOError = catch
#endif

> import System.Process ( CreateProcess(std_err, std_in, std_out)
>                       , StdStream(CreatePipe, UseHandle)
>                       , createProcess
>                       , proc
>                       , waitForProcess
>                       )

> data PlebConfig = PlebConfig
>     { dotProg :: (String, [String])
>     , displayProg :: (String, [String])
>     , pagerProg :: Maybe (String, [String])
>     , formatting :: Bool
>     , promptString :: String
>     } deriving (Eq, Ord, Read, Show)

> writeStrLn :: String -> IO ()
> writeStrLn = runInputT defaultSettings . outputStrLn
> writeStr :: String -> IO ()
> writeStr = runInputT defaultSettings . outputStr

> writeVersion :: InputT IO ()
> writeVersion
>     = (\x -> if x then outputStr $ unlines header else return ())
>     =<< haveTerminalUI
>     where header = [ name ++ ", version " ++ version ++ ": " ++ url
>                    , ":help for help"
>                    ]
>           name = "plebby"
>           version = "1.1"
>           url = "https://hackage.haskell.org/package/language-toolkit"
> main :: IO ()
> main = do
>   pc <- getConfig
>   runInputT defaultSettings
>        $ (writeVersion >> processLines pc (empty, empty))


> getConfig :: IO PlebConfig
> getConfig = do
>   xdgPath <- (</> "config.ini") <$> getXdgDirectory XdgConfig "plebby"
>   homePath <- (</> ".plebby") <$> getHomeDirectory
>   xdgExists <- doesFileExist xdgPath
>   homeExists <- doesFileExist homePath
>   if xdgExists
>   then parseConfig base <$> readFile xdgPath
>   else if homeExists
>        then parseConfig base <$> readFile homePath
>        else return base
>       where base = PlebConfig { dotProg = ("dot", ["-Tpng"])
>                               , displayProg = ("display", [])
>                               , pagerProg = Nothing
>                               , formatting = True
>                               , promptString = "> "
>                               }

> parseConfig :: PlebConfig -> String -> PlebConfig
> parseConfig pc s = foldr go pc
>                    . map (\(a,b) -> (words a, words $ drop 1 b, b))
>                    . filter (not . null . snd)
>                    . map (break (== '=') . fst . break (== '#'))
>                    $ lines s
>     where go (["dot"],(x:xs),_) c = c { dotProg = (x, xs) }
>           go (["display"],(x:xs),_) c = c { displayProg = (x, xs) }
>           go (["formatting"],(x:_),_) c = c { formatting = mkBool x }
>           go (["pager"],(x:xs),_) c = c { pagerProg = Just (x, xs) }
>           go (["prompt"],_,b) c = c { promptString = extractString b }
>           go _ c = c
>           extractString = deescape . extractString'
>                           . drop 1 . dropWhile (/= '"')
>           extractString' [] = ""
>           extractString' ('"':_) = []
>           extractString' ('\\':x:xs) = '\\' : x : extractString' xs
>           extractString' (x:xs) = x : extractString' xs
>           mkBool x = map toLower x `elem` ["t","true","1"]

> prompt :: Monad m => PlebConfig -> InputT m String
> prompt pc = (\x -> if x then promptString pc else "")
>             <$> haveTerminalUI

> data Trither a b c = L a
>                    | M b
>                    | R c
>                      deriving (Eq, Ord, Read, Show)

> data ArgType = ArgE
>              | ArgF
>              | ArgI
>              | ArgS
>              | ArgV
>                deriving (Eq, Ord, Read, Show)

> data Command = Bindings
>              | D_EB Expr -- Display EggBox
>              | D_JE Expr -- Display J-minimized Form
>              | D_OJ Expr -- Display Green's L Order
>              | D_OL Expr -- Display Green's L Order
>              | D_OR Expr -- Display Green's R Order
>              | D_PSG Expr -- Display Powerset Graph
>              | D_SM Expr -- Display Syntactic Monoid
>              | D_SO Expr -- Display Syntactic Order
>              | Display Expr
>              | Dotify Expr
>              | DT_PSG Expr -- Dotify Powerset Graph
>              | DT_SM Expr -- Dotify Syntactic Monoid
>              | ErrorMsg String
>              | Help [(String, [ArgType], String)]
>              | Import FilePath
>              | LearnSL Int FilePath
>              | LearnSP Int FilePath
>              | LearnTSL Int FilePath
>              | Loadstate FilePath
>              | Read FilePath
>              | ReadATT FilePath FilePath FilePath
>              | ReadATTO FilePath FilePath FilePath
>              | ReadBin FilePath
>              | ReadJeff FilePath
>              | Reset
>              | RestoreUniverse
>              | RestrictUniverse
>              | Savestate FilePath
>              | Show String
>              | Unset String
>              | Write FilePath Expr
>              | WriteATT FilePath FilePath FilePath Expr
>                deriving (Eq, Read, Show)

> data Relation = CEqual Expr Expr
>               | CImply Expr Expr
>               | Equal Expr Expr
>               | IsAcom Expr
>               | IsB Expr
>               | IsCB Expr
>               | IsDef Expr
>               | IsDot1 Expr
>               | IsFin Expr
>               | IsFO2 Expr
>               | IsFO2B Expr
>               | IsFO2BF Expr
>               | IsFO2S Expr
>               | IsGD Expr
>               | IsGLPT Expr
>               | IsGLT Expr
>               | IsLAcom Expr
>               | IsLB Expr
>               | IsLT Expr
>               | IsLPT Expr
>               | IsLTT Expr
>               | IsMTDef Expr
>               | IsMTF Expr
>               | IsMTGD Expr
>               | IsMTRDef Expr
>               | IsPT Expr
>               | IsRDef Expr
>               | IsSF Expr
>               | IsSL Expr
>               | IsSP Expr
>               | IsTDef Expr
>               | IsTGD Expr
>               | IsTLAcom Expr
>               | IsTLB Expr
>               | IsTLT Expr
>               | IsTLPT Expr
>               | IsTLTT Expr
>               | IsTRDef Expr
>               | IsTrivial Expr
>               | IsTSL Expr
>               | IsVariety VType String Expr
>               | Subset Expr Expr
>               | SSubset Expr Expr -- Strict Subset
>                 deriving (Eq, Read, Show)

> data VType = VTStar | VTPlus | VTTier
>              deriving (Eq, Ord, Read, Show)

> processLines :: PlebConfig -> Env -> InputT IO ()
> processLines pc e = f =<< getinput =<< prompt pc
>     where f minput
>               = case minput
>                 of Nothing       ->  return ()
>                    Just ":quit"  ->  return ()
>                    Just line     ->  go line >>= processLines pc
>           getinput p = handle (\Interrupt -> return (Just ""))
>                        . withInterrupt $ getInputLine p
>           go line = handle (\Interrupt ->
>                             lift $ act pc e
>                             (L . ErrorMsg $ unlines ["interrupted"]))
>                     . withInterrupt . lift
>                     $ act pc e (processLine e line)

Always use "modwords" when FilePath objects are at issue,
so that file names can be quoted or escaped
in order to deal with spaces or other special characters.

> processLine :: Env -> String -> Trither Command Relation Env
> processLine d str
>     | not (isPrefixOf str ":")
>         = either (L . ErrorMsg . deescape) R
>           $ doStatementsWithError d str
>     | isStartOf str ":isvarietym"
>         = case words str
>           of (_:a:b)   ->  let ~(u,v) = getVDesc $ unwords (a:b)
>                            in g (M . IsVariety VTStar u <$> pe) v
>              _         ->  R d
>     | isStartOf str ":isvarietys"
>         = case words str
>           of (_:a:b)   ->  let ~(u,v) = getVDesc $ unwords (a:b)
>                            in g (M . IsVariety VTPlus u <$> pe) v
>              _         ->  R d
>     | isStartOf str ":isvarietyt"
>         = case words str
>           of (_:a:b)   ->  let ~(u,v) = getVDesc $ unwords (a:b)
>                            in g (M . IsVariety VTTier u <$> pe) v
>              _         ->  R d
>     | isStartOf str ":import"
>         = case modwords str
>           of [_,a]  ->  L (Import a)
>              _      ->  R d
>     | isStartOf str ":learnsl"
>         = case modwords str
>           of [_,a,b]  ->  if all (isIn "0123456789") a
>                           then L (LearnSL (read a) b)
>                           else R d
>              _        ->  R d
>     | isStartOf str ":learnsp"
>         = case modwords str
>           of [_,a,b]  ->  if all (isIn "0123456789") a
>                           then L (LearnSP (read a) b)
>                           else R d
>              _        ->  R d
>     | isStartOf str ":learntsl"
>         = case modwords str
>           of [_,a,b]  ->  if all (isIn "0123456789") a
>                           then L (LearnTSL (read a) b)
>                           else R d
>              _        ->  R d
>     | isStartOf str ":loadstate"
>         = case modwords str
>           of [_,a]  ->  L (Loadstate a)
>              _      ->  R d
>     | isStartOf str ":readatto"
>         = case modwords str
>           of [_,a,b,c]  ->  L (ReadATTO a b c)
>              _          ->  R d
>     | isStartOf str ":readatt"
>         = case modwords str
>           of [_,a,b,c]  ->  L (ReadATT a b c)
>              _          ->  R d
>     | isStartOf str ":readbin"
>         = case modwords str
>           of [_,a]  ->  L (ReadBin a)
>              _       ->  R d
>     | isStartOf str ":readjeff"
>         = case modwords str
>           of [_,a]  ->  L (ReadJeff a)
>              _       ->  R d
>     | isStartOf str ":read"
>         = case modwords str
>           of [_,a]  ->  L (Read a)
>              _      ->  R d
>     | isStartOf str ":savestate"
>         = case modwords str
>           of [_,a]  ->  L (Savestate a)
>              _      ->  R d
>     | isStartOf str ":show"
>         = case words str
>           of (_:a:as) -> L (Show (unwords (a:as)))
>              _        -> R d
>     | isStartOf str ":unset"
>         = case words str of
>             [_,a]  -> L (Unset a)
>             _      -> R d
>     | isStartOf str ":writeatt"
>         =  case modwords str
>            of (_:a:b:c:as) -> g (L . WriteATT a b c <$> pe) (unwords as)
>               _            -> R d
>     | isStartOf str ":write"
>         = case modwords str
>           of (_:a:as) -> g (L . Write a <$> pe) (unwords as)
>              _        -> R d
>     | otherwise =  doOne . filter (isStartOf str . fst) $ p12 commands
>     where pe        =  parseExpr
>           p2e       =  (,) <$> pe <*> pe
>           f (s, p)  =  g p (drop (length s) str)
>           g p x     =  either (L . ErrorMsg . deescape) fst
>                        . doParse p $ tokenize x
>           getVDesc  =  (\(a,b) -> (a ++ take 1 b, drop 1 b))
>                        . break (== ']')
>           p12       =  map (\(a,b,_,_) -> (a,b))
>           p134      =  map (\(w,_,y,z) -> (w,y,z))
>           doOne xs  =  case xs
>                        of (x:_)  ->  f x
>                           _      ->  L . ErrorMsg $
>                                      "unknown interpreter command\n"
>           isStartOf xs x
>               = isPrefixOf (map toLower xs) (map toLower x)
>                 && (all isSpace . take 1 $ drop (length x) xs)
>           commands
>               = [ ( ":bindings"
>                   , pure $ L Bindings
>                   , []
>                   , "print list of variables and their bindings"
>                   )
>                 , ( ":cequal"
>                   , M . uncurry CEqual <$> p2e
>                   , [ArgE, ArgE]
>                   , "compare two exprs for logical equivalence"
>                   )
>                 , ( ":cimplies"
>                   , M . uncurry CImply <$> p2e
>                   , [ArgE, ArgE]
>                   , "determine if expr1 logically implies expr2"
>                   )
>                 , ( ":compile"
>                   , pure . R $ compileEnv d
>                   , []
>                   , "convert all expr variables to automata"
>                   )
>                 , ( ":display"
>                   , L . Display <$> pe
>                   , [ArgE]
>                   , "show expr graphically via external display program"
>                   )
>                 , ( ":dot-psg"
>                   , L . DT_PSG <$> pe
>                   , [ArgE]
>                   , ":dot the powerset graph of expr"
>                   )
>                 , ( ":dot-synmon"
>                   , L . DT_SM <$> pe
>                   , [ArgE]
>                   , ":dot the syntactic monoid of expr"
>                   )
>                 , ( ":dot"
>                   , L . Dotify <$> pe
>                   , [ArgE]
>                   , "print a Dot file of expr"
>                   )
>                 , ( ":eggbox"
>                   , L . D_EB <$> pe
>                   , [ArgE]
>                   , "show egg-box of expr via external display program"
>                   )
>                 , ( ":equal"
>                   , M . uncurry Equal <$> p2e
>                   , [ArgE, ArgE]
>                   , "compare two exprs for set-equality"
>                   )
>                 , ( ":ground"
>                   , pure . R $ groundEnv d
>                   , []
>                   , "convert all expr variables to grounded automata"
>                   )
>                 , ( ":help"
>                   , pure . L . Help $ p134 commands
>                   , []
>                   , "print this help"
>                   )
>                 , ( ":implies"
>                   , M . uncurry Subset <$> p2e
>                   , [ArgE, ArgE]
>                   , "synonym for :subset"
>                   )
>                 , ( ":import"
>                   , error ":import not defined here"
>                   , [ArgF]
>                   , "read file as plebby script"
>                   )
>                 , ( ":isAcom"
>                   , M . IsAcom <$> pe
>                   , [ArgE]
>                   , "determine if expr is k,1-LTT"
>                   )
>                 , ( ":isB"
>                   , M . IsB <$> pe
>                   , [ArgE]
>                   , "determine if expr is a band"
>                   )
>                 , ( ":isCB"
>                   , M . IsCB <$> pe
>                   , [ArgE]
>                   , "determine if expr is a semilattice language"
>                   )
>                 , ( ":isDef"
>                   , M . IsDef <$> pe
>                   , [ArgE]
>                   , "determine if expr is a definite language"
>                   )
>                 , ( ":isDot1"
>                   , M . IsDot1 <$> pe
>                   , [ArgE]
>                   , "determine if expr has dot-depth at most one"
>                   )
>                 , ( ":isFinite"
>                   , M . IsFin <$> pe
>                   , [ArgE]
>                   , "determine if expr is finite"
>                   )
>                 , ( ":isFO2"
>                   , M . IsFO2 <$> pe
>                   , [ArgE]
>                   , "determine if expr is FO2[<]-definable"
>                   )
>                 , ( ":isFO2B"
>                   , M . IsFO2B <$> pe
>                   , [ArgE]
>                   , "determine if expr is FO2[<,bet]-definable"
>                   )
>                 , ( ":isFO2BF"
>                   , M . IsFO2BF <$> pe
>                   , [ArgE]
>                   , "determine if expr is FO2[<,betfac]-definable"
>                   )
>                 , ( ":isFO2S"
>                   , M . IsFO2S <$> pe
>                   , [ArgE]
>                   , "determine if expr is FO2[<,+1]-definable"
>                   )
>                 , ( ":isGD"
>                   , M . IsGD <$> pe
>                   , [ArgE]
>                   , "determine if expr is generalized definite"
>                   )
>                 , ( ":isGLPT"
>                   , M . IsGLPT <$> pe
>                   , [ArgE]
>                   , "determine if expr is generalized locally PT"
>                   )
>                 , ( ":isGLT"
>                   , M . IsGLT <$> pe
>                   , [ArgE]
>                   , "determine if expr is generalized locally testable"
>                   )
>                 , ( ":isLAcom"
>                   , M . IsLAcom <$> pe
>                   , [ArgE]
>                   , "determine if expr is locally Acom"
>                   )
>                 , ( ":isLB"
>                   , M . IsLB <$> pe
>                   , [ArgE]
>                   , "determine if expr is locally a band"
>                   )
>                 , ( ":isLPT"
>                   , M . IsLPT <$> pe
>                   , [ArgE]
>                   , "determine if expr is locally piecewise testable"
>                   )
>                 , ( ":isLT"
>                   , M . IsLT <$> pe
>                   , [ArgE]
>                   , "determine if expr is locally testable"
>                   )
>                 , ( ":isLTT"
>                   , M . IsLTT <$> pe
>                   , [ArgE]
>                   , "determine if expr is locally threshold testable"
>                   )
>                 , ( ":isMTDef"
>                   , M . IsMTDef <$> pe
>                   , [ArgE]
>                   , "determine if expr is multitier definite"
>                   )
>                 , ( ":isMTF"
>                   , M . IsMTF <$> pe
>                   , [ArgE]
>                   , "determine if expr is multitier co/finite"
>                   )
>                 , ( ":isMTGD"
>                   , M . IsMTGD <$> pe
>                   , [ArgE]
>                   , "determine if expr is multitier gen. definite"
>                   )
>                 , ( ":isMTRDef"
>                   , M . IsMTRDef <$> pe
>                   , [ArgE]
>                   , "determine if expr is multitier rev. definite"
>                   )
>                 , ( ":isPT"
>                   , M . IsPT <$> pe
>                   , [ArgE]
>                   , "determine if expr is piecewise testable"
>                   )
>                 , ( ":isRDef"
>                   , M . IsRDef <$> pe
>                   , [ArgE]
>                   , "determine if expr is a reverse definite language"
>                   )
>                 , ( ":isSF"
>                   , M . IsSF <$> pe
>                   , [ArgE]
>                   , "determine if expr is star-free"
>                   )
>                 , ( ":isSL"
>                   , M . IsSL <$> pe
>                   , [ArgE]
>                   , "determine if expr is strictly local"
>                   )
>                 , ( ":isSP"
>                   , M . IsSP <$> pe
>                   , [ArgE]
>                   , "determine if expr is strictly piecewise"
>                   )
>                 , ( ":isTDef"
>                   , M . IsTDef <$> pe
>                   , [ArgE]
>                   , "determine if expr is definite on a tier"
>                   )
>                 , ( ":isTGD"
>                   , M . IsTGD <$> pe
>                   , [ArgE]
>                   , "determine if expr is generalized definite on a tier"
>                   )
>                 , ( ":isTLAcom"
>                   , M . IsTLAcom <$> pe
>                   , [ArgE]
>                   , "determine if expr is tier-locally Acom"
>                   )
>                 , ( ":isTLB"
>                   , M . IsTLB <$> pe
>                   , [ArgE]
>                   , "determine if expr is tier-locally a band"
>                   )
>                 , ( ":isTLPT"
>                   , M . IsTLPT <$> pe
>                   , [ArgE]
>                   , "determine if expr is tier-locally piecewise testable"
>                   )
>                 , ( ":isTLT"
>                   , M . IsTLT <$> pe
>                   , [ArgE]
>                   , "determine if expr is tier-locally testable"
>                   )
>                 , ( ":isTLTT"
>                   , M . IsTLTT <$> pe
>                   , [ArgE]
>                   , "determine if expr is tier-LTT"
>                   )
>                 , ( ":isTRDef"
>                   , M . IsTRDef <$> pe
>                   , [ArgE]
>                   , "determine if expr is reverse definite on a tier"
>                   )
>                 , ( ":isTrivial"
>                   , M . IsTrivial <$> pe
>                   , [ArgE]
>                   , "determine if expr has only a single state"
>                   )
>                 , ( ":isTSL"
>                   , M . IsTSL <$> pe
>                   , [ArgE]
>                   , "determine if expr is strictly tier-local"
>                   )
>                 , ( ":isVarietyM"
>                   , error ":isVarietyM not defined here"
>                   , [ArgS, ArgE]
>                   , "determine if expr is in the *-variety"
>                   )
>                 , ( ":isVarietyS"
>                   , error ":isVarietyS not defined here"
>                   , [ArgS, ArgE]
>                   , "determine if expr is in the +-variety"
>                   )
>                 , ( ":isVarietyT"
>                   , error ":isVarietyT not defined here"
>                   , [ArgS, ArgE]
>                   , "determine if expr is in the +-variety on a tier"
>                   )
>                 , ( ":Jmin"
>                   , L . D_JE <$> pe
>                   , [ArgE]
>                   , ":display the J-minimized version of expr"
>                   )
>                 , ( ":learnSL"
>                   , error ":learnSL not defined here"
>                   , [ArgI, ArgF]
>                   , "infer k-SL grammar, bind result to 'it'"
>                   )
>                 , ( ":learnSP"
>                   , error ":learnSP not defined here"
>                   , [ArgI, ArgF]
>                   , "infer k-SP grammar, bind result to 'it'"
>                   )
>                 , ( ":learnTSL"
>                   , error ":learnTSL not defined here"
>                   , [ArgI, ArgF]
>                   , "infer k-TSL grammar, bind result to 'it'"
>                   )
>                 , ( ":loadstate"
>                   , error ":loadstate not defined here"
>                   , [ArgF]
>                   , "restore state from file"
>                   )
>                 , ( ":orderJ"
>                   , L . D_OJ <$> pe
>                   , [ArgE]
>                   , "display Green's J-order of expr"
>                   )
>                 , ( ":orderL"
>                   , L . D_OL <$> pe
>                   , [ArgE]
>                   , "display Green's L-order of expr"
>                   )
>                 , ( ":orderR"
>                   , L . D_OR <$> pe
>                   , [ArgE]
>                   , "display Green's R-order of expr"
>                   )
>                 , ( ":psg"
>                   , L . D_PSG <$> pe
>                   , [ArgE]
>                   , ":display the powerset graph of expr"
>                   )
>                 , ( ":quit"
>                   , error ":quit not defined here"
>                   , []
>                   , "exit plebby"
>                   )
>                 , ( ":readATT"
>                   , error ":readatt not defined here"
>                   , [ArgF, ArgF, ArgF]
>                   , "read AT&T files, bind input-projection to 'it'"
>                   )
>                 , ( ":readATTO"
>                   , error ":readatto not defined here"
>                   , [ArgF, ArgF, ArgF]
>                   , "read AT&T files, bind output-projection to 'it'"
>                   )
>                 , ( ":readBin"
>                   , error ":readbin not defined here"
>                   , [ArgF]
>                   , "read binary expr from file, bind to 'it'"
>                   )
>                 , ( ":readJeff"
>                   , error ":readjeff not defined here"
>                   , [ArgF]
>                   , "read Jeff format automaton file, bind to 'it'"
>                   )
>                 , ( ":read"
>                   , error ":read not defined here"
>                   , [ArgF]
>                   , "read Pleb file"
>                   )
>                 , ( ":reset"
>                   , pure $ L Reset
>                   , []
>                   , "purge the current environment"
>                   )
>                 , ( ":restore-universe"
>                   , pure $ L RestoreUniverse
>                   , []
>                   , "set universe to all and only necessary symbols"
>                   )
>                 , ( ":restrict"
>                   , pure $ L RestrictUniverse
>                   , []
>                   , "remove non-universe symbols from the environment"
>                   )
>                 , ( ":savestate"
>                   , error ":savestate not defined here"
>                   , [ArgF]
>                   , "write current state to file"
>                   )
>                 , ( ":show"
>                   , error ":show not defined here"
>                   , [ArgV]
>                   , "print meaning(s) of var"
>                   )
>                 , ( ":strict-subset"
>                   , M . uncurry SSubset <$> p2e
>                   , [ArgE, ArgE]
>                   , "determine if expr1 is a strict subset of expr2"
>                   )
>                 , ( ":subset"
>                   , M . uncurry Subset <$> p2e
>                   , [ArgE, ArgE]
>                   , "determine if expr1 is a subset of expr2"
>                   )
>                 , ( ":synmon"
>                   , L . D_SM <$> pe
>                   , [ArgE]
>                   , ":display the syntactic monoid of expr"
>                   )
>                 , ( ":synord"
>                   , L . D_SO <$> pe
>                   , [ArgE]
>                   , "display the syntactic order of expr"
>                   )
>                 , ( ":unset"
>                   , error ":unset not defined here"
>                   , [ArgV]
>                   , "remove a single var from the environment"
>                   )
>                 , ( ":writeatt"
>                   , error ":writeatt not defined here"
>                   , [ArgF, ArgF, ArgF, ArgE]
>                   , "write AT&T form of expr to files (edges, ins, outs)"
>                   )
>                 , ( ":write"
>                   , error ":write not defined here"
>                   , [ArgF, ArgE]
>                   , "write binary form of expr to file"
>                   )
>                 ]

> doCommand :: PlebConfig -> Env -> Command -> IO Env
> doCommand pc e@(dict, subexprs) c
>     = case c
>       of Bindings
>              -> writeStrLn "# Symbol aliases:"
>                 >> mapM_ (\(n, s) ->
>                           writeStrLn
>                           (n ++ " <- " ++ deescape (formatSet s))
>                          ) dict
>                 >> writeStrLn "# Expression aliases:"
>                 >> writeStrLn (formatSet $ tmap fst subexprs)
>                 >> return e
>          Display x -> disp id x
>          D_EB x -> disp' (display' pc) (to EggBox) x
>          D_JE x -> disp (renameStatesBy (formatSet . tmap f)
>                         . minimizeOver jEquivalence
>                         . syntacticMonoid) x
>          D_OJ x -> disp' (display' pc) greenOrderJ x
>          D_OL x -> disp' (display' pc) greenOrderL x
>          D_OR x -> disp' (display' pc) greenOrderR x
>          D_PSG x -> disp (renameStatesBy formatSet . powersetGraph) x
>          D_SM x -> disp (renameStatesBy f . syntacticMonoid) x
>          D_SO x -> disp' (display' pc) (to SyntacticOrder) x
>          Dotify x -> dot id x
>          DT_PSG x -> dot (renameStatesBy formatSet . powersetGraph) x
>          DT_SM x -> dot (renameStatesBy f . syntacticMonoid) x
>          ErrorMsg str -> hPutStr stderr str >> return e
>          Help xs -> lessHelp pc xs >> return e
>          Import file
>              -> catchIOError
>                 (importScript pc e . lines
>                  =<< readFileWithExpansion file)
>                 (const
>                  $  hPutStrLn stderr
>                     ("failed to read \"" ++ file ++ "\"")
>                  >> return e
>                 )
>          LearnSL k file -> selearn (fSL k) file
>          LearnSP k file -> selearn (fSP k) file
>          LearnTSL k file -> selearn (fTSL k) file
>          Loadstate file
>              -> catchIOError (read <$> readFileWithExpansion file)
>                 (const
>                  $  hPutStrLn stderr
>                     ("failed to read \"" ++ file ++ "\"")
>                  >> return e
>                 )
>          Read file
>              -> catchIOError
>                 (doStatements e <$> readFileWithExpansion file)
>                 (const
>                  $  hPutStrLn stderr
>                     ("failed to read \"" ++ file ++ "\"")
>                  >> return e
>                 )
>          ReadATT f1 f2 f3 -> ratt f1 f2 f3 ATT
>          ReadATTO f1 f2 f3 -> ratt f1 f2 f3 ATTO
>          ReadBin file
>              -> catchIOError
>                 (maybe
>                  (hPutStrLn stderr
>                   "input not a binary automaton, environment unchanged" >>
>                   return e
>                  )
>                  (return . insertExpr e . fromSemanticAutomaton)
>                  . readMaybe =<< readFileWithExpansion file
>                 )
>                 (const
>                  $  hPutStrLn stderr
>                     ("failed to read \"" ++ file ++ "\"")
>                  >> return e
>                 )
>          ReadJeff file
>              -> catchIOError
>                 (either
>                  (const
>                   $  hPutStrLn stderr
>                      "input not a Jeff, environment unchanged"
>                   >> return e
>                  )
>                  (return . insertExpr e . fromAutomaton)
>                  . fromE Jeff =<< readFileWithExpansion file
>                 )
>                 (const
>                  $  hPutStrLn stderr
>                     ("failed to read \"" ++ file ++ "\"")
>                  >> return e
>                 )
>          Reset -> return (empty, empty)
>          --
>          -- Note: RestoreUniverse is implemented in a probably-inefficient
>          --       way, by making use of the side-effect that all assignments
>          --       properly update the universe.  The code currently just
>          --       rebinds every bound variable by creating and evaluating
>          --       assignment statements.  This should be done differently.
>          --
>          RestoreUniverse
>              -> let d' = keep ((/= "universe") . fst) dict
>                 in return . doStatements (d', subexprs) .
>                    unlines . fromCollapsible $
>                    union
>                    (tmap
>                     (\(a, _) ->
>                      "= " ++ a ++ " { " ++ a ++ " } "
>                     ) d'
>                    )
>                    (tmap (\(a, _) -> "= " ++ a ++ " " ++ a) subexprs)
>          RestrictUniverse -> return (restrictUniverse e)
>          Savestate file
>              -> catchIOError (writeAndCreateDir file . unlines $ [show e])
>                 (const $
>                  hPutStrLn stderr
>                  ("failed to write \"" ++ file ++ "\"")
>                 ) >> return e
>          Show name
>              -> if both
>                    (isNotIn (tmap fst subexprs))
>                    (isNotIn (tmap fst dict))
>                    name
>                 then writeStrLn
>                      ("undefined variable \"" ++ name ++ "\"")
>                      >> return e
>                 else mapM_
>                      (\(_,a) ->
>                       writeStrLn (name ++ " <- " ++ show a)
>                      ) (keep ((== name) . fst) subexprs)
>                      >> mapM_
>                      (\(_,s) ->
>                       writeStrLn
>                       (name ++ " <- " ++ deescape (formatSet s))
>                      ) (keep ((== name) . fst) dict)
>                      >> return e
>          Unset name
>              -> return ( keep ((/= name) . fst) dict
>                        , keep ((/= name) . fst) subexprs
>                        )
>          Write file x
>              -> let aut = makeAutomaton e x
>                 in maybe
>                    (hPutStrLn stderr "could not make automaton")
>                    (\a -> werr file (unlines [show a]))
>                    aut >> return e
>          WriteATT f1 f2 f3 x
>              -> let aut  =  fmap desemantify $ makeAutomaton e x
>                     w2   =  if f2 == "_" then const (return ()) else werr f2
>                     w3   =  if f3 == "_" then const (return ()) else werr f3
>                 in maybe
>                    (hPutStrLn stderr "could not make automaton")
>                    (\a ->
>                     let (ts, i, o) = extractSymbolsATT $ to ATT a
>                     in werr f1 ts >> w2 i >> w3 o
>                    ) aut >>
>                    return e
>     where disp :: (Ord n, Show n) =>
>                   (FSA Integer String -> FSA n String) -> Expr -> IO Env
>           disp = disp' (display pc)
>           disp' how x expr
>               = either (hPutStr stderr . deescape)
>                 (how . x . normalize . desemantify)
>                 (makeAutomatonE e expr)
>                 >> return e
>           dot :: (Ord n, Show n) =>
>                  (FSA Integer String -> FSA n String) -> Expr -> IO Env
>           dot = disp' (writeStr . to Dot)
>           f (_, xs) = '<' : unwords (map f' xs) ++ ">"
>           f' Epsilon = "ε"
>           f' (Symbol x) = x
>           werr ofile s
>               = catchIOError (writeAndCreateDir ofile s)
>                 (const $
>                  hPutStrLn stderr
>                  ("failed to write \"" ++ ofile ++
>                   if any isPathSeparator ofile
>                   then "\nDoes the directory exist?"
>                   else ""
>                  )
>                 )
>           selearn :: Grammar g => ([String] -> g String) -> FilePath -> IO Env
>           selearn method file
>               = catchIOError
>                 (insertExpr e . fromAutomaton . genFSA
>                  . learn method
>                  . map (Just . words) . lines
>                  <$> readFileWithExpansion file
>                 )
>                 (const
>                  $  hPutStrLn stderr
>                     ("failed to read \"" ++ file ++ "\"")
>                  >> return e
>                 )
>           ratt f1 f2 f3 typ
>               = catchIOError
>                 (either
>                  (const
>                   (hPutStrLn stderr
>                    "input not an ATT file, environment unchanged" >>
>                    return e
>                   )
>                  )
>                  (return . insertExpr e . fromAutomaton)
>                  . fromE typ
>                  =<< (embedSymbolsATT
>                       <$> readFileWithExpansion f1
>                       <*> (if f2 == "_"
>                            then mempty
>                            else Just <$> readFileWithExpansion f2
>                           )
>                       <*> (if f3 == "_"
>                            then mempty
>                            else Just <$> readFileWithExpansion f3
>                           )
>                  )
>                 )
>                 (const
>                  $  hPutStrLn stderr
>                     "failed to read input files"
>                  >> return e
>                 )


> doHelp :: Bool -> [(String, [ArgType], String)] -> String
> doHelp format xs
>     = showArg ArgE ++ " = expression, "  ++
>       showArg ArgF ++ " = file, "        ++
>       showArg ArgI ++ " = int, "         ++
>       showArg ArgS ++ " = string, "      ++
>       showArg ArgV ++ " = variable\n\n"  ++
>       unlines s2
>     where cs = zipWith (++) (map bold $ p1 xs) (map showArgs (p2 xs))
>           s1 = let l = foldr (max . lengthsgr) 0 cs
>                in map (alignl (l + 2) . alignr l) cs
>           s2 = zipWith (++) s1 (p3 xs)
>           alignr l s = takesgr (l - lengthsgr s) (cycle " ") ++ s
>           alignl l s = takesgr l (s ++ cycle " ")
>           wrap s = '<' : s ++ ">"
>           sgr :: Int -> String -> String
>           sgr n s = if format
>                     then "\27[" ++ shows n ('m' : s ++ "\27[m")
>                     else s
>           bold = (++ sgr 0 "") . sgr 1
>           showArg ArgE  =  wrap $ sgr 4 "e"
>           showArg ArgF  =  wrap $ sgr 4 "f"
>           showArg ArgI  =  wrap $ sgr 4 "i"
>           showArg ArgS  =  wrap $ sgr 4 "s"
>           showArg _     =  wrap $ sgr 4 "v"
>           showArgs = concatMap ((' ':) . showArg)
>           p1 = map (\(a,_,_) -> a)
>           p2 = map (\(_,b,_) -> b)
>           p3 = map (\(_,_,c) -> c)

> lengthsgr :: String -> Int
> lengthsgr ('\27':xs) = lengthsgr . drop 1 . snd $ break (== 'm') xs
> lengthsgr (_:xs) = 1 + lengthsgr xs
> lengthsgr _ = 0

> takesgr :: Int -> String -> String
> takesgr _ [] = []
> takesgr n (x:xs)
>     | n < 1 = []
>     | otherwise = case x of
>                     '\27' -> sgrseq ++ takesgr n (drop 1 post)
>                     _     -> x : takesgr (n - 1) xs
>     where (pre,post) = break (== 'm') xs
>           sgrseq = '\27' : pre ++ take 1 post

> lessHelp :: PlebConfig -> [(String, [ArgType], String)] -> IO ()
> lessHelp pc xs = do
>   mpager <- (map snd . filter ((==) "PAGER" . fst)) <$> getEnvironment
>   let args   =  if formatting pc then ["-sR"] else ["-s"]
>       ps     =  case pagerProg pc of
>                   Nothing  ->  case mpager of
>                                  (x:_) -> words x
>                                  _ -> []
>                   Just ys -> uncurry (:) ys
>       (p,s)  =  case ps of
>                   (y:ys) -> (y,ys)
>                   _ -> ("less",args)
>       lessP  =  (proc p s)
>                 { std_in = CreatePipe
>                 , std_out = UseHandle stdout
>                 , std_err = CreatePipe
>                 }
>   (Just p_stdin, _, Just p_stderr, less_ph) <- createProcess lessP
>   _ <- hGetContents p_stderr
>   hPutStr p_stdin (doHelp (formatting pc) xs)
>   hClose p_stdin
>   _ <- waitForProcess less_ph
>   return ()

"Relation" isn't really just a "relation" anymore,
as it carries along a set of parameters.
Pure relations need to be wrapped.
The outer Maybe is for when parsing fails,
the inner Maybe is Nothing::False, (Just params)::True

> doRelation :: Env -> Relation -> Maybe (Maybe [Parameter String])
> doRelation e r
>     = case r
>       of CEqual p1 p2   ->  rel' id e (==) p1 p2
>          Equal p1 p2    ->  rel' desemantify e (==) p1 p2
>          CImply p1 p2   ->  rel' id e isSupersetOf p1 p2
>          IsAcom p       ->  check pAcom p
>          IsB p          ->  check (fromBool . isB) p
>          IsCB p         ->  check pCB p
>          IsDef p        ->  check pDef p
>          IsDot1 p       ->  check (fromBool . isDot1) p
>          IsFin p        ->  check (fromBool . isFinite) p
>          IsFO2 p        ->  check (fromBool . isFO2) p
>          IsFO2B p       ->  check (fromBool . isFO2B) p
>          IsFO2BF p      ->  check (fromBool . isFO2BF) p
>          IsFO2S p       ->  check (fromBool . isFO2S) p
>          IsGD p         ->  check pGDef p
>          IsGLPT p       ->  check (fromBool . isGLPT) p
>          IsGLT p        ->  check (fromBool . isGLT) p
>          IsLAcom p      ->  check (fromBool . isLAcom) p
>          IsLB p         ->  check (fromBool . isLB) p
>          IsLPT p        ->  check (fromBool . isLPT) p
>          IsLT p         ->  check (fromBool . isLT) p
>          IsLTT p        ->  check (fromBool . isLTT) p
>          IsMTDef p      ->  check (fromBool . isMTDef) p
>          IsMTF p        ->  check (fromBool . isMTF) p
>          IsMTGD p       ->  check (fromBool . isMTGD) p
>          IsMTRDef p     ->  check (fromBool . isMTRDef) p
>          IsPT p         ->  check (fromBool . isPT) p
>          IsRDef p       ->  check pRDef p
>          IsSF p         ->  check (fromBool . isSF) p
>          IsSL p         ->  check pSL p
>          IsSP p         ->  check pSP p
>          IsTDef p       ->  check (pTier pDef) p
>          IsTGD p        ->  check (pTier pGDef) p
>          IsTLAcom p     ->  check (tierX isLAcom) p
>          IsTLB p        ->  check (tierX isLB) p
>          IsTLT p        ->  check (tierX isLT) p
>          IsTLPT p       ->  check (tierX isLPT) p
>          IsTLTT p       ->  check (tierX isLTT) p
>          IsTRDef p      ->  check (pTier pRDef) p
>          IsTrivial p    ->  check (fromBool . isTrivial) p
>          IsTSL p        ->  check (pTier pSL) p
>          IsVariety t s p
>              -> case t of
>                   VTStar -> check (fromBool . isV True s) p
>                   VTPlus -> check (fromBool . isV False s) p
>                   VTTier -> check (fromBool . isV False s . project) p
>          Subset p1 p2   ->  rel' desemantify e isSupersetOf p1 p2
>          SSubset p1 p2  ->  rel' desemantify e isProperSupersetOf p1 p2
>     where check f = fmap (f . normalize . desemantify)
>                     . makeAutomaton e
>           isV a b = fromMaybe False . isVariety a b
>           fromBool x = if x then Just [] else Nothing
>           rel' u v x y z = fromBool <$> relate u v x y z
>           tierX f = pTier (fromBool . f)

> relate :: (FSA Integer (Maybe String) -> x) ->
>           Env ->
>           (x -> x -> a) -> Expr -> Expr ->
>           Maybe a
> relate g e f p1 p2
>     = f' <$> makeAutomaton e p1 <*> makeAutomaton e p2
>     where f' x y = let ss = collapse (maybe id insert) empty $
>                             union (alphabet x) (alphabet y)
>                    in f (g $ semanticallyExtendAlphabetTo ss x)
>                         (g $ semanticallyExtendAlphabetTo ss y)

> act :: PlebConfig ->  Env -> Trither Command Relation Env -> IO Env
> act pc d = trither
>            (doCommand pc d)
>            (\r -> maybe err printP (doRelation d r) >> return d)
>            return
>     where err = hPutStrLn stderr "could not parse relation"
>           printP = writeStrLn . showParameters

> showParameters :: Show e => Maybe [Parameter e] -> String
> showParameters Nothing = "False"
> showParameters (Just []) = "True"
> showParameters (Just xs)
>     = "True: " ++ intercalate ", " (map showP xs)
>     where showP (PInt s x) = s ++ "=" ++ show x
>           showP (PSymSet s x) = s ++ "=" ++ deescape (formatSet x)

> importScript :: PlebConfig -> Env -> [String] -> IO Env
> importScript _ e [] = return e
> importScript pc e (a:as)
>     = flip (importScript pc) as =<< act pc e (processLine e a)



> deescape :: String -> String
> deescape ('\\' : '&' : xs) = deescape xs
> deescape ('\\' : 'a' : xs) = '\a' : deescape xs
> deescape ('\\' : 'b' : xs) = '\b' : deescape xs
> deescape ('\\' : 'f' : xs) = '\f' : deescape xs
> deescape ('\\' : 'n' : xs) = '\n' : deescape xs
> deescape ('\\' : 'r' : xs) = '\r' : deescape xs
> deescape ('\\' : 't' : xs) = '\t' : deescape xs
> deescape ('\\' : 'v' : xs) = '\v' : deescape xs
> deescape ('\\' : '\\' : xs) = '\\' : deescape xs
> deescape ('\\' : x : xs)
>     | isEmpty digits  =  x : deescape xs
>     | otherwise       =  toEnum (read digits) : deescape others
>     where (digits, others) = span (isIn "0123456789") (x:xs)
> deescape (x:xs)  =  x : deescape xs
> deescape _       =  []

> display :: (Ord n, Ord e, Show n, Show e) =>
>            PlebConfig -> FSA n e -> IO ()
> display pc = display' pc . to Dot

> display' :: PlebConfig -> String -> IO ()
> display' pc s = do
>   let dotP = (uncurry proc $ dotProg pc)
>              { std_in = CreatePipe
>              , std_out = CreatePipe
>              , std_err = CreatePipe
>              }
>   (Just p_stdin, Just pipe, Just p_stderr, dot_ph) <- createProcess dotP
>   _ <- hGetContents p_stderr
>   hSetBinaryMode pipe True
>   let displayP = (uncurry proc $ displayProg pc)
>                  { std_in = UseHandle pipe
>                  , std_out = CreatePipe
>                  , std_err = CreatePipe
>                  }
>   (_, Just d_stdout, Just d_stderr, _)  <- createProcess displayP
>   _ <- hGetContents d_stdout
>   _ <- hGetContents d_stderr
>   hPutStr p_stdin s
>   hClose p_stdin
>   _ <- waitForProcess dot_ph
>   return ()

> isPrefixOf :: (Eq a) => [a] -> [a] -> Bool
> isPrefixOf _ []  =  True
> isPrefixOf [] _  =  False
> isPrefixOf (x:xs) (y:ys)
>     | x == y     =  isPrefixOf xs ys
>     | otherwise  =  False

> trither :: (a -> d) -> (b -> d) -> (c -> d) -> Trither a b c -> d
> trither f g h t = case t
>                   of L a -> f a
>                      M b -> g b
>                      R c -> h c

> readMaybe :: (Read a) => String -> Maybe a
> readMaybe s = case reads s
>               of [(x, as)] -> if all isSpace as then Just x else Nothing
>                  _ -> Nothing

> -- |Separate a string into words, accounting for quoting and escapes.
> modwords :: String -> [String]
> modwords s = modwords' s ""

> modwords' :: String -> String -> [String]
> modwords' [] partial = [partial | not $ null partial]
> modwords' (a:xs) partial
>     | isSpace a = g $ modwords (dropWhile isSpace xs)
>     | a == '\\' = modwords' (drop 1 xs) (partial ++ take 1 xs)
>     | a == '\'' || a == '"' = f a
>     | otherwise = modwords' xs (partial ++ [a])
>     where f c = uncurry (:) . fmap modwords $ obtainWord (== c) xs partial
>           g = if null partial then id else (partial :)

> -- |The longest prefix of the input string
> -- which does not contain an unescaped character
> -- that satisfies the given predicate, and the remainder of the string.
> obtainWord :: (Char -> Bool) -> String -> String -> (String, String)
> obtainWord _ [] partial = (partial, "")
> obtainWord p (a:xs) partial
>     | a == '\\' = obtainWord p (drop 1 xs) (partial ++ take 1 xs)
>     | p a = (partial, xs)
>     | otherwise = obtainWord p xs (partial ++ [a])

> -- | writeFile, attempting to guarantee existence of its parents.
> -- Tilde-expansion is performed.
> writeAndCreateDir :: FilePath -> String -> IO ()
> writeAndCreateDir fp s = do
>     fp' <- expand fp
>     createDirectoryIfMissing True (takeDirectory fp')
>     writeFile fp' s

> -- | readFile, with tilde-expansion.
> readFileWithExpansion :: FilePath -> IO String
> readFileWithExpansion fp = do
>     fp' <- expand fp
>     readFile fp'

> -- | tilde-expand a filepath.
> -- Note that "~user" is unsupported, only plain "~".
> expand :: FilePath -> IO FilePath
> expand fp
>     = case parts of
>         ("~":xs) -> joinPath . (:xs)
>                     <$> catchIOError getHomeDirectory (const (pure "~"))
>         _ -> pure fp
>     where parts = splitDirectories fp





> greenOrderL :: (Ord n, Ord e, Show e) => FSA n e -> String
> greenOrderL = greenOrder gl
>     where gl m x y = State x `Set.member` primitiveIdealL m (State y)
> greenOrderR :: (Ord n, Ord e, Show e) => FSA n e -> String
> greenOrderR = greenOrder gr
>     where gr m x y = State x `Set.member` primitiveIdealR m (State y)
> greenOrderJ :: (Ord n, Ord e, Show e) => FSA n e -> String
> greenOrderJ = greenOrder gj
>     where gj m x y = State x `Set.member` primitiveIdeal2 m (State y)

> greenOrder :: (Ord n, Ord e, Show e) =>
>               (  FSA ([Maybe n], [Symbol e]) e
>               -> ([Maybe n], [Symbol e])
>               -> ([Maybe n], [Symbol e]) -> Bool)
>            -> FSA n e -> String
> greenOrder o f = showOrder isMonoid . sccGraph
>                  . renameStatesBy (unsymbols . snd)
>                  $ orderGraph (o m) m
>     where m = syntacticMonoid f
>           isMonoid
>               = case Set.toList (initials m) of
>                   (y:_) -> any ((==y) . destination) (transitions m)
>                   _ -> False

> -- |Draw the Hasse diagram of the given ordered graph
> -- in GraphViz @dot@ format.
> showOrder :: (Ord n, Show n) => Bool -> FSA (Set [n]) () -> String
> showOrder i g
>     = unlines
>       ([ "digraph {", "graph [rankdir=BT]"
>        , "node [shape=box]", "edge [dir=none]" ]
>       ++ sts
>       ++ map (uncurry showtr) (reduce rel)
>       ++ ["}"]
>       )
>     where qs = zip (map show [1::Integer ..]) . Set.toList $ states g
>           rel = [ (fst x, fst y)
>                 | x <- qs, y <- qs
>                 , x /= y
>                 , Transition { source = snd x
>                              , destination = snd y
>                              , edgeLabel = Symbol () }
>                   `elem` transitions g
>                 ]
>           showstr s = if null s then
>                           if i then "*" else ""
>                       else
>                           intercalate "\x2009" $ map showish s
>           showset x = '{' : intercalate ", " (map showstr x) ++ "}"
>           sts = map
>                 (\(x,y) ->
>                  concat [ x
>                         , " [label=\""
>                         , showset . Set.toList $ nodeLabel y
>                         , "\"];"]
>                 ) qs
>           showish = deescape . filter (/= '"') . show
>           showtr x y = x ++ " -> " ++ y ++ ";"

Compute the transitive reduction of an acyclic graph
which is specified by source/destination pairs.
The precondition, that the graph be acyclic, is not checked.

> reduce :: (Eq a) => [(a,a)] -> [(a,a)]
> reduce ps = [(x,y) | x <- nodes, y <- nodes, y `elem` ex x,
>              all ((`notElem` ps) . flip (,) y) (ex x)]
>     where nodes = nub $ map fst ps ++ map snd ps
>           ex p = let n = map snd $ filter ((p ==) . fst) ps
>                  in n ++ concatMap ex n
