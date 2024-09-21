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

> import qualified Data.Map as Map
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
> import LTK.Plebby.Help
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
>                         , makeAutomatonE
>                         , parseExpr
>                         , restoreUniverse
>                         , restrictUniverse
>                         , tokenize
>                         )


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
>           version = "1.2"
>           url = "https://hackage.haskell.org/package/language-toolkit"
> main :: IO ()
> main = do
>   pc <- getConfig
>   runInputT defaultSettings
>        $ (writeVersion >> processLines pc (Map.empty, Map.empty))


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
>              | Help String
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

> data Relation
>     = RDyad (  FSA Integer (Maybe String)
>             -> FSA Integer (Maybe String) -> Maybe [Parameter String])
>       Expr Expr
>     | RMono (FSA Integer (Maybe String) -> Maybe [Parameter String])
>       Expr

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

> fromBool :: Bool -> Maybe [Parameter String]
> fromBool x = if x then Just [] else Nothing

> isV :: (Ord n, Ord e) => Bool -> String -> FSA n e
>     -> Maybe [Parameter String]
> isV a b = maybe Nothing fromBool . isVariety a b

> apBoth :: (a -> b) -> (b -> b -> c) -> a -> a -> c
> apBoth f g x y = f x `g` f y

Always use "modwords" when FilePath objects are at issue,
so that file names can be quoted or escaped
in order to deal with spaces or other special characters.

> processLine :: Env -> String -> Trither Command Relation Env
> processLine d str
>     | not (isPrefixOf str ":")
>         = either (L . ErrorMsg . deescape) R
>           $ doStatementsWithError d str
>     | isStartOf str ":help"
>         = L . Help . dropWhile isSpace $ drop (length ":help") str
>     | isStartOf str ":isvarietym"
>         = case words str
>           of (_:a:b)   ->  let ~(u,v) = getVDesc $ unwords (a:b)
>                            in g (m (isV True u . n_d)) v
>              _         ->  R d
>     | isStartOf str ":isvarietys"
>         = case words str
>           of (_:a:b)   ->  let ~(u,v) = getVDesc $ unwords (a:b)
>                            in g (m (isV False u . n_d)) v
>              _         ->  R d
>     | isStartOf str ":isvarietyt"
>         = case words str
>           of (_:a:b)   ->  let ~(u,v) = getVDesc $ unwords (a:b)
>                            in g (m (pTier (isV False u) . n_d)) v
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
>     | otherwise =  doOne $ filter (isStartOf str . fst) commands
>     where pe        =  parseExpr
>           p2e       =  (,) <$> pe <*> pe
>           f (s, p)  =  g p (drop (length s) str)
>           g p x     =  either (L . ErrorMsg . deescape) fst
>                        . doParse p $ tokenize x
>           getVDesc  =  (\(a,b) -> (a ++ take 1 b, drop 1 b))
>                        . break (== ']')
>           doOne xs  =  case xs
>                        of (x:_)  ->  f x
>                           _      ->  L . ErrorMsg $
>                                      "unknown interpreter command\n"
>           isStartOf xs x
>               = isPrefixOf (map toLower xs) (map toLower x)
>                 && (all isSpace . take 1 $ drop (length x) xs)
>           m  x = M . (RMono x) <$> pe
>           m2 x = M . uncurry (RDyad (fmap fromBool . x)) <$> p2e
>           n_d = normalize . desemantify
>           commands
>               = [ (":bindings", pure $ L Bindings)
>                 , (":cequal", m2 (==))
>                 , (":cimplies", m2 isSupersetOf)
>                 , (":compile", pure . R $ compileEnv d)
>                 , (":display", L . Display <$> pe)
>                 , (":dot", L . Dotify <$> pe)
>                 , (":dotPSG", L . DT_PSG <$> pe)
>                 , (":dotSynmon", L . DT_SM <$> pe)
>                 , (":eggbox", L . D_EB <$> pe)
>                 , (":equal", m2 (apBoth desemantify (==)))
>                 , (":ground", pure . R $ groundEnv d)
>                 , (":help", error ":help not defined here")
>                 , (":implies", m2 (apBoth desemantify isSupersetOf))
>                 , (":import", error ":import not defined here")
>                 , (":isAcom", m (pAcom . n_d))
>                 , (":isB", m (fromBool . isB . n_d))
>                 , (":isCB", m (pCB . n_d))
>                 , (":isDef", m (pDef . n_d))
>                 , (":isDot1", m (fromBool . isDot1 . n_d))
>                 , (":isFinite", m (fromBool . isFinite . n_d))
>                 , (":isFO2", m (fromBool . isFO2 . n_d))
>                 , (":isFO2B", m (fromBool . isFO2B . n_d))
>                 , (":isFO2BF", m (fromBool . isFO2BF . n_d))
>                 , (":isFO2S", m (fromBool . isFO2S . n_d))
>                 , (":isGD", m (pGDef . n_d))
>                 , (":isGLPT", m (fromBool . isGLPT . n_d))
>                 , (":isGLT", m (fromBool . isGLT . n_d))
>                 , (":isLAcom", m (fromBool . isLAcom . n_d))
>                 , (":isLB", m (fromBool . isLB . n_d))
>                 , (":isLPT", m (fromBool . isLPT . n_d))
>                 , (":isLT", m (fromBool . isLT . n_d))
>                 , (":isLTT", m (fromBool . isLTT . n_d))
>                 , (":isMTDef", m (fromBool . isMTDef . n_d))
>                 , (":isMTF", m (fromBool . isMTF . n_d))
>                 , (":isMTGD", m (fromBool . isMTGD . n_d))
>                 , (":isMTRDef", m (fromBool . isMTRDef . n_d))
>                 , (":isPT", m (fromBool . isPT . n_d))
>                 , (":isRDef", m (pRDef . n_d))
>                 , (":isSF", m (fromBool . isSF . n_d))
>                 , (":isSL", m (pSL . n_d))
>                 , (":isSP", m (pSP . n_d))
>                 , (":isTDef", m (pTier pDef . n_d))
>                 , (":isTGD", m (pTier pGDef . n_d))
>                 , (":isTLAcom", m (pTier (fromBool . isLAcom) . n_d))
>                 , (":isTLB", m (pTier (fromBool . isLB) . n_d))
>                 , (":isTLPT", m (pTier (fromBool . isLPT) . n_d))
>                 , (":isTLT", m (pTier (fromBool . isLT) . n_d))
>                 , (":isTLTT", m (pTier (fromBool . isLTT) . n_d))
>                 , (":isTRDef", m (pTier pRDef . n_d))
>                 , (":isTrivial", m (fromBool . isTrivial . n_d))
>                 , (":isTSL", m (pTier pSL . n_d))
>                 , (":isVarietyM", error ":isVarietyM not defined here")
>                 , (":isVarietyS", error ":isVarietyS not defined here")
>                 , (":isVarietyT", error ":isVarietyT not defined here")
>                 , (":Jmin", L . D_JE <$> pe)
>                 , (":learnSL", error ":learnSL not defined here")
>                 , (":learnSP", error ":learnSP not defined here")
>                 , (":learnTSL", error ":learnTSL not defined here")
>                 , (":loadstate", error ":loadstate not defined here")
>                 , (":orderJ", L . D_OJ <$> pe)
>                 , (":orderL", L . D_OL <$> pe)
>                 , (":orderR", L . D_OR <$> pe)
>                 , (":psg", L . D_PSG <$> pe)
>                 , (":quit", error ":quit not defined here")
>                 , (":readATT", error ":readatt not defined here")
>                 , (":readATTO", error ":readatto not defined here")
>                 , (":readBin", error ":readbin not defined here")
>                 , (":readJeff", error ":readjeff not defined here")
>                 , (":read", error ":read not defined here")
>                 , (":reset", pure $ L Reset)
>                 , (":restoreUniverse", pure $ L RestoreUniverse)
>                 , (":restrict", pure $ L RestrictUniverse)
>                 , (":savestate", error ":savestate not defined here")
>                 , (":show", error ":show not defined here")
>                 , (":strictSubset"
>                   , m2 (apBoth desemantify isProperSupersetOf))
>                 , (":subset", m2 (apBoth desemantify isSupersetOf))
>                 , (":synmon", L . D_SM <$> pe)
>                 , (":synord", L . D_SO <$> pe)
>                 , (":unset", error ":unset not defined here")
>                 , (":writeATT", error ":writeatt not defined here")
>                 , (":write", error ":write not defined here")
>                 ]

> doCommand :: PlebConfig -> Env -> Command -> IO Env
> doCommand pc e@(dict, subexprs) c
>     = case c
>       of Bindings
>              -> writeStrLn "# Symbol aliases:"
>                 >> mapM_ (\(n, s) ->
>                           writeStrLn
>                           (n ++ " <- " ++ deescape (formatSet s))
>                          ) (Map.assocs dict)
>                 >> writeStrLn "# Expression aliases:"
>                 >> writeStrLn
>                    (formatSet . Set.fromList $ Map.keys subexprs)
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
>          Reset -> return (Map.empty, Map.empty)
>          RestoreUniverse -> return (restoreUniverse e)
>          RestrictUniverse -> return (restrictUniverse e)
>          Savestate file
>              -> catchIOError (writeAndCreateDir file . unlines $ [show e])
>                 (const $
>                  hPutStrLn stderr
>                  ("failed to write \"" ++ file ++ "\"")
>                 ) >> return e
>          Show name
>              -> if both
>                    (flip Map.notMember subexprs)
>                    (flip Map.notMember dict)
>                    name
>                 then writeStrLn
>                      ("undefined variable \"" ++ name ++ "\"")
>                      >> return e
>                 else mapM_
>                      (\a ->
>                       writeStrLn (name ++ " <- " ++ show a)
>                      ) (Map.filterWithKey (\k _ -> k == name) subexprs)
>                      >> mapM_
>                      (\s ->
>                       writeStrLn
>                       (name ++ " <- " ++ deescape (formatSet s))
>                      ) (Map.filterWithKey (\k _ -> k == name) dict)
>                      >> return e
>          Unset name
>              -> return ( Map.filterWithKey (\k _ -> k /= name) dict
>                        , Map.filterWithKey (\k _ -> k /= name) subexprs
>                        )
>          Write file x
>              -> let aut = makeAutomatonE e x
>                 in either
>                    (hPutStr stderr)
>                    (\a -> werr file (unlines [show a]))
>                    aut >> return e
>          WriteATT f1 f2 f3 x
>              -> let aut  =  fmap desemantify $ makeAutomatonE e x
>                     w2   =  if f2 == "_" then const (return ()) else werr f2
>                     w3   =  if f3 == "_" then const (return ()) else werr f3
>                 in either
>                    (hPutStr stderr)
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

> lessHelp :: PlebConfig -> String -> IO ()
> lessHelp pc xs = do
>   mpager <- (map snd . filter ((==) "PAGER" . fst)) <$> getEnvironment
>   lang' <- (map snd . filter ((==) "LANG" . fst)) <$> getEnvironment
>   cols' <- (map snd . filter ((==) "COLUMNS" . fst)) <$> getEnvironment
>   let topic  =  if null xs then ":help" else xs
>       width  =  case cols' of
>                   (x:_) -> if all (flip elem "0123456789") x
>                            then (read x) - 2
>                            else 78
>                   _ -> 78
>       lang   =  case lang' of
>                   (x:_) -> x
>                   _ -> ""
>       text   =  map ( formatRS
>                     $ if formatting pc
>                       then spanTypes
>                       else Map.fromList [('p',("","\n"))])
>                 . showHelp width lang $ getTopic lang topic
>       args   =  if formatting pc then ["-FsR"] else ["-Fs"]
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
>   hPutStr p_stdin $ unlines text
>   hClose p_stdin
>   _ <- waitForProcess less_ph
>   return ()

"Relation" isn't really just a "relation" anymore,
as it carries along a set of parameters.
Pure relations need to be wrapped.
The outer Either is for when parsing fails,
the inner Maybe is Nothing::False, (Just params)::True
For RDyad: can't just insert both, as we need equal alphabets,
and insertion overrides "it", so if "it" appears in an expression,
things go wonky.
Create, then extend, then operate.

> doRelation :: Env -> Relation
>            -> Either String (Maybe [Parameter String])
> doRelation e r
>     = case r of
>         RMono f p ->  f <$> makeAutomatonE e p
>         RDyad f p1 p2
>             ->  let m1 = makeAutomatonE e p1
>                     m2 = makeAutomatonE e p2
>                     ax = foldr (maybe id insert) Set.empty . alphabet
>                     u  = Set.union <$> (ax <$> m1) <*> (ax <$> m2)
>                     s  = semanticallyExtendAlphabetTo <$> u
>                 in f <$> (s <*> m1) <*> (s <*> m2)

> act :: PlebConfig ->  Env -> Trither Command Relation Env -> IO Env
> act pc d = trither
>            (doCommand pc d)
>            (\r -> either err printP (doRelation d r) >> return d)
>            return
>     where err = hPutStr stderr
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
