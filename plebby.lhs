> module Main where

> import FSA
> import Pleb ( Env
>             , Expr
>             , compileEnv
>             , doParse
>             , doStatements
>             , fromAutomaton
>             , fromSemanticAutomaton
>             , groundEnv
>             , insertExpr
>             , makeAutomaton
>             , parseExpr
>             , restrictUniverse
>             , tokenize
>             )
> import Porters ( Dot(..), Jeff(..), formatSet, to, fromE)
> import ExtractSL (isSL)
> import ExtractSP (isSP)

> import Control.Applicative ( Applicative(..) )
> import Control.Monad.Trans.Class ( lift )
> import Data.Char (isSpace)
> import Data.Functor ( (<$>) )
> import System.Console.Haskeline ( InputT
>                                 , defaultSettings
>                                 , getInputLine
>                                 , runInputT
>                                 )
> import System.IO ( hClose
>                  , hPutStr
>                  , hPutStrLn
>                  , hSetBinaryMode
>                  , stderr
>                  )
> import System.IO.Error ( catchIOError )
> import System.Process ( CreateProcess(..)
>                       , StdStream(..)
>                       , createProcess
>                       , proc
>                       , waitForProcess
>                       )

> main = runInputT defaultSettings (processLines (empty, empty, Nothing))

> prompt :: String
> prompt = "> "

> data Trither a b c = L a
>                    | M b
>                    | R c
>                      deriving (Eq, Ord, Read, Show)
> data Command = Bindings
>              | D_PSG Expr -- Display Powerset Graph
>              | D_SM Expr -- Display Syntactic Monoid
>              | Display Expr
>              | Dotify Expr
>              | DT_PSG Expr -- Dotify Powerset Graph
>              | DT_SM Expr -- Dotify Syntactic Monoid
>              | ErrorMsg String
>              | Import FilePath
>              | Loadstate FilePath
>              | Read FilePath
>              | ReadBin FilePath
>              | ReadJeff FilePath
>              | Reset
>              | RestoreUniverse
>              | RestrictUniverse
>              | Savestate FilePath
>              | Show String
>              | Unset String
>              | Write FilePath Expr
>              deriving (Eq, Read, Show)
> data Relation = Equal Expr Expr
>               | IsPT Expr
>               | IsSL Expr
>               | IsSP Expr
>               | Subset Expr Expr
>               | SSubset Expr Expr -- Strict Subset
>                 deriving (Eq, Read, Show)

> processLines :: Env -> InputT IO ()
> processLines env = do
>   minput <- getInputLine prompt
>   case minput of
>     Nothing -> return ()
>     Just ":quit" -> return ()
>     Just line -> lift (act env (processLine env line)) >>= processLines

> processLine :: Env -> String -> Trither Command Relation Env
> processLine d@(dict, subexprs, last) str
>     | null str                   =  R d
>     | not (isPrefixOf str ":")   =  R $ doStatements d str
>     | isPrefixOf str ":import" = case words str of
>                                       (_:a:[]) -> L (Import a)
>                                       _        -> R d
>     | isPrefixOf str ":loadstate" = case words str of
>                                       (_:a:[]) -> L (Loadstate a)
>                                       _        -> R d
>     | isPrefixOf str ":readBin"  =  case words str of
>                                       (_:a:[]) -> L (ReadBin a)
>                                       _        -> R d
>     | isPrefixOf str ":readJeff" =  case words str of
>                                       (_:a:[]) -> L (ReadJeff a)
>                                       _        -> R d
>     | isPrefixOf str ":read"     =  case words str of
>                                       (_:a:[]) -> L (Read a)
>                                       _        -> R d
>     | isPrefixOf str ":savestate" = case words str of
>                                       (_:a:[]) -> L (Savestate a)
>                                       _        -> R d
>     | isPrefixOf str ":show"     =  case words str of
>                                       (_:a:[]) -> L (Show a)
>                                       _        -> R d
>     | isPrefixOf str ":unset"    =  case words str of
>                                       (_:a:[]) -> L (Unset a)
>                                       _        -> R d
>     | isPrefixOf str ":write"    =  case words str of
>                                       (_:a:as) -> g ((L . Write a) <$> pe)
>                                                   (unwords as)
>     | otherwise                  =  doOne $
>                                     filter (isPrefixOf str . fst) commands
>     where pe        =  parseExpr dict subexprs
>           p2e       =  (,) <$> pe <*> pe
>           f (s, p)  =  g p (drop (length s) str)
>           g p x     =  either (L . err) fst . doParse p $ tokenize x
>           commands  =  [ (":bindings",       pure (L Bindings))
>                        , (":compile",        pure (R $ compileEnv d))
>                        , (":display",        ((L .         Display) <$> pe ))
>                        , (":dot-psg",        ((L .         DT_PSG ) <$> pe ))
>                        , (":dot-synmon",     ((L .         DT_SM  ) <$> pe ))
>                        , (":dot",            ((L .         Dotify ) <$> pe ))
>                        , (":equal",          ((M . uncurry Equal  ) <$> p2e))
>                        , (":ground",         pure (R $ groundEnv d))
>                        , (":implies",        ((M . uncurry Subset ) <$> p2e))
>                        , (":isPT",           ((M .         IsPT   ) <$> pe ))
>                        , (":isSL",           ((M .         IsSL   ) <$> pe ))
>                        , (":isSP",           ((M .         IsSP   ) <$> pe ))
>                        , (":psg",            ((L .         D_PSG  ) <$> pe ))
>                        , (":reset",          pure (L Reset))
>                        , (":restore-universe", pure (L RestoreUniverse))
>                        , (":restrict",       pure (L RestrictUniverse))
>                        , (":strict-subset",  ((M . uncurry SSubset) <$> p2e))
>                        , (":subset",         ((M . uncurry Subset ) <$> p2e))
>                        , (":synmon",         ((L .         D_SM   ) <$> pe ))
>                        ]
>           doOne xs  = case xs of
>                         (x:_)  ->  f x
>                         _      ->  L (ErrorMsg "unknown interpreter command\n")
>           err x = ErrorMsg x -- "failed to evaluate"

> doCommand :: Env -> Command -> IO Env
> doCommand e@(dict, subexprs, last) c
>     = case c of
>         Bindings -> do
>                putStrLn "# Symbol aliases:"
>                mapM_ (\(n, s) ->
>                       putStrLn (n ++ " <- " ++ deescape (formatSet s))
>                      ) dict
>                putStrLn "# Expression aliases:"
>                putStrLn (formatSet $ tmap fst subexprs)
>                return e
>         Display expr -> (maybe err (display . normalize . desemantify) $
>                          makeAutomaton (dict, subexprs, Just expr)) >>
>                         return e
>         D_PSG expr -> (maybe err
>                        (display . renameStatesBy formatSet . powersetGraph .
>                         normalize . desemantify) $
>                        makeAutomaton (dict, subexprs, Just expr)) >>
>                         return e
>         D_SM expr -> (maybe err
>                       (display . renameStatesBy f . syntacticMonoid .
>                        normalize . desemantify) $
>                       makeAutomaton (dict, subexprs, Just expr)) >>
>                      return e
>         Dotify expr -> (maybe err (p . normalize . desemantify) $
>                         makeAutomaton (dict, subexprs, Just expr)) >>
>                        return e
>         DT_PSG expr -> (maybe err
>                        (p . renameStatesBy formatSet . powersetGraph .
>                         normalize . desemantify) $
>                        makeAutomaton (dict, subexprs, Just expr)) >>
>                         return e
>         DT_SM expr -> (maybe err
>                        (p . renameStatesBy f . syntacticMonoid .
>                         normalize . desemantify) $
>                        makeAutomaton (dict, subexprs, Just expr)) >>
>                       return e
>         ErrorMsg str -> hPutStr stderr str >> return e
>         Import file -> catchIOError (importScript e =<< lines <$> readFile file)
>                        (const $
>                            (hPutStrLn stderr
>                             ("failed to read \"" ++ file ++ "\"") >>
>                             return e))
>         Loadstate file -> catchIOError (read <$> readFile file)
>                           (const $
>                            (hPutStrLn stderr
>                             ("failed to read \"" ++ file ++ "\"") >>
>                             return e))
>         Read file -> catchIOError (doStatements e <$> readFile file)
>                      (const $ hPutStrLn stderr
>                       ("failed to read \"" ++ file ++ "\"") >>
>                       return e)
>         ReadBin file -> catchIOError (maybe
>                                       ((hPutStrLn stderr
>                                         "input not a binary automaton, environment unchanged" >>
>                                         return e))
>                                       (return . insertExpr e . fromSemanticAutomaton) =<<
>                                       readMaybe <$> readFile file)
>                         (const $ hPutStrLn stderr
>                          ("failed to read \"" ++ file ++ "\"") >>
>                          return e)
>         ReadJeff file -> catchIOError (either
>                                        (const
>                                         (hPutStrLn stderr
>                                          "input not a Jeff, environment unchanged" >>
>                                          return e))
>                                        (return . insertExpr e . fromAutomaton) =<<
>                                        fromE Jeff <$> readFile file)
>                          (const $ hPutStrLn stderr
>                           ("failed to read \"" ++ file ++ "\"") >>
>                           return e)
>         Reset -> return (empty, empty, Nothing)
>         --
>         -- Note: RestoreUniverse is implemented in a probably-inefficient
>         --       way, by making use of the side-effect that all assignments
>         --       properly update the universe.  The code currently just
>         --       rebinds every bound variable by creating and evaluating
>         --       assignment statements.  This should be done differently.
>         --
>         RestoreUniverse -> let d' = keep ((/= "universe") . fst) dict
>                            in return . doStatements (d', subexprs, last) .
>                               unlines . fromCollapsible $
>                               union
>                               (tmap
>                                (\(a, _) -> "= " ++ a ++ " { " ++ a ++ " } ") $
>                                d')
>                               (tmap
>                                (\(a, _) -> "= " ++ a ++ " " ++ a) subexprs)
>         RestrictUniverse -> return (restrictUniverse e)
>         Savestate file -> catchIOError (writeFile file . unlines $ [show e])
>                           (const $ hPutStrLn stderr
>                            ("failed to write \"" ++ file ++ "\"")
>                           ) >> return e
>         Show name  -> (mapM_
>                        (\(_,a) ->
>                         putStrLn (name ++ " <- " ++ show a)) $
>                        keep ((== name) . fst) subexprs) >>
>                       (mapM_
>                        (\(_,s) ->
>                         putStrLn (name ++ " <- " ++ deescape (formatSet s))) $
>                        keep ((== name) . fst) dict) >>
>                       return e
>         Unset name -> return ( keep ((/= name) . fst) dict
>                              , keep ((/= name) . fst) subexprs
>                              , if name == "it"
>                                then Nothing
>                                else last)
>         Write file expr -> let aut = makeAutomaton $
>                                      insertExpr (empty, empty, Nothing) expr
>                            in maybe
>                               (hPutStrLn stderr "could not make automaton")
>                               (\a ->
>                                catchIOError (writeFile file . unlines $ [show a])
>                                (const $ hPutStrLn stderr
>                                 ("failed to write \"" ++ file ++ "\"")
>                                )) aut >>
>                               return e
>       where err = hPutStrLn stderr "could not parse expression"
>             f (_, xs) = '<' : f' xs ++ ">"
>             f' [] = ""
>             f' (a:[]) = f'' a
>             f' (a:as) = f'' a ++ " " ++ f' as
>             f'' Epsilon = "ε"
>             f'' (Symbol x) = x
>             p :: (Ord n, Ord e, Show n, Show e) => FSA n e -> IO ()
>             p = putStr . to Dot

> doRelation :: Env -> Relation -> Maybe Bool
> doRelation e r = case r of
>                    Equal p1 p2    ->  relate e (==) p1 p2
>                    IsPT p         ->  isPT <$> normalize <$> desemantify <$>
>                                       makeAutomaton (e' p)
>                    IsSL p         ->  isSL <$> normalize <$> desemantify <$>
>                                       makeAutomaton (e' p)
>                    IsSP p         ->  isSP <$> normalize <$> desemantify <$>
>                                       makeAutomaton (e' p)
>                    Subset p1 p2   ->  relate e isSupersetOf p1 p2
>                    SSubset p1 p2  ->  relate e isProperSupersetOf p1 p2
>     where e' p = (\(a, b, _) -> (a, b, Just p)) e
>           isPT f = let m = syntacticMonoid f
>                    in renameStates m `asTypeOf` f ==
>                       renameStates (minimizeOver jEquivalence m)

> relate :: Env
>        -> (FSA Integer String -> FSA Integer String -> a) -> Expr -> Expr
>        -> Maybe a
> relate (a,b,_) f p1 p2 = f' <$> makeAutomaton e1 <*> makeAutomaton e2
>     where e1 = (a, b, Just p1)
>           e2 = (a, b, Just p2)
>           f' x y = let ss = collapse (maybe id insert) empty $
>                             union (alphabet x) (alphabet y)
>                    in f (desemantify $ semanticallyExtendAlphabetTo ss x)
>                         (desemantify $ semanticallyExtendAlphabetTo ss y)

> act :: Env -> Trither Command Relation Env -> IO Env
> act d = trither
>         (doCommand d)
>         (\r -> maybe err print (doRelation d r) >> return d)
>         return
>     where err = hPutStrLn stderr "could not parse relation"

> importScript :: Env -> [String] -> IO Env
> importScript e [] = return e
> importScript e (a:as) = flip importScript as =<<
>                         act e (processLine e a)



> deescape :: String -> String
> deescape ('\\' : '&' : xs) = deescape xs
> deescape ('\\' : x : xs)
>     | isEmpty digits = x : deescape xs
>     | otherwise      = toEnum (read digits) : deescape others
>     where (digits, others) = span (isIn "0123456789") (x:xs)
> deescape (x:xs) = x : deescape xs
> deescape _      = []

> display :: (Ord n, Ord e, Show n, Show e) => FSA n e -> IO ()
> display fsa = do
>   let dotP     = (proc "dot" ["-Tpng"]) {
>                    std_in = CreatePipe
>                  , std_out = CreatePipe
>                  , std_err = NoStream
>                  }
>   (Just std_in, Just pipe, _, dot_ph) <- createProcess dotP
>   hSetBinaryMode pipe True
>   let displayP = (proc "display" []) {
>                    std_in = UseHandle pipe
>                  , std_out = NoStream
>                  , std_err = NoStream
>                  }
>   createProcess displayP
>   hPutStr std_in (to Dot fsa)
>   hClose std_in
>   waitForProcess dot_ph
>   return ()

> isPrefixOf :: (Eq a) => [a] -> [a] -> Bool
> isPrefixOf _ []  =  True
> isPrefixOf [] _  =  False
> isPrefixOf (x:xs) (y:ys)
>     | x == y     =  isPrefixOf xs ys
>     | otherwise  =  False

> trither :: (a -> d) -> (b -> d) -> (c -> d) -> Trither a b c -> d
> trither f g h t = case t of
>                     L a -> f a
>                     M b -> g b
>                     R c -> h c

> readMaybe :: (Read a) => String -> Maybe a
> readMaybe s = case reads s of
>               [(x, as)] -> if all isSpace as then Just x else Nothing
>               _ -> Nothing
