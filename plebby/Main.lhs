> {-# Language CPP #-}

#if !defined(MIN_VERSION_base)
# define MIN_VERSION_base(a,b,c) 0
#endif

> module Main where

> import LTK.FSA
> import LTK.Porters.Pleb ( Env
>                         , Expr
>                         , compileEnv
>                         , doParse
>                         , doStatements
>                         , fromAutomaton
>                         , fromSemanticAutomaton
>                         , groundEnv
>                         , insertExpr
>                         , makeAutomaton
>                         , parseExpr
>                         , restrictUniverse
>                         , tokenize
>                         )
> import LTK.Porters.ATT  ( embedSymbolsATT, extractSymbolsATT )
> import LTK.Porters      ( ATT(ATT), ATTO(ATTO), Dot(Dot), Jeff(Jeff)
>                         , formatSet, fromE, to)
> import LTK.Decide       ( isSL, isTSL
>                         , isLT, isTLT
>                         , isLTT, isTLTT
>                         , isSP
>                         , isPT
>                         , isSF)

> import Control.Applicative ((<*>), pure)
> import Control.Monad.Trans.Class ( lift )
> import Data.Char (isSpace, toLower)
> import Data.Functor ((<$>))
> import System.Console.Haskeline ( InputT
>                                 , defaultSettings
>                                 , getInputLine
>                                 , runInputT
>                                 )
> import System.Environment (getEnvironment)
> import System.IO ( hClose
>                  , hGetContents
>                  , hPutStr
>                  , hPutStrLn
>                  , hSetBinaryMode
>                  , stderr
>                  , stdout
>                  )

#if MIN_VERSION_base(4,4,0)

> import System.IO.Error ( catchIOError )

# else
Older versions of base used catch instead of catchIOError.
The types are consistent, so it is enough to define a synonym here.

> import System.IO.Error ( IOError, catch )
> catchIOError :: IO a -> (IOError -> IO a) -> IO a
> catchIOError = catch

# endif

> import System.Process ( CreateProcess(std_err, std_in, std_out)
>                       , StdStream(CreatePipe, UseHandle)
>                       , createProcess
>                       , proc
>                       , waitForProcess
>                       )

> main :: IO ()
> main = runInputT defaultSettings (processLines (empty, empty, Nothing))

> prompt :: String
> prompt = "> "

> data Trither a b c = L a
>                    | M b
>                    | R c
>                      deriving (Eq, Ord, Read, Show)
> data ArgType = ArgE
>              | ArgF
>              | ArgV
>                deriving (Eq, Ord, Read, Show)
> data Command = Bindings
>              | D_PSG Expr -- Display Powerset Graph
>              | D_SM Expr -- Display Syntactic Monoid
>              | Display Expr
>              | Dotify Expr
>              | DT_PSG Expr -- Dotify Powerset Graph
>              | DT_SM Expr -- Dotify Syntactic Monoid
>              | ErrorMsg String
>              | Help [(String, [ArgType], String)]
>              | Import FilePath
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
>              deriving (Eq, Read, Show)
> data Relation = Equal Expr Expr
>               | IsLT Expr
>               | IsLTT Expr
>               | IsPT Expr
>               | IsSF Expr
>               | IsSL Expr
>               | IsSP Expr
>               | IsTLT Expr
>               | IsTLTT Expr
>               | IsTSL Expr
>               | Subset Expr Expr
>               | SSubset Expr Expr -- Strict Subset
>                 deriving (Eq, Read, Show)

> processLines :: Env -> InputT IO ()
> processLines e = do
>   minput <- getInputLine prompt
>   case minput of
>     Nothing -> return ()
>     Just ":quit" -> return ()
>     Just line -> lift (act e (processLine e line)) >>= processLines

> processLine :: Env -> String -> Trither Command Relation Env
> processLine d@(dict, subexprs, _) str
>     | null str                    =  R d
>     | not (isPrefixOf str ":")    =  R $ doStatements d str
>     | isStartOf str ":import"     = case words str of
>                                       (_:a:[]) -> L (Import a)
>                                       _        -> R d
>     | isStartOf str ":loadstate"  = case words str of
>                                       (_:a:[]) -> L (Loadstate a)
>                                       _        -> R d
>     | isStartOf str ":readatto"   =  case words str of
>                                        (_:a:b:c:[]) -> L (ReadATTO a b c)
>                                        _            -> R d
>     | isStartOf str ":readatt"    =  case words str of
>                                        (_:a:b:c:[]) -> L (ReadATT a b c)
>                                        _            -> R d
>     | isStartOf str ":readbin"    =  case words str of
>                                        (_:a:[]) -> L (ReadBin a)
>                                        _        -> R d
>     | isStartOf str ":readjeff"   =  case words str of
>                                        (_:a:[]) -> L (ReadJeff a)
>                                        _        -> R d
>     | isStartOf str ":read"       =  case words str of
>                                        (_:a:[]) -> L (Read a)
>                                        _        -> R d
>     | isStartOf str ":savestate"  =  case words str of
>                                        (_:a:[]) -> L (Savestate a)
>                                        _        -> R d
>     | isStartOf str ":show"       =  case words str of
>                                        (_:a:as) -> L (Show (unwords (a:as)))
>                                        _        -> R d
>     | isStartOf str ":unset"      =  case words str of
>                                        (_:a:[]) -> L (Unset a)
>                                        _        -> R d
>     | isStartOf str ":writeatt"   =  case words str of
>                                        (_:a:b:c:as) -> g ((L .
>                                                            WriteATT a b c)
>                                                          <$> pe)
>                                                        (unwords as)
>                                        _            -> R d
>     | isStartOf str ":write"      =  case words str of
>                                        (_:a:as) -> g ((L . Write a) <$> pe)
>                                                    (unwords as)
>                                        _        -> R d
>     | otherwise                   =  doOne .
>                                      filter (isStartOf str . fst) $
>                                      p12 commands
>     where pe        =  parseExpr dict subexprs
>           p2e       =  (,) <$> pe <*> pe
>           f (s, p)  =  g p (drop (length s) str)
>           g p x     =  either (L . err) fst . doParse p $ tokenize x
>           p12       =  map (\(a,b,_,_) -> (a,b))
>           p134      =  map (\(w,_,y,z) -> (w,y,z))
>           commands
>               =  [ ( ":bindings",       pure (L Bindings)
>                    , [], "print list of variables and their bindings")
>                  , ( ":compile",        pure (R $ compileEnv d)
>                    , [], "convert all expr variables to automata")
>                  , ( ":display",        ((L .         Display) <$> pe )
>                    , [ArgE]
>                    , "show expr graphically via external display program")
>                  , ( ":dot-psg",        ((L .         DT_PSG ) <$> pe )
>                    , [ArgE], ":dot the powerset graph of expr")
>                  , ( ":dot-synmon",     ((L .         DT_SM  ) <$> pe )
>                    , [ArgE], ":dot the syntactic monoid of expr")
>                  , ( ":dot",            ((L .         Dotify ) <$> pe )
>                    , [ArgE], "print a Dot file of expr")
>                  , ( ":equal",          ((M . uncurry Equal  ) <$> p2e)
>                    , [ArgE, ArgE], "compare two exprs for set-equality")
>                  , ( ":ground",         pure (R $ groundEnv d)
>                    , [], "convert all expr variables to grounded automata")
>                  , ( ":help",           pure (L . Help $ p134 commands)
>                    , [], "print this help")
>                  , ( ":implies",        ((M . uncurry Subset ) <$> p2e)
>                    , [ArgE, ArgE], "determine if expr1 implies expr2")
>                  , ( ":import",         error ":import not defined here"
>                    , [ArgF], "read file as plebby script")
>                  , ( ":isLT",           ((M .         IsLT   ) <$> pe )
>                    , [ArgE], "determine if expr is Locally Testable")
>                  , ( ":isLTT",          ((M .         IsLTT  ) <$> pe )
>                    , [ArgE]
>                    , "determine if expr is Locally Threshold Testable")
>                  , ( ":isPT",           ((M .         IsPT   ) <$> pe )
>                    , [ArgE], "determine if expr is Piecewise Testable")
>                  , ( ":isSF",           ((M .         IsSF   ) <$> pe )
>                    , [ArgE], "determine if expr is Star-Free")
>                  , ( ":isSL",           ((M .         IsSL   ) <$> pe )
>                    , [ArgE], "determine if expr is Strictly Local")
>                  , ( ":isSP",           ((M .         IsSP   ) <$> pe )
>                    , [ArgE], "determine if expr is Strictly Piecewise")
>                  , ( ":isTLT",          ((M .         IsTLT  ) <$> pe )
>                    , [ArgE], "determine if expr is Tier-Locally Testable")
>                  , ( ":isTLTT",         ((M .         IsTLTT ) <$> pe )
>                    , [ArgE], "determine if expr is Tier-LTT")
>                  , ( ":isTSL",          ((M .         IsTSL  ) <$> pe )
>                    , [ArgE], "determine if expr is Strictly Tier-Local")
>                  , ( ":loadstate",      error ":loadstate not defined here"
>                    , [ArgF], "restore state from file")
>                  , ( ":psg",            ((L .         D_PSG  ) <$> pe )
>                    , [ArgE], ":display the powerset graph of expr")
>                  , ( ":quit",           error ":quit not defined here"
>                    , [], "exit plebby")
>                  , ( ":readATT",        error ":readatt not defined here"
>                    , [ArgF, ArgF, ArgF]
>                    , "read AT&T files, bind input-projection to 'it'")
>                  , ( ":readATTO",        error ":readatto not defined here"
>                    , [ArgF, ArgF, ArgF]
>                    , "read AT&T files, bind output-projection to 'it'")
>                  , ( ":readBin",        error ":readbin not defined here"
>                    , [ArgF], "read binary expr from file, bind to 'it'")
>                  , ( ":readJeff",       error ":readjeff not defined here"
>                    , [ArgF], "read Jeff format automaton file, bind to 'it'")
>                  , ( ":read",           error ":read not defined here"
>                    , [ArgF], "read Pleb file")
>                  , ( ":reset",          pure (L Reset)
>                    , [], "purge the current environment")
>                  , ( ":restore-universe", pure (L RestoreUniverse)
>                    , [], "set universe to all and only necessary symbols")
>                  , ( ":restrict",       pure (L RestrictUniverse)
>                    , [], "remove non-universe symbols from the environment")
>                  , ( ":savestate",      error ":savestate not defined here"
>                    , [ArgF], "write current state to file")
>                  , ( ":show",           error ":show not defined here"
>                    , [ArgV], "print meaning(s) of var")
>                  , ( ":strict-subset",  ((M . uncurry SSubset) <$> p2e)
>                    , [ArgE, ArgE]
>                    , "determine if expr1 is a strict subset of expr2")
>                  , ( ":subset",         ((M . uncurry Subset ) <$> p2e)
>                    , [ArgE, ArgE], "determine if expr1 is a subset of expr2")
>                  , ( ":synmon",         ((L .         D_SM   ) <$> pe )
>                    , [ArgE], ":display the syntactic monoid of expr")
>                  , ( ":unset",          error ":unset not defined here"
>                    , [ArgV], "remove a single var from the environment")
>                  , ( ":writeatt",       error ":writeatt not defined here"
>                    , [ArgF, ArgF, ArgF, ArgE]
>                    , "write AT&T form of expr to files (edges, ins, outs)")
>                  , ( ":write",          error ":write not defined here"
>                    , [ArgF, ArgE], "write binary form of expr to file")
>                  ]
>           doOne xs  = case xs of
>                         (x:_)  ->  f x
>                         _      ->  L (ErrorMsg "unknown interpreter command\n")
>           err x = ErrorMsg x -- "failed to evaluate"
>           isStartOf xs x = ((isPrefixOf (map toLower xs) (map toLower x)) &&
>                             (all isSpace . take 1 $
>                              drop (length x) xs))

> doCommand :: Env -> Command -> IO Env
> doCommand e@(dict, subexprs, ex) c
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
>         Help xs -> lessHelp xs >> return e
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
>         ReadATT f1 f2 f3 -> ratt f1 f2 f3 ATT
>         ReadATTO f1 f2 f3 -> ratt f1 f2 f3 ATTO
>         ReadBin file
>             -> catchIOError
>                (maybe
>                 ((hPutStrLn stderr
>                   "input not a binary automaton, environment unchanged" >>
>                   return e))
>                 (return . insertExpr e . fromSemanticAutomaton) =<<
>                 readMaybe <$> readFile file)
>                (const $ hPutStrLn stderr
>                 ("failed to read \"" ++ file ++ "\"") >>
>                 return e)
>         ReadJeff file
>             -> catchIOError
>                (either
>                 (const
>                  (hPutStrLn stderr
>                   "input not a Jeff, environment unchanged" >>
>                   return e))
>                 (return . insertExpr e . fromAutomaton) =<<
>                 fromE Jeff <$> readFile file)
>                (const $ hPutStrLn stderr
>                 ("failed to read \"" ++ file ++ "\"") >>
>                 return e)
>         Reset -> return (empty, empty, Nothing)
>         --
>         -- Note: RestoreUniverse is implemented in a probably-inefficient
>         --       way, by making use of the side-effect that all assignments
>         --       properly update the universe.  The code currently just
>         --       rebinds every bound variable by creating and evaluating
>         --       assignment statements.  This should be done differently.
>         --
>         RestoreUniverse -> let d' = keep ((/= "universe") . fst) dict
>                            in return . doStatements (d', subexprs, ex) .
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
>         Show name
>             -> if (isNotIn (tmap fst subexprs) name &&
>                    isNotIn (tmap fst dict) name)
>                then (putStrLn ("undefined variable \"" ++ name ++ "\"") >>
>                      return e)
>                else ((mapM_
>                       (\(_,a) ->
>                        putStrLn (name ++ " <- " ++ show a)) $
>                       keep ((== name) . fst) subexprs) >>
>                      (mapM_
>                       (\(_,s) ->
>                        putStrLn (name ++ " <- " ++ deescape (formatSet s))) $
>                       keep ((== name) . fst) dict) >>
>                      return e)
>         Unset name -> return ( keep ((/= name) . fst) dict
>                              , keep ((/= name) . fst) subexprs
>                              , if name == "it"
>                                then Nothing
>                                else ex)
>         Write file expr
>             -> let aut = makeAutomaton $
>                          insertExpr e expr
>                in (maybe (hPutStrLn stderr "could not make automaton")
>                    (\a -> werr file (unlines $ [show a]))
>                    aut >>
>                    return e)
>         WriteATT f1 f2 f3 expr
>             -> let aut = fmap desemantify . makeAutomaton $
>                          insertExpr e expr
>                    w2  = if f2 == "_" then const (return ()) else werr f2
>                    w3  = if f3 == "_" then const (return ()) else werr f3
>                in (maybe (hPutStrLn stderr "could not make automaton")
>                    (\a ->
>                     let (ts, i, o) = extractSymbolsATT $ to ATT a
>                     in werr f1 ts >> w2 i >> w3 o)
>                    aut >>
>                    return e)
>       where err = hPutStrLn stderr "could not parse expression"
>             f (_, xs) = '<' : f' xs ++ ">"
>             f' [] = ""
>             f' (a:[]) = f'' a
>             f' (a:as) = f'' a ++ " " ++ f' as
>             f'' Epsilon = "ε"
>             f'' (Symbol x) = x
>             p :: (Ord n, Ord e, Show n, Show e) => FSA n e -> IO ()
>             p = putStr . to Dot
>             werr ofile s = catchIOError (writeFile ofile s)
>                            (const $ hPutStrLn stderr
>                             ("failed to write \"" ++ ofile ++
>                              if (isIn ofile '/')
>                              then "\nDoes the directory exist?"
>                              else ""))
>             ratt f1 f2 f3 typ
>                 = catchIOError
>                   (either
>                    (const
>                     (hPutStrLn stderr
>                      "input not an ATT file, environment unchanged" >>
>                      return e))
>                    (return . insertExpr e . fromAutomaton) =<<
>                    fromE typ <$>
>                    (embedSymbolsATT                                       <$>
>                     readFile f1                                           <*>
>                     (if f2 == "_" then mempty else Just <$> readFile f2)  <*>
>                     (if f3 == "_" then mempty else Just <$> readFile f3)))
>                   (const $ hPutStrLn stderr
>                    ("failed to read input files") >>
>                    return e)


> doHelp :: [(String, [ArgType], String)] -> String
> doHelp xs = showArg ArgE ++ " = expression, "  ++
>             showArg ArgF ++ " = file, "        ++
>             showArg ArgV ++ " = variable\n\n"  ++
>             unlines s2
>     where cs = zipWith (\a b -> a ++ b) (p1 xs) (map showArgs (p2 xs))
>           s1 = let l = foldr max 0 $ map length cs
>                in map (alignl (l + 2) . alignr l) cs
>           s2 = zipWith (++) s1 (p3 xs)
>           alignr l s = take (l - length s) (cycle " ") ++ s
>           alignl l s = take l (s ++ cycle " ")
>           showArg ArgE  =  "<e>"
>           showArg ArgF  =  "<f>"
>           showArg _     =  "<v>"
>           showArgs []      =  ""
>           showArgs (y:ys)  =  " " ++ showArg y ++ showArgs' ys
>               where showArgs' []      =  ""
>                     showArgs' (z:zs)  =  " " ++ showArg z ++ showArgs' zs
>           p1       = map (\(a,_,_) -> a)
>           p2       = map (\(_,b,_) -> b)
>           p3       = map (\(_,_,c) -> c)

> lessHelp :: [(String, [ArgType], String)] -> IO ()
> lessHelp xs = do
>   mpager <- fmap (map snd . filter ((==) "PAGER" . fst)) getEnvironment
>   let ps     = words $ head (mpager ++ ["less"])
>   let (p:s)  = if null ps then ["less"] else ps
>   let lessP  = (proc p s) {
>                  std_in = CreatePipe
>                , std_out = UseHandle stdout
>                , std_err = CreatePipe
>                }
>   (Just p_stdin, _, Just p_stderr, less_ph) <- createProcess lessP
>   _ <- hGetContents p_stderr
>   hPutStr p_stdin (doHelp xs)
>   hClose p_stdin
>   _ <- waitForProcess less_ph
>   return ()

> doRelation :: Env -> Relation -> Maybe Bool
> doRelation e r = case r of
>                    Equal p1 p2    ->  relate e (==) p1 p2
>                    IsLT p         ->  isLT <$> normalize <$> desemantify <$>
>                                       makeAutomaton (e' p)
>                    IsLTT p        ->  isLTT <$> normalize <$> desemantify <$>
>                                       makeAutomaton (e' p)
>                    IsPT p         ->  isPT <$> normalize <$> desemantify <$>
>                                       makeAutomaton (e' p)
>                    IsSF p         ->  isSF <$> normalize <$> desemantify <$>
>                                       makeAutomaton (e' p)
>                    IsSL p         ->  isSL <$> normalize <$> desemantify <$>
>                                       makeAutomaton (e' p)
>                    IsSP p         ->  isSP <$> normalize <$> desemantify <$>
>                                       makeAutomaton (e' p)
>                    IsTLT p        ->  isTLT <$> normalize <$> desemantify <$>
>                                       makeAutomaton (e' p)
>                    IsTLTT p       ->  isTLTT <$> normalize <$>
>                                       desemantify <$> makeAutomaton (e' p)
>                    IsTSL p        ->  isTSL <$> normalize <$> desemantify <$>
>                                       makeAutomaton (e' p)
>                    Subset p1 p2   ->  relate e isSupersetOf p1 p2
>                    SSubset p1 p2  ->  relate e isProperSupersetOf p1 p2
>     where e' p = (\(a, b, _) -> (a, b, Just p)) e

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
>                  , std_err = CreatePipe
>                  }
>   (Just p_stdin, Just pipe, Just p_stderr, dot_ph) <- createProcess dotP
>   _ <- hGetContents p_stderr
>   hSetBinaryMode pipe True
>   let displayP = (proc "display" []) {
>                    std_in = UseHandle pipe
>                  , std_out = CreatePipe
>                  , std_err = CreatePipe
>                  }
>   (_, Just d_stdout, Just d_stderr, _)  <- createProcess displayP
>   _ <- hGetContents d_stdout
>   _ <- hGetContents d_stderr
>   hPutStr p_stdin (to Dot fsa)
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
> trither f g h t = case t of
>                     L a -> f a
>                     M b -> g b
>                     R c -> h c

> readMaybe :: (Read a) => String -> Maybe a
> readMaybe s = case reads s of
>               [(x, as)] -> if all isSpace as then Just x else Nothing
>               _ -> Nothing
