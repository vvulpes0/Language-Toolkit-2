> module Main where

> import FSA
> import Pleb ( Env, Expr
>             , doParse, doStatements, makeAutomaton, parseExpr, tokenize)
> import Porters

> import Control.Applicative (Applicative(..))
> import Control.Monad.Trans.Class (lift)
> import Data.Functor ((<$>))
> import System.Console.Haskeline ( InputT
>                                 , defaultSettings
>                                 , getInputLine
>                                 , runInputT
>                                 )
> import System.IO
> import System.IO.Error
> import System.Process

> main = runInputT defaultSettings (processLines (empty, empty, Nothing))

> prompt :: String
> prompt = "> "

> data Trither a b c = L a
>                    | M b
>                    | R c
>                      deriving (Eq, Ord, Read, Show)
> data Command = Bindings
>              | Display Expr
>              | Dotify Expr
>              | ErrorMsg String
>              | Read FilePath
>              | Reset
>              | Unset String
>              deriving (Eq, Read, Show)
> data Relation = Equal Expr Expr
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
>     | isPrefixOf str ":read"     =  case words str of
>                                       (_:a:[]) -> L (Read a)
>                                       _        -> R d
>     | isPrefixOf str ":unset"    =  case words str of
>                                       (_:a:[]) -> L (Unset a)
>                                       _        -> R d
>     | otherwise                  =  doOne $
>                                     filter (isPrefixOf str . fst) commands
>     where pe        =  parseExpr dict subexprs
>           p2e       =  (,) <$> pe <*> pe
>           f (s, p)  =  either (const (L err)) fst .
>                        doParse p $ tokenize (drop (length s) str)
>           commands  =  [ (":bindings",       pure (L Bindings))
>                        , (":display",        ((L .         Display) <$> pe ))
>                        , (":dot",            ((L .         Dotify ) <$> pe ))
>                        , (":equal",          ((M . uncurry Equal  ) <$> p2e))
>                        , (":implies",        ((M . uncurry Subset ) <$> p2e))
>                        , (":reset",          pure (L Reset))
>                        , (":strict-subset",  ((M . uncurry SSubset) <$> p2e))
>                        , (":subset",         ((M . uncurry Subset ) <$> p2e))
>                        ]
>           doOne xs  = case xs of
>                         (x:[]) -> f x
>                         _      -> L (ErrorMsg "unknown interpreter command")
>           err = ErrorMsg "failed to evaluate"

> doCommand :: Env -> Command -> IO Env
> doCommand e@(dict, subexprs, last) c
>     = case c of
>         Bindings -> do
>                putStrLn "# Symbol aliases:"
>                mapM_ (\(n, s) ->
>                       putStrLn (n ++ " <- " ++ formatSet s)
>                      ) dict
>                putStrLn "# Expression aliases:"
>                putStrLn (formatSet $ tmap fst subexprs)
>                return e
>         Display expr -> (maybe err display $
>                          makeAutomaton (dict, subexprs, Just expr)) >>
>                         return e
>         Dotify expr -> (maybe err (putStr . to Dot) $
>                         makeAutomaton (dict, subexprs, Just expr)) >>
>                        return e
>         ErrorMsg str -> hPutStrLn stderr str >> return e
>         Read file -> catchIOError (doStatements e <$> readFile file)
>                      (const $ hPutStrLn stderr
>                       ("failed to read \"" ++ file ++ "\"") >>
>                       return e)
>         Reset -> return (empty, empty, Nothing)
>         Unset name -> return ( keep ((/= name) . fst) dict
>                              , keep ((/= name) . fst) subexprs
>                              , if name == "it"
>                                then Nothing
>                                else last)
>       where err = hPutStrLn stderr "could not parse expression"

> doRelation :: Env -> Relation -> Maybe Bool
> doRelation e r = case r of
>                    Equal p1 p2    ->  relate e (==) p1 p2
>                    Subset p1 p2   ->  relate e isSupersetOf p1 p2
>                    SSubset p1 p2  ->  relate e isProperSupersetOf p1 p2

> relate :: Env
>        -> (FSA Integer String -> FSA Integer String -> a) -> Expr -> Expr
>        -> Maybe a
> relate (a,b,_) f p1 p2 = f <$> makeAutomaton e1 <*> makeAutomaton e2
>     where e1 = (a, b, Just p1)
>           e2 = (a, b, Just p2)

> act :: Env -> Trither Command Relation Env -> IO Env
> act d = trither
>         (doCommand d)
>         (\r -> maybe err print (doRelation d r) >> return d)
>         return
>     where err = hPutStrLn stderr "could not parse relation"



> display :: (Ord n, Ord e, Show n, Show e) => FSA n e -> IO ()
> display fsa = do
>   (readEnd, writeEnd) <- createPipe
>   hSetBinaryMode readEnd True
>   hSetBinaryMode writeEnd True
>   let displayP = (proc "display" []) {
>                    std_in = UseHandle readEnd
>                  , std_out = NoStream
>                  , std_err = NoStream
>                  }
>       dotP     = (proc "dot" ["-Tpng"]) {
>                    std_in = CreatePipe
>                  , std_out = UseHandle writeEnd
>                  , std_err = NoStream
>                  }
>   (Just std_in, _, _, dot_ph) <- createProcess dotP
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
