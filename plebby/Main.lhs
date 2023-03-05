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
> import Data.List (intercalate)
> import System.Console.Haskeline ( InputT
>                                 , defaultSettings
>                                 , getInputLine
>                                 , runInputT
>                                 )
> import System.Environment (getEnvironment)
> import System.Directory ( createDirectoryIfMissing
>                         , getHomeDirectory
>                         )
> import System.FilePath ( isPathSeparator
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
#if MIN_VERSION_base(4,4,0)
> import System.IO.Error (catchIOError)
#else
> import System.IO.Error (IOError, catch) -- We'll make our own
#endif

> import LTK.Decide       ( isSL, isTSL
>                         , isLT, isTLT
>                         , isLTT, isTLTT
>                         , isLPT, isTLPT
>                         , isSP
>                         , isPT
>                         , isFO2, isFO2B, isFO2BF, isFO2S
>                         , isSF
>                         , isGLT, isGLPT
>                         , isFinite
>                         , isGD
>                         , isTGD
>                         , isCB
>                         , isAcom, isLAcom, isTLAcom
>                         , isB, isLB, isTLB
>                         , isDef
>                         , isRDef
>                         , isTDef
>                         , isTRDef
>                         , isTrivial
>                         , isMTF, isMTDef, isMTRDef, isMTGD
>                         )
> import LTK.FSA
> import LTK.Learn.SL  (fSL)
> import LTK.Learn.SP  (fSP)
> import LTK.Learn.TSL (fTSL)
> import LTK.Learn.StringExt (Grammar(..), learn)
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
>                         , fromAutomaton
>                         , fromSemanticAutomaton
>                         , groundEnv
>                         , insertExpr
>                         , makeAutomaton
>                         , parseExpr
>                         , restrictUniverse
>                         , tokenize
>                         )


#if !MIN_VERSION_base(4,4,0)
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
> main = runInputT defaultSettings $ processLines (empty, empty, Nothing)

> prompt :: String
> prompt = "> "

> data Trither a b c = L a
>                    | M b
>                    | R c
>                      deriving (Eq, Ord, Read, Show)

> data ArgType = ArgE
>              | ArgF
>              | ArgI
>              | ArgV
>                deriving (Eq, Ord, Read, Show)

> data Command = Bindings
>              | D_EB Expr -- Display EggBox
>              | D_JE Expr -- Display J-minimized Form
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
>               | Subset Expr Expr
>               | SSubset Expr Expr -- Strict Subset
>                 deriving (Eq, Read, Show)

> processLines :: Env -> InputT IO ()
> processLines e = f =<< getInputLine prompt
>     where f minput
>               = case minput
>                 of Nothing       ->  return ()
>                    Just ":quit"  ->  return ()
>                    Just line     ->  lift (act e (processLine e line)) >>=
>                                      processLines

Always use "modwords" when FilePath objects are at issue,
so that file names can be quoted or escaped
in order to deal with spaces or other special characters.

> processLine :: Env -> String -> Trither Command Relation Env
> processLine d@(dict, subexprs, _) str
>     | null str = R d
>     | not (isPrefixOf str ":") = R $ doStatements d str
>     | isStartOf str ":import"
>         = case modwords str
>           of (_:a:[])  ->  L (Import a)
>              _         ->  R d
>     | isStartOf str ":learnsl"
>         = case modwords str
>           of (_:a:b:[])  ->  if all (isIn "0123456789") a
>                              then L (LearnSL (read a) b)
>                              else R d
>              _           ->  R d
>     | isStartOf str ":learnsp"
>         = case modwords str
>           of (_:a:b:[])  ->  if all (isIn "0123456789") a
>                              then L (LearnSP (read a) b)
>                              else R d
>              _           ->  R d
>     | isStartOf str ":learntsl"
>         = case modwords str
>           of (_:a:b:[])  ->  if all (isIn "0123456789") a
>                              then L (LearnTSL (read a) b)
>                              else R d
>              _           ->  R d
>     | isStartOf str ":loadstate"
>         = case modwords str
>           of (_:a:[])  ->  L (Loadstate a)
>              _         ->  R d
>     | isStartOf str ":readatto"
>         = case modwords str
>           of (_:a:b:c:[])  ->  L (ReadATTO a b c)
>              _             ->  R d
>     | isStartOf str ":readatt"
>         = case modwords str
>           of (_:a:b:c:[])  ->  L (ReadATT a b c)
>              _             ->  R d
>     | isStartOf str ":readbin"
>         = case modwords str
>           of (_:a:[])  ->  L (ReadBin a)
>              _         ->  R d
>     | isStartOf str ":readjeff"
>         = case modwords str
>           of (_:a:[])  ->  L (ReadJeff a)
>              _         ->  R d
>     | isStartOf str ":read"
>         = case modwords str
>           of (_:a:[])  ->  L (Read a)
>              _         ->  R d
>     | isStartOf str ":savestate"
>         = case modwords str
>           of (_:a:[])  ->  L (Savestate a)
>              _         ->  R d
>     | isStartOf str ":show"
>         = case words str
>           of (_:a:as) -> L (Show (unwords (a:as)))
>              _        -> R d
>     | isStartOf str ":unset"
>         = case words str of
>             (_:a:[]) -> L (Unset a)
>             _        -> R d
>     | isStartOf str ":writeatt"
>         =  case modwords str
>            of (_:a:b:c:as) -> g ((L . WriteATT a b c) <$> pe) (unwords as)
>               _            -> R d
>     | isStartOf str ":write"
>         = case modwords str
>           of (_:a:as) -> g ((L . Write a) <$> pe) (unwords as)
>              _        -> R d
>     | otherwise =  doOne . filter (isStartOf str . fst) $ p12 commands
>     where pe        =  parseExpr dict subexprs
>           p2e       =  (,) <$> pe <*> pe
>           f (s, p)  =  g p (drop (length s) str)
>           g p x     =  either (L . err) fst . doParse p $ tokenize x
>           p12       =  map (\(a,b,_,_) -> (a,b))
>           p134      =  map (\(w,_,y,z) -> (w,y,z))
>           doOne xs  =  case xs
>                        of (x:_)  ->  f x
>                           _      ->  L . ErrorMsg $
>                                      "unknown interpreter command\n"
>           err x     =  ErrorMsg x -- "failed to evaluate"
>           isStartOf xs x
>               = (isPrefixOf (map toLower xs) (map toLower x)) &&
>                 (all isSpace . take 1 $ drop (length x) xs)
>           commands
>               = [ ( ":bindings"
>                   , pure $ L Bindings
>                   , []
>                   , "print list of variables and their bindings"
>                   )
>                 , ( ":cequal"
>                   , (M . uncurry CEqual) <$> p2e
>                   , [ArgE, ArgE]
>                   , "compare two exprs for logical equivalence"
>                   )
>                 , ( ":cimplies"
>                   , (M . uncurry CImply) <$> p2e
>                   , [ArgE, ArgE]
>                   , "determine if expr1 logically implies expr2"
>                   )
>                 , ( ":compile"
>                   , pure . R $ compileEnv d
>                   , []
>                   , "convert all expr variables to automata"
>                   )
>                 , ( ":display"
>                   , (L . Display) <$> pe
>                   , [ArgE]
>                   , "show expr graphically via external display program"
>                   )
>                 , ( ":dot-psg"
>                   , (L . DT_PSG) <$> pe
>                   , [ArgE]
>                   , ":dot the powerset graph of expr"
>                   )
>                 , ( ":dot-synmon"
>                   , (L . DT_SM) <$> pe
>                   , [ArgE]
>                   , ":dot the syntactic monoid of expr"
>                   )
>                 , ( ":dot"
>                   , (L . Dotify) <$> pe
>                   , [ArgE]
>                   , "print a Dot file of expr"
>                   )
>                 , ( ":eggbox"
>                   , (L . D_EB) <$> pe
>                   , [ArgE]
>                   , "show egg-box of expr via external display program"
>                   )
>                 , ( ":equal"
>                   , (M . uncurry Equal) <$> p2e
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
>                   , (M . uncurry Subset) <$> p2e
>                   , [ArgE, ArgE]
>                   , "synonym for :subset"
>                   )
>                 , ( ":import"
>                   , error ":import not defined here"
>                   , [ArgF]
>                   , "read file as plebby script"
>                   )
>                 , ( ":isAcom"
>                   , (M . IsAcom) <$> pe
>                   , [ArgE]
>                   , "determine if expr is k,1-LTT"
>                   )
>                 , ( ":isB"
>                   , (M . IsB) <$> pe
>                   , [ArgE]
>                   , "determine if expr is a band"
>                   )
>                 , ( ":isCB"
>                   , (M . IsCB) <$> pe
>                   , [ArgE]
>                   , "determine if expr is a semilattice language"
>                   )
>                 , ( ":isDef"
>                   , (M . IsDef) <$> pe
>                   , [ArgE]
>                   , "determine if expr is a definite language"
>                   )
>                 , ( ":isFinite"
>                   , (M . IsFin) <$> pe
>                   , [ArgE]
>                   , "determine if expr is finite"
>                   )
>                 , ( ":isFO2"
>                   , (M . IsFO2) <$> pe
>                   , [ArgE]
>                   , "determine if expr is FO2[<]-definable"
>                   )
>                 , ( ":isFO2B"
>                   , (M . IsFO2B) <$> pe
>                   , [ArgE]
>                   , "determine if expr is FO2[<,bet]-definable"
>                   )
>                 , ( ":isFO2BF"
>                   , (M . IsFO2BF) <$> pe
>                   , [ArgE]
>                   , "determine if expr is FO2[<,betfac]-definable"
>                   )
>                 , ( ":isFO2S"
>                   , (M . IsFO2S) <$> pe
>                   , [ArgE]
>                   , "determine if expr is FO2[<,+1]-definable"
>                   )
>                 , ( ":isGD"
>                   , (M . IsGD) <$> pe
>                   , [ArgE]
>                   , "determine if expr is Generalized Definite"
>                   )
>                 , ( ":isGLPT"
>                   , (M . IsGLPT) <$> pe
>                   , [ArgE]
>                   , "determine if expr is Generalized Locally PT"
>                   )
>                 , ( ":isGLT"
>                   , (M . IsGLT) <$> pe
>                   , [ArgE]
>                   , "determine if expr is Generalized Locally Testable"
>                   )
>                 , ( ":isLAcom"
>                   , (M . IsLAcom) <$> pe
>                   , [ArgE]
>                   , "determine if expr is locally Acom"
>                   )
>                 , ( ":isLB"
>                   , (M . IsLB) <$> pe
>                   , [ArgE]
>                   , "determine if expr is locally a band"
>                   )
>                 , ( ":isLPT"
>                   , (M . IsLPT) <$> pe
>                   , [ArgE]
>                   , "determine if expr is locally Piecewise Testable"
>                   )
>                 , ( ":isLT"
>                   , (M . IsLT) <$> pe
>                   , [ArgE]
>                   , "determine if expr is Locally Testable"
>                   )
>                 , ( ":isLTT"
>                   , (M . IsLTT) <$> pe
>                   , [ArgE]
>                   , "determine if expr is Locally Threshold Testable"
>                   )
>                 , ( ":isMTDef"
>                   , (M . IsMTDef) <$> pe
>                   , [ArgE]
>                   , "determine if expr is a combination of TDef things"
>                   )
>                 , ( ":isMTF"
>                   , (M . IsMTF) <$> pe
>                   , [ArgE]
>                   , "determine if expr is a combination of tier-(co)finite things"
>                   )
>                 , ( ":isMTGD"
>                   , (M . IsMTGD) <$> pe
>                   , [ArgE]
>                   , "determine if expr is a combination of TGD things"
>                   )
>                 , ( ":isMTRDef"
>                   , (M . IsMTRDef) <$> pe
>                   , [ArgE]
>                   , "determine if expr is a combination of TRDef things"
>                   )
>                 , ( ":isPT"
>                   , (M . IsPT) <$> pe
>                   , [ArgE]
>                   , "determine if expr is Piecewise Testable"
>                   )
>                 , ( ":isRDef"
>                   , (M . IsRDef) <$> pe
>                   , [ArgE]
>                   , "determine if expr is a reverse definite language"
>                   )
>                 , ( ":isSF"
>                   , (M . IsSF) <$> pe
>                   , [ArgE]
>                   , "determine if expr is Star-Free"
>                   )
>                 , ( ":isSL"
>                   , (M . IsSL) <$> pe
>                   , [ArgE]
>                   , "determine if expr is Strictly Local"
>                   )
>                 , ( ":isSP"
>                   , (M . IsSP) <$> pe
>                   , [ArgE]
>                   , "determine if expr is Strictly Piecewise"
>                   )
>                 , ( ":isTDef"
>                   , (M . IsTDef) <$> pe
>                   , [ArgE]
>                   , "determine if expr is definite on a tier"
>                   )
>                 , ( ":isTGD"
>                   , (M . IsTGD) <$> pe
>                   , [ArgE]
>                   , "determine if expr is Generalized Definite on a tier"
>                   )
>                 , ( ":isTLAcom"
>                   , (M . IsTLAcom) <$> pe
>                   , [ArgE]
>                   , "determine if expr is tier-locally Acom"
>                   )
>                 , ( ":isTLB"
>                   , (M . IsTLB) <$> pe
>                   , [ArgE]
>                   , "determine if expr is tier-locally a band"
>                   )
>                 , ( ":isTLPT"
>                   , (M . IsTLPT) <$> pe
>                   , [ArgE]
>                   , "determine if expr is tier-locally Piecewise Testable"
>                   )
>                 , ( ":isTLT"
>                   , (M . IsTLT) <$> pe
>                   , [ArgE]
>                   , "determine if expr is Tier-Locally Testable"
>                   )
>                 , ( ":isTLTT"
>                   , (M . IsTLTT) <$> pe
>                   , [ArgE]
>                   , "determine if expr is Tier-LTT"
>                   )
>                 , ( ":isTRDef"
>                   , (M . IsTRDef) <$> pe
>                   , [ArgE]
>                   , "determine if expr is reverse definite on a tier"
>                   )
>                 , ( ":isTrivial"
>                   , (M . IsTrivial) <$> pe
>                   , [ArgE]
>                   , "determine if expr has only a single state"
>                   )
>                 , ( ":isTSL"
>                   , (M . IsTSL) <$> pe
>                   , [ArgE]
>                   , "determine if expr is Strictly Tier-Local"
>                   )
>                 , ( ":Jmin"
>                   , (L . D_JE) <$> pe
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
>                 , ( ":psg"
>                   , (L . D_PSG) <$> pe
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
>                   , (M . uncurry SSubset) <$> p2e
>                   , [ArgE, ArgE]
>                   , "determine if expr1 is a strict subset of expr2"
>                   )
>                 , ( ":subset"
>                   , (M . uncurry Subset) <$> p2e
>                   , [ArgE, ArgE]
>                   , "determine if expr1 is a subset of expr2"
>                   )
>                 , ( ":synmon"
>                   , (L . D_SM) <$> pe
>                   , [ArgE]
>                   , ":display the syntactic monoid of expr"
>                   )
>                 , ( ":synord"
>                   , (L . D_SO) <$> pe
>                   , [ArgE]
>                   , "display teh syntactic order of expr"
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

> doCommand :: Env -> Command -> IO Env
> doCommand e@(dict, subexprs, ex) c
>     = case c
>       of Bindings
>              -> putStrLn "# Symbol aliases:" >>
>                 mapM_ (\(n, s) ->
>                        putStrLn
>                        (n ++ " <- " ++ deescape (formatSet s))
>                       ) dict >>
>                 putStrLn "# Expression aliases:" >>
>                 putStrLn (formatSet $ tmap fst subexprs) >>
>                 return e
>          Display expr -> disp id expr
>          D_EB expr -> disp' display' (to EggBox) expr
>          D_JE expr -> disp (renameStatesBy (formatSet . tmap f)
>                             . minimizeOver jEquivalence
>                             . syntacticMonoid) expr
>          D_PSG expr -> disp (renameStatesBy formatSet . powersetGraph) expr
>          D_SM expr -> disp (renameStatesBy f . syntacticMonoid) expr
>          D_SO expr -> disp' display' (to SyntacticOrder) expr
>          Dotify expr -> dot id expr
>          DT_PSG expr -> dot (renameStatesBy formatSet . powersetGraph) expr
>          DT_SM expr -> dot (renameStatesBy f . syntacticMonoid) expr
>          ErrorMsg str -> hPutStr stderr str >> return e
>          Help xs -> lessHelp xs >> return e
>          Import file
>              -> catchIOError
>                 (importScript e =<< lines <$> readFileWithExpansion file)
>                 (const $
>                  hPutStrLn stderr
>                  ("failed to read \"" ++ file ++ "\"") >>
>                  return e
>                 )
>          LearnSL k file -> selearn (fSL k) file
>          LearnSP k file -> selearn (fSP k) file
>          LearnTSL k file -> selearn (fTSL k) file
>          Loadstate file
>              -> catchIOError (read <$> readFileWithExpansion file)
>                 (const $
>                  hPutStrLn stderr
>                  ("failed to read \"" ++ file ++ "\"") >>
>                  return e
>                 )
>          Read file
>              -> catchIOError (doStatements e <$> readFileWithExpansion file)
>                 (const $
>                  hPutStrLn stderr
>                  ("failed to read \"" ++ file ++ "\"") >>
>                  return e
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
>                  (return . insertExpr e . fromSemanticAutomaton) =<<
>                  readMaybe <$> readFileWithExpansion file
>                 )
>                 (const $
>                  hPutStrLn stderr
>                  ("failed to read \"" ++ file ++ "\"") >>
>                  return e
>                 )
>          ReadJeff file
>              -> catchIOError
>                 (either
>                  (const $
>                   hPutStrLn stderr
>                   "input not a Jeff, environment unchanged" >>
>                   return e
>                  )
>                  (return . insertExpr e . fromAutomaton) =<<
>                  fromE Jeff <$> readFileWithExpansion file
>                 )
>                 (const $
>                  hPutStrLn stderr
>                  ("failed to read \"" ++ file ++ "\"") >>
>                  return e
>                 )
>          Reset -> return (empty, empty, Nothing)
>          --
>          -- Note: RestoreUniverse is implemented in a probably-inefficient
>          --       way, by making use of the side-effect that all assignments
>          --       properly update the universe.  The code currently just
>          --       rebinds every bound variable by creating and evaluating
>          --       assignment statements.  This should be done differently.
>          --
>          RestoreUniverse
>              -> let d' = keep ((/= "universe") . fst) dict
>                 in return . doStatements (d', subexprs, ex) .
>                    unlines . fromCollapsible $
>                    union
>                    (tmap
>                     (\(a, _) ->
>                      "= " ++ a ++ " { " ++ a ++ " } "
>                     ) $ d'
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
>              -> if (both
>                     (isNotIn (tmap fst subexprs))
>                     (isNotIn (tmap fst dict))
>                     name
>                    )
>                 then putStrLn ("undefined variable \"" ++ name ++ "\"") >>
>                      return e
>                 else mapM_
>                      (\(_,a) ->
>                       putStrLn (name ++ " <- " ++ show a)
>                      ) (keep ((== name) . fst) subexprs) >>
>                      mapM_
>                      (\(_,s) ->
>                       putStrLn (name ++ " <- " ++ deescape (formatSet s))
>                      ) (keep ((== name) . fst) dict) >>
>                      return e
>          Unset name
>              -> return ( keep ((/= name) . fst) dict
>                        , keep ((/= name) . fst) subexprs
>                        , if name == "it"
>                          then Nothing
>                          else ex
>                        )
>          Write file expr
>              -> let aut = makeAutomaton $ insertExpr e expr
>                 in maybe
>                    (hPutStrLn stderr "could not make automaton")
>                    (\a -> werr file (unlines $ [show a]))
>                    aut >> return e
>          WriteATT f1 f2 f3 expr
>              -> let aut  =  fmap desemantify . makeAutomaton $
>                             insertExpr e expr
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
>           disp = disp' display
>           disp' how x expr
>               = (maybe err (how . x . normalize . desemantify) $
>                  makeAutomaton (dict, subexprs, Just expr)
>                 ) >> return e
>           dot :: (Ord n, Show n) =>
>                  (FSA Integer String -> FSA n String) -> Expr -> IO Env
>           dot = disp' (putStr . to Dot)
>           err = hPutStrLn stderr "could not parse expression"
>           f (_, xs) = '<' : intercalate " " (map f' xs) ++ ">"
>           f' Epsilon = "ε"
>           f' (Symbol x) = x
>           werr ofile s
>               = catchIOError (writeAndCreateDir ofile s)
>                 (const $
>                  hPutStrLn stderr
>                  ("failed to write \"" ++ ofile ++
>                   if (any isPathSeparator ofile)
>                   then "\nDoes the directory exist?"
>                   else ""
>                  )
>                 )
>           selearn :: Grammar g => ([String] -> g String) -> FilePath -> IO Env
>           selearn method file
>               = catchIOError
>                 (insertExpr e <$> fromAutomaton <$> genFSA
>                  <$> learn method
>                  <$> map (Just . words) <$> lines
>                  <$> readFileWithExpansion file
>                 )
>                 (const $
>                  hPutStrLn stderr
>                  ("failed to read \"" ++ file ++ "\"") >>
>                  return e
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
>                  (return . insertExpr e . fromAutomaton) =<<
>                  fromE typ <$>
>                  (embedSymbolsATT <$>
>                   readFileWithExpansion f1 <*>
>                   (if f2 == "_"
>                    then mempty
>                    else Just <$> readFileWithExpansion f2
>                   ) <*>
>                   (if f3 == "_"
>                    then mempty
>                    else Just <$> readFileWithExpansion f3
>                   )
>                  )
>                 )
>                 (const $
>                  hPutStrLn stderr
>                  "failed to read input files" >>
>                  return e
>                 )


> doHelp :: [(String, [ArgType], String)] -> String
> doHelp xs = showArg ArgE ++ " = expression, "  ++
>             showArg ArgF ++ " = file, "        ++
>             showArg ArgI ++ " = int, "         ++
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
>           showArg ArgI  =  "<i>"
>           showArg _     =  "<v>"
>           showArgs = concatMap ((' ':) . showArg)
>           p1 = map (\(a,_,_) -> a)
>           p2 = map (\(_,b,_) -> b)
>           p3 = map (\(_,_,c) -> c)

> lessHelp :: [(String, [ArgType], String)] -> IO ()
> lessHelp xs = do
>   mpager <- fmap (map snd . filter ((==) "PAGER" . fst)) getEnvironment
>   let ps     =  words $ head (mpager ++ ["less"])
>       (p,s)  =  case ps of
>                   (y:ys) -> (y,ys)
>                   _ -> ("less",[])
>       lessP  =  (proc p s)
>                 { std_in = CreatePipe
>                 , std_out = UseHandle stdout
>                 , std_err = CreatePipe
>                 }
>   (Just p_stdin, _, Just p_stderr, less_ph) <- createProcess lessP
>   _ <- hGetContents p_stderr
>   hPutStr p_stdin (doHelp xs)
>   hClose p_stdin
>   _ <- waitForProcess less_ph
>   return ()

> doRelation :: Env -> Relation -> Maybe Bool
> doRelation e r
>     = case r
>       of CEqual p1 p2   ->  relate id e (==) p1 p2
>          Equal p1 p2    ->  relate desemantify e (==) p1 p2
>          CImply p1 p2   ->  relate id e isSupersetOf p1 p2
>          IsAcom p       ->  check isAcom p
>          IsB p          ->  check isB p
>          IsCB p         ->  check isCB p
>          IsDef p        ->  check isDef p
>          IsFin p        ->  check isFinite p
>          IsFO2 p        ->  check isFO2 p
>          IsFO2B p       ->  check isFO2B p
>          IsFO2BF p      ->  check isFO2BF p
>          IsFO2S p       ->  check isFO2S p
>          IsGD p         ->  check isGD p
>          IsGLPT p       ->  check isGLPT p
>          IsGLT p        ->  check isGLT p
>          IsLAcom p      ->  check isLAcom p
>          IsLB p         ->  check isLB p
>          IsLPT p        ->  check isLPT p
>          IsLT p         ->  check isLT p
>          IsLTT p        ->  check isLTT p
>          IsMTDef p      ->  check isMTDef p
>          IsMTF p        ->  check isMTF p
>          IsMTGD p       ->  check isMTGD p
>          IsMTRDef p     ->  check isMTRDef p
>          IsPT p         ->  check isPT p
>          IsRDef p       ->  check isRDef p
>          IsSF p         ->  check isSF p
>          IsSL p         ->  check isSL p
>          IsSP p         ->  check isSP p
>          IsTDef p       ->  check isTDef p
>          IsTGD p        ->  check isTGD p
>          IsTLAcom p     ->  check isTLAcom p
>          IsTLB p        ->  check isTLB p
>          IsTLT p        ->  check isTLT p
>          IsTLPT p       ->  check isTLPT p
>          IsTLTT p       ->  check isTLTT p
>          IsTRDef p      ->  check isTRDef p
>          IsTrivial p    ->  check isTrivial p
>          IsTSL p        ->  check isTSL p
>          Subset p1 p2   ->  relate desemantify e isSupersetOf p1 p2
>          SSubset p1 p2  ->  relate desemantify e isProperSupersetOf p1 p2
>     where check f p = fmap f . fmap normalize . fmap desemantify .
>                       makeAutomaton $ (\(a, b, _) -> (a, b, Just p)) e

> relate :: (FSA Integer (Maybe String) -> x) ->
>           Env ->
>           (x -> x -> a) -> Expr -> Expr ->
>           Maybe a
> relate g (a,b,_) f p1 p2 = f' <$> makeAutomaton e1 <*> makeAutomaton e2
>     where e1 = (a, b, Just p1)
>           e2 = (a, b, Just p2)
>           f' x y = let ss = collapse (maybe id insert) empty $
>                             union (alphabet x) (alphabet y)
>                    in f (g $ semanticallyExtendAlphabetTo ss x)
>                         (g $ semanticallyExtendAlphabetTo ss y)

> act :: Env -> Trither Command Relation Env -> IO Env
> act d = trither
>         (doCommand d)
>         (\r -> maybe err print (doRelation d r) >> return d)
>         return
>     where err = hPutStrLn stderr "could not parse relation"

> importScript :: Env -> [String] -> IO Env
> importScript e [] = return e
> importScript e (a:as) = flip importScript as =<< act e (processLine e a)



> deescape :: String -> String
> deescape ('\\' : '&' : xs) = deescape xs
> deescape ('\\' : x : xs)
>     | isEmpty digits  =  x : deescape xs
>     | otherwise       =  toEnum (read digits) : deescape others
>     where (digits, others) = span (isIn "0123456789") (x:xs)
> deescape (x:xs)  =  x : deescape xs
> deescape _       =  []

> display :: (Ord n, Ord e, Show n, Show e) => FSA n e -> IO ()
> display = display' . to Dot

> display' :: String -> IO ()
> display' s = do
>   let dotP = (proc "dot" ["-Tpng"])
>              { std_in = CreatePipe
>              , std_out = CreatePipe
>              , std_err = CreatePipe
>              }
>   (Just p_stdin, Just pipe, Just p_stderr, dot_ph) <- createProcess dotP
>   _ <- hGetContents p_stderr
>   hSetBinaryMode pipe True
>   let displayP = (proc "display" [])
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
> modwords' [] partial = if null partial then [] else [partial]
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
>         ("~":xs) -> joinPath <$> (:xs)
>                     <$> catchIOError getHomeDirectory (const (pure "~"))
>         _ -> pure fp
>     where parts = splitDirectories fp
