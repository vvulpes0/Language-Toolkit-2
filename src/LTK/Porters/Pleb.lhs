> {-# OPTIONS_HADDOCK show-extensions #-}
> {-# Language CPP #-}

#if !defined(MIN_VERSION_base)
# define MIN_VERSION_base(a,b,c) 0
#endif

> {-|
> Module:    LTK.Porters.Pleb
> Copyright: (c) 2018-2024 Dakotah Lambert
> License:   MIT

> The (P)iecewise / (L)ocal (E)xpression (B)uilder.
> This module defines a parser for a representation of
> logical formulae over subsequence- and adjacency-factors,
> as well as a mechanism for evaluating (creating an t'FSA' from)
> the resulting expression tree.

> There are two special variables:
> 
> * @it@ describes the most recent expression, and
> 
> * @universe@ collects all symbols used.
> -}
> module LTK.Porters.Pleb
>        ( Dictionary
>        , Parse(..)
>        , Env
>        , Expr
>        , SymSet
>        , Token
>        , compileEnv
>        , groundEnv
>        , insertExpr
>        , fromAutomaton
>        , fromSemanticAutomaton
>        , makeAutomaton
>        , makeAutomatonE
>        , doStatements
>        , doStatementsWithError
>        , parseExpr
>        , readPleb
>        , restoreUniverse
>        , restrictUniverse
>        , tokenize
>        ) where

#if !MIN_VERSION_base(4,8,0)
> import Data.Functor ((<$>))
> import Data.Monoid (mconcat)
> import Control.Applicative (Applicative, pure, (<*>))
#endif
> import Control.Applicative ( Alternative
>                            , empty, many, some, (<|>))
> import Data.Char (isLetter, isSpace)
> import Data.Foldable (asum)
> import Data.List (intersperse,foldl1')
> import Data.Map (Map)
> import Data.Set (Set)
> import qualified Data.Map as Map
> import qualified Data.Set as Set

> import LTK.FSA
> import LTK.Factors (Factor(..), buildLiteral, required)
> import LTK.Extract.SP (subsequenceClosure)

> -- |A syntactic unit.
> data Token = TSymbol Char
>            | TName String
>              deriving (Eq, Ord, Read, Show)

> -- |Convert a string into a stream of tokens ready for parsing.
> tokenize  :: String -> [Token]
> tokenize "" = []
> tokenize (x:xs)
>     | x == '#'    =  tokenize (dropWhile (/= '\n') xs)
>     | isSpace x   =  tokenize (dropWhile isSpace xs)
>     | isLetter x  =  uncurry (:) . mapfst TName . fmap tokenize $
>                      break (\s -> s == ',' || isDelim s || isSpace s) (x:xs)
>     | otherwise   =  TSymbol x : tokenize xs
>     where isDelim c = matchingDelimiter c /= c || c == '|'

> -- |The environment: defined sets of symbols and defined expressions.
> type Env = (Dictionary (Set String), Dictionary Expr)

> -- |An expression, the root of an expression tree.
> data Expr
>     = Automaton (FSA Integer (Maybe String))
>     | Concatenation [Expr]
>     | Conjunction [Expr]
>     | Disjunction [Expr]
>     | Domination [Expr]
>     | DownClose Expr            -- ^@since 1.0
>     | Factor PLFactor
>     | Infiltration [Expr]       -- ^@since 1.1
>     | Iteration Expr
>     | Negation Expr
>     | Neutralize [SymSet] Expr  -- ^@since 1.1
>     | Reversal Expr             -- ^@since 1.1
>     | Shuffle [Expr]            -- ^@since 1.1
>     | StrictOrder [Expr]
>     | Tierify [SymSet] Expr
>     | QuotientL [Expr]          -- ^@since 1.0
>     | QuotientR [Expr]          -- ^@since 1.0
>     | UpClose Expr              -- ^@since 1.1
>     | Variable String
>       deriving (Eq, Ord, Read, Show)

> -- |A subexpression representing a single Piecewise-Local factor.
> -- @Left s@ represents a variable name, while @Right x@ is a real set.
> data PLFactor
>     = PLFactor Bool Bool [[SymSet]]
>     | PLGap [PLFactor]
>     | PLCat [PLFactor]
>     | PLVariable String
>       deriving (Eq, Ord, Read, Show)

> -- |A particular action.
> data Statement
>     = EAssignment String Expr
>     | SAssignment String SymSet
>       deriving (Eq, Ord, Read, Show)

> -- |A set of symbols.
> data SymSet = SSSet (Set String)
>             | SSUni [SymSet]
>             | SSInt [SymSet]
>             | SSVar String
>               deriving (Eq, Ord, Read, Show)

> -- |Parse an input string and create a stringset-automaton
> -- from the result.
> readPleb :: String -> Either String (FSA Integer String)
> readPleb = fmap desemantify
>            . (=<<) (flip makeAutomatonE (Variable "it"))
>            . (=<<) (evaluateS (Map.empty, Map.empty) . fst)
>            . doParse parseStatements
>            . tokenize

> -- |Parse an input string and update the environment
> -- according to the result of the parse.
> doStatements :: Env -> String -> Env
> doStatements d  =  either (const d) id . doStatementsWithError d

> -- |Parse an input string and update the environment
> -- according to the result of the parse.  Pass along
> -- errors encountered.
> doStatementsWithError :: Env -> String -> Either String Env
> doStatementsWithError d str
>     = evaluateS d =<< f =<< (doParse parseStatements $ tokenize str)
>     where f (x, []) = Right x
>           f _ = Left $ unlines ["input not exhausted"]

> -- |Add a new expression to the environment, call it "@(it)@".
> insertExpr :: Env -> Expr -> Env
> insertExpr d e
>     = either (const d) id $ evaluate d (EAssignment "it" e)

> -- |Act upon a statement, reporting any semantic errors
> -- (i.e. undefined variables)
> evaluate :: Env -> Statement -> Either String Env
> evaluate d@(dict,subexprs) stmt
>     = case stmt of
>         EAssignment name e
>             -> (\x -> ( mkUniverse $ usedSymbols x
>                       , define name x subexprs
>                       )
>                ) <$> fillVars d e
>         SAssignment name s
>             -> (\x -> ( let x' = getSyms x
>                         in define name x' $ mkUniverse x'
>                       , subexprs
>                       )
>                ) <$> fillVarsS d s
>     where u = either (const Set.empty) id $ definition "universe" dict
>           mkUniverse s = define "universe" (Set.union s u) dict
> -- |Act upon a sequence of statements.
> evaluateS :: Env -> [Statement] -> Either String Env
> evaluateS d [] = Right d
> evaluateS d (x:xs) = evaluate d x >>= (\d' -> evaluateS d' xs)

> -- |Instantiate variables in an expression.
> fillVars :: Env -> Expr -> Either String Expr
> fillVars d@(_,subexprs) e
>     = case e of
>         Automaton x       ->  Right $ Automaton x
>         Concatenation xs  ->  Concatenation <$> f xs
>         Conjunction xs    ->  Conjunction <$> f xs
>         Disjunction xs    ->  Disjunction <$> f xs
>         Domination xs     ->  Domination  <$> f xs
>         DownClose x       ->  DownClose <$> fillVars d x
>         Factor x          ->  Factor <$> (fillVarsF d x)
>         Infiltration xs   ->  Infiltration <$> f xs
>         Iteration x       ->  Iteration <$> fillVars d x
>         Negation x        ->  Negation <$> fillVars d x
>         Neutralize ts x
>             -> Neutralize <$> sequence (map (fillVarsS d) ts)
>                <*> fillVars d x
>         QuotientL xs      ->  QuotientL <$> f xs
>         QuotientR xs      ->  QuotientR <$> f xs
>         Reversal x        ->  Reversal <$> fillVars d x
>         Shuffle xs        ->  Shuffle <$> f xs
>         StrictOrder xs    ->  StrictOrder <$> f xs
>         Tierify ts x
>             -> Tierify <$> sequence (map (fillVarsS d) ts)
>                <*> fillVars d x
>         UpClose x         ->  UpClose <$> fillVars d x
>         Variable v        ->  fillVars d =<< definition v subexprs
>     where f es = sequence $ map (fillVars d) es
> fillVarsF :: Env -> PLFactor -> Either String PLFactor
> fillVarsF d (PLFactor h t ps)
>     = fmap (PLFactor h t)
>       . sequence $ map (sequence . map (fillVarsS d)) ps
> fillVarsF d (PLCat fs)
>           = fmap PLCat . sequence $ map (fillVarsF d) fs
> fillVarsF d (PLGap fs)
>           = fmap PLGap . sequence $ map (fillVarsF d) fs
> fillVarsF d@(_,subexprs) (PLVariable s)
>     = case definition s subexprs of
>         Left msg -> Left msg
>         Right (Variable v) -> fillVarsF d (PLVariable v)
>         Right (Factor p) -> fillVarsF d p
>         Right _ -> Left $ unlines
>                    ["attempted to use the non-factor "
>                     ++ s ++ " as a factor"]
> fillVarsS :: Env -> SymSet -> Either String SymSet
> fillVarsS d@(dict,_) s
>     = case s of
>         SSSet xs -> Right $ SSSet xs
>         SSUni xs -> fmap SSUni . sequence $ map (fillVarsS d) xs
>         SSInt xs -> fmap SSInt . sequence $ map (fillVarsS d) xs
>         SSVar v  -> SSSet <$> definition v dict

> -- |Transform all saved expressions into automata to prevent reevaluation.
> compileEnv :: Env -> Env
> compileEnv (dict, subexprs) = (dict, Map.map f subexprs)
>     where f = Automaton . renameStates
>               . minimizeDeterministic . automatonFromExpr

> -- |Convert saved automata from descriptions of constraints to
> -- descriptions of stringsets.
> -- This action effectively removes metadata describing constraint types
> -- from the environment.
> groundEnv :: Env -> Env
> groundEnv (dict, subexprs) = (dict, Map.map f subexprs)
>     where f = Automaton
>               . renameSymbolsBy Just
>               . renameStates . minimizeDeterministic
>               . desemantify . semanticallyExtendAlphabetTo universe
>               . automatonFromExpr
>           universe = either (const Set.empty) id
>                      (definition "universe" dict)

> -- |Reset the "@universe@" to contain all and only other symbols used.
> --
> -- @since 1.2
> restoreUniverse :: Env -> Env
> restoreUniverse (d, s) = (define "universe" syms d, s)
>     where syms = Map.foldr (Set.union . usedSymbols)
>                  (Set.unions . Map.elems $ Map.filterWithKey
>                   (\k _ -> k /= "universe") d) s

=====
Note:
=====

@restrictUniverse@ previously deleted symbolsets bound to the empty set.
However, it is now possible to manually define the empty set: [/a,/b].
Therefore, this cleanup step has been removed.

> -- |Remove any symbols not present in @(universe)@ from the environment.
> restrictUniverse :: Env -> Env
> restrictUniverse (dict, subexprs)
>     = ( Map.map (Set.intersection universe) dict
>       , Map.map restrictUniverseE subexprs
>       )
>     where universe = either (const Set.empty) id
>                      $ definition "universe" dict
>           restrictUniverseS s
>               = case s of
>                   SSSet x -> SSSet (intersection universe x)
>                   SSUni x -> SSUni $ map restrictUniverseS x
>                   SSInt x -> SSInt $ map restrictUniverseS x
>                   SSVar x -> SSVar x
>           restrictUniverseF pf
>               = case pf of
>                   PLVariable x -> PLVariable x
>                   PLGap ps -> PLGap $ map restrictUniverseF ps
>                   PLCat ps -> PLCat $ map restrictUniverseF ps
>                   PLFactor h t ps
>                       -> PLFactor h t
>                          $ map (map restrictUniverseS) ps
>           restrictUniverseE e
>               = case e of
>                   Automaton x
>                       ->  Automaton $
>                           contractAlphabetTo
>                           (insert Nothing (tmap Just universe))
>                           x
>                   Concatenation es  ->  f Concatenation es
>                   Conjunction es    ->  f Conjunction es
>                   Disjunction es    ->  f Disjunction es
>                   Domination es     ->  f Domination es
>                   DownClose ex      ->  g DownClose ex
>                   Factor pf
>                       ->  Factor $ restrictUniverseF pf
>                   Infiltration es   ->  f Infiltration es
>                   Iteration ex      ->  g Iteration ex
>                   Negation ex       ->  g Negation ex
>                   Neutralize ts ex
>                       -> g (Neutralize (tmap restrictUniverseS ts)) ex
>                   QuotientL es      ->  f QuotientL es
>                   QuotientR es      ->  f QuotientR es
>                   Reversal ex       ->  g Reversal ex
>                   Shuffle es        ->  f Shuffle es
>                   StrictOrder es    ->  f StrictOrder es
>                   Tierify ts ex
>                       -> g (Tierify (tmap restrictUniverseS ts)) ex
>                   UpClose ex        ->  g UpClose ex
>                   Variable x        ->  Variable x
>           f t es = t $ map restrictUniverseE es
>           g t e  = t $ restrictUniverseE e

> -- |Create an t'FSA' from an expression tree and environment,
> -- complete with metadata regarding the constraint(s) it represents.
> makeAutomaton :: Env -> Expr -> Maybe (FSA Integer (Maybe String))
> makeAutomaton e = either (const Nothing) Just . makeAutomatonE e

> -- |Create an t'FSA' from an expression tree and environment,
> -- complete with metadata regarding the constraint(s) it represents.
> makeAutomatonE :: Env -> Expr
>                -> Either String (FSA Integer (Maybe String))
> makeAutomatonE d@(dict, _) e
>     = renameStates . minimizeDeterministic
>       . semanticallyExtendAlphabetTo symsets
>       . automatonFromExpr <$> fillVars d e
>     where symsets = either (const Set.empty) id
>                     $ definition "universe" dict

The properties of semantic automata are used here to prevent having to
pass alphabet information to the individual constructors, which in turn
prevents having to descend through the tree to find this information.

> -- |Create an t'FSA' from an expression tree,
> -- complete with metadata regarding the constraint(s) it represents.
> automatonFromExpr :: Expr -> FSA Integer (Maybe String)
> automatonFromExpr e
>     = case e
>       of Automaton x             -> x
>          Concatenation es -> f emptyStr mconcat es
>          Conjunction es   -> f univLang flatIntersection es
>          Disjunction es   -> f emptyLanguage flatUnion es
>          Domination es
>              -> f emptyStr
>                 (mconcat .
>                  intersperse (totalWithAlphabet (singleton Nothing))
>                 ) es
>          DownClose ex
>              -> renameStates . minimize . subsequenceClosure $
>                 automatonFromExpr ex
>          Factor x
>              -> automatonFromPLFactor (simplifyPL x)
>          Infiltration es  -> f emptyStr flatInfiltration es
>          Iteration ex
>              -> renameStates . minimize . kleeneClosure $
>                 automatonFromExpr ex
>          Negation ex
>              -> complementDeterministic $ automatonFromExpr ex
>          Neutralize ts ex
>              -> renameStates . minimize
>                 . neutralize
>                   (Set.mapMonotonic Just . unionAll $ map getSyms ts)
>                 $ automatonFromExpr ex
>          QuotientL es     -> f emptyStr ql es
>          QuotientR es     -> f emptyStr qr es
>          Reversal ex
>              -> renameStates . minimize . LTK.FSA.reverse
>                 $ automatonFromExpr ex
>          Shuffle es       -> f emptyStr flatShuffle es
>          StrictOrder es   -> foldr
>                                     (\x y ->
>                                      renameStates . minimize
>                                      $ autStrictOrderOverlay x y)
>                                     emptyStr
>                                     $ automata es
>          Tierify ts ex
>              -> renameStates . minimize
>                 . tierify (unionAll $ map getSyms ts)
>                 $ automatonFromExpr ex
>          UpClose ex
>              -> renameStates . minimize . loopify $
>                 automatonFromExpr ex
>          Variable _
>              -> error "free variable in expression"
>     where f z tl xs = case automata xs
>                       of [] -> z
>                          a -> renameStates . minimize $ tl a
>           automata es
>               =  let as = map automatonFromExpr es
>                  in map (semanticallyExtendAlphabetTo $ bigAlpha as) as
>           univLang = totalWithAlphabet (Set.singleton Nothing)
>           emptyStr = totalWithAlphabet Set.empty
>           bigAlpha = collapse (maybe id insert) Set.empty .
>                      collapse (union . alphabet) Set.empty
>           ql xs = if null xs
>                   then emptyWithAlphabet (Set.singleton Nothing)
>                   else foldl1' (\a b -> renameStates $ quotLeft a b) xs
>           qr xs = if null xs
>                   then emptyWithAlphabet (Set.singleton Nothing)
>                   else foldr1 (\a b -> renameStates $ quotRight a b) xs

> automatonFromPLFactor :: (Bool, Bool, [[SymSet]])
>                       -> FSA Integer (Maybe String)
> automatonFromPLFactor (h, t, pieces')
>     = case tmap (tmap (tmap Just)) pieces of
>         []      ->  bl (Substring [] h t)
>         [p]     ->  bl (Substring p  h t)
>         (p:ps)  ->  if isPF
>                     then bl . Subsequence $ concat (p:ps)
>                     else renameStates . minimize . mconcat
>                          $ map bl lfs
>                         where lfs  =  Substring p h False : lfs' ps
>     where as           =  insert Nothing . tmap Just
>                           . Set.unions $ concat pieces
>           bl           =  buildLiteral as . required
>           isPF         =  not h && not t &&
>                           all ((==) [()] . map (const ())) pieces
>           lfs' [x]     =  Substring x False t : lfs' []
>           lfs' (x:xs)  =  Substring x False False : lfs' xs
>           lfs' _       =  []
>           pieces       =  map (map (getSyms)) pieces'

> getSyms :: SymSet -> Set String
> getSyms (SSSet ts) = ts
> getSyms (SSUni xs) = Set.unions $ map getSyms xs
> getSyms (SSInt []) = error "unreplaced void intersection"
> getSyms (SSInt (x:xs))
>     = foldr (Set.intersection) (getSyms x) (map getSyms xs)
> getSyms (SSVar _) = error "free variable in symset"

> usedSymbols :: Expr -> Set String
> usedSymbols e
>     = case e of
>         Automaton a
>              ->  collapse (maybe id insert) Set.empty $ alphabet a
>         Concatenation es  ->  us es
>         Conjunction es    ->  us es
>         Disjunction es    ->  us es
>         Domination es     ->  us es
>         DownClose ex      ->  usedSymbols ex
>         Factor f          ->  usedSymbolsF f
>         Infiltration es   ->  us es
>         Iteration ex      ->  usedSymbols ex
>         Negation ex       ->  usedSymbols ex
>         Neutralize ts ex
>             -> Set.unions (usedSymbols ex : map usedSymsInSet ts)
>         Reversal ex       ->  usedSymbols ex
>         Shuffle es        ->  us es
>         StrictOrder es    ->  us es
>         Tierify ts _
>             -> Set.unions $ map usedSymsInSet ts
>         QuotientL es      ->  us es
>         QuotientR es      ->  us es
>         UpClose ex        ->  usedSymbols ex
>         Variable _        ->  Set.empty
>     where us = collapse (union . usedSymbols) Set.empty
>           usedSymbolsF (PLFactor _ _ ps)
>               = Set.unions . map usedSymsInSet $ concat ps
>           usedSymbolsF (PLCat xs)
>               = Set.unions $ map usedSymbolsF xs
>           usedSymbolsF (PLGap xs)
>               = Set.unions $ map usedSymbolsF xs
>           usedSymbolsF (PLVariable _) = Set.empty

> usedSymsInSet :: SymSet -> Set String
> usedSymsInSet (SSSet ts) = ts
> usedSymsInSet (SSUni sets) = Set.unions $ map usedSymsInSet sets
> usedSymsInSet (SSInt sets) = Set.unions $ map usedSymsInSet sets
> usedSymsInSet (SSVar _) = Set.empty

> parseStatements :: Parse [Statement]
> parseStatements
>     = asum
>       [ (:)
>         <$> (EAssignment <$> (start >> getName) <*> parseExpr)
>         <*> parseStatements
>       , (:)
>         <$> (SAssignment <$> (start >> getName) <*> parseSymExpr)
>         <*> parseStatements
>       , (:) <$> (EAssignment "it" <$> parseExpr) <*> parseStatements
>       , Parse $ \ts ->
>         case ts
>         of []  ->  Right ([], [])
>            _   ->  Left $ unlines ["not finished"]
>       ]
>    where getName
>              = Parse $ \ts ->
>                case ts
>                of (TName n : ts') -> Right (n, ts')
>                   (x : _)
>                       -> Left . unlines . pure $
>                          "could not find name at " ++
>                          showParen True (shows x) ""
>                   _ -> Left . unlines . pure
>                        $ "end of input looking for name"
>          start = eat "≝" [] <|> eat "=" []

> -- |Parse an expression from a 'Token' stream.
> parseExpr :: Parse Expr
> parseExpr = asum
>             [ Parse var
>             , parseNAryExpr
>             , parseUnaryExpr
>             , Factor <$> parsePLFactor
>             ]
>     where var (TName n : ts) = Right (Variable n, ts)
>           var (x : _) = Left . unlines . pure $
>                         "not a variable: " ++
>                         showParen False (shows x) ""
>           var _ = Left $ unlines ["not a variable"]

> parseNAryExpr :: Parse Expr
> parseNAryExpr
>     = makeLifter
>       [ (["⋀", "⋂", "∧", "∩", "/\\"],  Conjunction)
>       , (["⋁", "⋃", "∨", "∪", "\\/"],  Disjunction)
>       , (["\\\\"],                     QuotientL)
>       , (["//"],                       QuotientR)
>       , ([".∙.", ".@."],               StrictOrder)
>       , (["∙∙", "@@"],                 Domination)
>       , (["∙" , "@" ],                 Concatenation)
>       , (["⧢", "|_|_|"],               Shuffle)
>       , (["⇑", ".^."],                 Infiltration)
>       ] <*> pd
>     where pd = parseEmpty
>                <|> parseDelimited ['(', '{']
>                    (parseSeparated "," $ parseExpr)
>           parseEmpty = Parse $ \xs ->
>                        case xs of
>                          (TSymbol '(':TSymbol ')':ts) -> Right ([], ts)
>                          (TSymbol '{':TSymbol '}':ts) -> Right ([], ts)
>                          _ -> Left $ unlines ["not an empty expr"]

> parseUnaryExpr :: Parse Expr
> parseUnaryExpr
>     = (makeLifter
>        [ (["↓", "$"],       DownClose)
>        , (["↑", "^"],       UpClose)
>        , (["*", "∗"],       Iteration)
>        , (["+"],            plus)
>        , (["¬", "~", "!"],  Negation)
>        , (["⇄", "-"],       Reversal)
>        ] <*> parseExpr
>       ) <|> (Tierify <$> pt <*> parseExpr)
>         <|> (Neutralize <$> pn <*> parseExpr)
>     where pt = parseDelimited ['['] (parseSeparated "," parseSymExpr)
>           pn = parseDelimited ['|'] (parseSeparated "," parseSymExpr)
>           plus e = Concatenation [e, Iteration e]

> parsePLFactor :: Parse PLFactor
> parsePLFactor = combine ".." PLGap <|> combine "‥" PLGap
>                 <|> combine "." PLCat
>                 <|> pplf
>     where combine s f = eat s f <*>
>                         parseDelimited ['<', '⟨']
>                         (parseSeparated "," pplf)
>           pplf = parseBasicPLFactor <|> Parse var
>           var (TName n : ts) = Right (PLVariable n, ts)
>           var (x : _) = Left . unlines . pure $
>                         "not a variable: " ++
>                         showParen False (shows x) ""
>           var _ = Left $ unlines ["not a variable"]

> parseBasicPLFactor :: Parse PLFactor
> parseBasicPLFactor
>     = makeLifter
>       [ (["⋊⋉", "%||%"], PLFactor True True)
>       , (["⋊", "%|"], PLFactor True False)
>       , (["⋉", "|%"], PLFactor False True)
>       , ([""], PLFactor False False)
>       ]
>       <*> parseDelimited ['<', '⟨']
>           (parseSeparated "," $ some parseSymExpr
>            <|> Parse (\ts -> Right ([], ts)))

> parseSymExpr :: Parse SymSet
> parseSymExpr
>     = (fmap SSUni
>        . parseDelimited ['{', '(']
>        $ parseSeparated "," parseSymExpr)
>       <|> ( fmap SSInt
>           . parseDelimited ['[']
>           $ parseSeparated "," parseSymExpr)
>       <|> parseSymSet

> parseSymSet :: Parse SymSet
> parseSymSet
>     = Parse $ \xs ->
>       case xs
>       of (TName n : ts)
>              -> Right ((SSVar n), ts)
>          (TSymbol '/' : TName n : ts)
>              -> Right ((SSSet $ Set.singleton n), ts)
>          (a:_)
>              -> Left . unlines . pure $
>                 "cannot start a SymSet with " ++
>                 showParen True (shows a) ""
>          _ -> Left $ unlines ["unexpected end of input in SymSet"]

> makeLifter :: [([String], a)] -> Parse a
> makeLifter = asum . concatMap (map (uncurry eat) . f)
>     where f ([], _)    =  []
>           f (x:xs, g)  =  (x, g) : f (xs, g)

> eat :: String -> a -> Parse a
> eat str f = Parse $ \ts ->
>             if isPrefixOf ts (tmap TSymbol str)
>             then Right (f, drop (length str) ts)
>             else Left ""

> parseDelimited :: [Char] -> Parse [a] -> Parse [a]
> parseDelimited ds pl = parseOpeningDelimiter ds >>= f
>     where f d = (++) <$> pl <*> parseClosingDelimiter d

> parseOpeningDelimiter :: [Char] -> Parse Char
> parseOpeningDelimiter ds = Parse openingDelimiter
>     where openingDelimiter (TSymbol x : ts)
>               | isIn ds x  =  Right (x, ts)
>               | otherwise  =  Left . unlines . pure $
>                               "sought " ++ sought ds ++
>                               " but instead found " ++ show x
>           openingDelimiter _
>               = Left . unlines . pure $
>                 "unexpected end of input looking for "
>                 ++ sought ds
>           sought (x:[]) = '\'' : x : "'"
>           sought (x:xs) = '\'' : x : '\'' : ',' : sought xs
>           sought _ = "nothing"

> parseClosingDelimiter :: Char -> Parse [a]
> parseClosingDelimiter = flip eat [] . singleton . matchingDelimiter

> parseSeparated :: String -> Parse a -> Parse [a]
> parseSeparated string p = (:) <$> p <*> many (eat string [] >> p)



> simplifyPL :: PLFactor -> (Bool, Bool, [[SymSet]])
> simplifyPL p
>     = case p of
>         PLVariable _ -> error "free variable in PLFactor"
>         PLFactor h t ps -> (h, t, ps)
>         PLCat [] -> (False, False, [])
>         PLCat (x:xs) -> let (h, _, a) = simplifyPL x
>                             (_, t, b) = simplifyPL (PLCat xs)
>                         in (h, t, pc a b)
>         PLGap [] -> (False, False, [])
>         PLGap (x:xs) -> let (h, _, a) = simplifyPL x
>                             (_, t, b) = simplifyPL (PLGap xs)
>                         in (h, t, a ++ b)
>     where pc [] bs       =  bs
>           pc [a] []      =  [a]
>           pc [a] (b:bs)  = (a ++ b) : bs
>           pc (a:as) bs   =  a : pc as bs



> -- |An association between names and values.
> type Dictionary a = Map String a

> define :: (Ord a) => String -> a -> Dictionary a -> Dictionary a
> define name value = Map.insert name value

> definition :: (Ord a) => String -> Dictionary a -> Either String a
> definition a = maybe (Left undef) Right . Map.lookup a
>     where undef = unlines ["undefined variable \"" ++ a ++ "\""]

> -- |The base type for a combinatorial parser.
> newtype Parse a = Parse
>     {doParse :: [Token] -> Either String (a, [Token])}

> instance Functor Parse
>     where fmap g (Parse f) = Parse (fmap (mapfst g) . f)

> instance Applicative Parse
>     where pure     =  Parse <$> fmap Right . (,)
>           f <*> x  =  Parse $ \s0 ->
>                       let h (g, s1) = mapfst g <$> doParse x s1
>                       in h =<< doParse f s0

> instance Alternative Parse
>     where empty    =  Parse . const $ Left ""
>           p <|> q  =  Parse $ \ts ->
>                       let f s1 s2
>                             = unlines
>                               $ concatMap (filter (/= "") . lines)
>                               [s1, s2]
>                           h s = either (Left . f s) Right $ doParse q ts
>                       in either h Right $ doParse p ts

> instance Monad Parse
>     where p >>= f   =  Parse $ \s0 ->
>                        let h (a, s1) = doParse (f a) s1
>                        in h =<< doParse p s0
#if !MIN_VERSION_base(4,8,0)
>           return    =  pure
#endif



> -- |Generate an expression (sub)tree from an t'FSA' that
> -- contains metadata regarding the constraint(s) it represents.
> fromSemanticAutomaton :: FSA Integer (Maybe String) -> Expr
> fromSemanticAutomaton = Automaton . renameStates . minimize

> -- |Generate an expression (sub)tree from an t'FSA'.
> fromAutomaton :: FSA Integer String -> Expr
> fromAutomaton = fromSemanticAutomaton . renameSymbolsBy Just



> isPrefixOf :: Eq a => [a] -> [a] -> Bool
> isPrefixOf _ []  =  True
> isPrefixOf [] _  =  False
> isPrefixOf (a:as) (b:bs)
>     | a == b     =  isPrefixOf as bs
>     | otherwise  =  False

> mapfst :: (a -> b) -> (a, c) -> (b, c)
> mapfst f (a, c) = (f a, c)

> matchingDelimiter :: Char -> Char
> matchingDelimiter x = foldr f x delimiters
>     where f (a, b) u
>               | a == x     =  b
>               | b == x     =  a
>               | otherwise  =  u
>           delimiters
>               = [ ('<', '>')
>                 , ('⟨', '⟩')
>                 , ('(', ')')
>                 , ('[', ']')
>                 , ('{', '}')
>                 , ('|', '|')
>                 ]
