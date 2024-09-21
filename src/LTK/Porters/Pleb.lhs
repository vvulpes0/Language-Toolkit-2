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
> import Data.Functor.Classes (Read1(..),Show1(..))
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

> newtype Fix a = In { out :: a (Fix a) }
> instance Read1 f => Read (Fix f) where
>     readsPrec d = map (mapfst In) . liftReadsPrec readsPrec readList d
> instance Show1 f => Show (Fix f) where
>     showsPrec d = liftShowsPrec showsPrec showList d . out

> type Expr = Fix ExprF
> -- |An expression, the root of an expression tree.
> data ExprF a
>     = Automaton (FSA Integer (Maybe String))
>     | Concatenation [a]
>     | Conjunction [a]
>     | Disjunction [a]
>     | Domination [a]
>     | DownClose a
>     | Factor PLFactor
>     | Infiltration [a]
>     | Iteration a
>     | Negation a
>     | Neutralize [SymSet] a
>     | Reversal a
>     | Shuffle [a]
>     | StrictOrder [a]
>     | Tierify [SymSet] a
>     | QuotientL [a]
>     | QuotientR [a]
>     | UpClose a
>     | Variable String
>       deriving (Eq, Ord, Read, Show)
> instance Functor ExprF where
>    fmap _ (Automaton x)      = Automaton x
>    fmap f (Concatenation xs) = Concatenation (map f xs)
>    fmap f (Conjunction xs)   = Conjunction (map f xs)
>    fmap f (Disjunction xs)   = Disjunction (map f xs)
>    fmap f (Domination xs)    = Domination (map f xs)
>    fmap f (DownClose x)      = DownClose (f x)
>    fmap _ (Factor x)         = Factor x
>    fmap f (Infiltration xs)  = Infiltration (map f xs)
>    fmap f (Iteration x)      = Iteration (f x)
>    fmap f (Negation x)       = Negation (f x)
>    fmap f (Neutralize s x)   = Neutralize s (f x)
>    fmap f (Reversal x)       = Reversal (f x)
>    fmap f (Shuffle xs)       = Shuffle (map f xs)
>    fmap f (StrictOrder xs)   = StrictOrder (map f xs)
>    fmap f (Tierify s x)      = Tierify s (f x)
>    fmap f (QuotientL xs)     = QuotientL (map f xs)
>    fmap f (QuotientR xs)     = QuotientR (map f xs)
>    fmap f (UpClose x)        = UpClose (f x)
>    fmap _ (Variable x)       = Variable x
> instance Foldable ExprF where
>    foldr _ a (Automaton _)      = a
>    foldr f a (Concatenation xs) = foldr f a xs
>    foldr f a (Conjunction xs)   = foldr f a xs
>    foldr f a (Disjunction xs)   = foldr f a xs
>    foldr f a (Domination xs)    = foldr f a xs
>    foldr f a (DownClose x)      = f x a
>    foldr _ a (Factor _)         = a
>    foldr f a (Infiltration xs)  = foldr f a xs
>    foldr f a (Iteration x)      = f x a
>    foldr f a (Negation x)       = f x a
>    foldr f a (Neutralize _ x)   = f x a
>    foldr f a (Reversal x)       = f x a
>    foldr f a (Shuffle xs)       = foldr f a xs
>    foldr f a (StrictOrder xs)   = foldr f a xs
>    foldr f a (Tierify _ x)      = f x a
>    foldr f a (QuotientL xs)     = foldr f a xs
>    foldr f a (QuotientR xs)     = foldr f a xs
>    foldr f a (UpClose x)        = f x a
>    foldr _ a (Variable _)       = a
> instance Traversable ExprF where
>    sequenceA (Automaton x)      = pure $ Automaton x
>    sequenceA (Concatenation xs) = Concatenation <$> sequenceA xs
>    sequenceA (Conjunction xs)   = Conjunction <$> sequenceA xs
>    sequenceA (Disjunction xs)   = Disjunction <$> sequenceA xs
>    sequenceA (Domination xs)    = Domination <$> sequenceA xs
>    sequenceA (DownClose x)      = DownClose <$> x
>    sequenceA (Factor x)         = pure $ Factor x
>    sequenceA (Infiltration xs)  = Infiltration <$> sequenceA xs
>    sequenceA (Iteration x)      = Iteration <$> x
>    sequenceA (Negation x)       = Negation <$> x
>    sequenceA (Neutralize s x)   = (Neutralize s) <$> x
>    sequenceA (Reversal x)       = Reversal <$> x
>    sequenceA (Shuffle xs)       = Shuffle <$> sequenceA xs
>    sequenceA (StrictOrder xs)   = StrictOrder <$> sequenceA xs
>    sequenceA (Tierify s x)      = (Tierify s) <$> x
>    sequenceA (QuotientL xs)     = QuotientL <$> sequenceA xs
>    sequenceA (QuotientR xs)     = QuotientR <$> sequenceA xs
>    sequenceA (UpClose x)        = UpClose <$> x
>    sequenceA (Variable x)       = pure $ Variable x

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
>       --deriving (Eq, Ord, Read, Show)

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
>            . (=<<) (flip makeAutomatonE (In $ Variable "it"))
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
> fillVars d = cata (fillVarsEF d)
> fillVarsEF :: Env -> ExprF (Either String Expr) -> Either String Expr
> fillVarsEF d@(_,subexprs) e
>     = case e of
>         Factor x         ->  (In . Factor) <$> fillVarsF d x
>         Neutralize ts x  ->  curry (In . uncurry Neutralize)
>                              <$> sequenceA (map (fillVarsS d) ts)
>                              <*> x
>         Tierify ts x     ->  curry (In . uncurry Tierify)
>                              <$> sequenceA (map (fillVarsS d) ts)
>                              <*> x
>         Variable v       ->  fillVars d =<< definition v subexprs
>         _                ->  In <$> sequenceA e
> fillVarsF :: Env -> PLFactor -> Either String PLFactor
> fillVarsF d (PLFactor h t ps)
>     = fmap (PLFactor h t)
>       . sequence $ map (sequence . map (fillVarsS d)) ps
> fillVarsF d (PLCat fs)
>           = fmap PLCat . sequence $ map (fillVarsF d) fs
> fillVarsF d (PLGap fs)
>           = fmap PLGap . sequence $ map (fillVarsF d) fs
> fillVarsF d@(_,subexprs) (PLVariable s)
>     = case out <$> definition s subexprs of
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
>     where f = In . Automaton . renameStates
>               . minimizeDeterministic . automatonFromExpr

> -- |Convert saved automata from descriptions of constraints to
> -- descriptions of stringsets.
> -- This action effectively removes metadata describing constraint types
> -- from the environment.
> groundEnv :: Env -> Env
> groundEnv (dict, subexprs) = (dict, Map.map f subexprs)
>     where f = In . Automaton
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
>           restrictUniverseE = cata restrictUniverseEF
>           restrictUniverseEF e
>               = case e of
>                   Automaton x
>                       ->  In . Automaton $
>                           contractAlphabetTo
>                           (insert Nothing (tmap Just universe))
>                           x
>                   Factor pf
>                       ->  In . Factor $ restrictUniverseF pf
>                   Neutralize ts ex
>                       ->  In $ (Neutralize (tmap restrictUniverseS ts)) ex
>                   Tierify ts ex
>                       ->  In $ (Tierify (tmap restrictUniverseS ts)) ex
>                   _ -> In e

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
> automatonFromExpr = cata automatonFromEF
> automatonFromEF :: ExprF (FSA Integer (Maybe String))
>                 -> FSA Integer (Maybe String)
> automatonFromEF e
>     = case e of
>         Automaton x      -> x
>         Concatenation xs -> f emptyStr mconcat xs
>         Conjunction xs   -> f univLang flatIntersection xs
>         Disjunction xs   -> f emptyLanguage flatUnion xs
>         Domination xs    -> f emptyStr mconcat $ intersperse univLang xs
>         DownClose x      -> renameStates . minimize $ subsequenceClosure x
>         Factor x         -> automatonFromPLFactor (simplifyPL x)
>         Infiltration xs  -> f emptyStr flatInfiltration xs
>         Iteration x      -> renameStates . minimize $ kleeneClosure x
>         Negation x       -> complementDeterministic x
>         Neutralize ts x
>             -> renameStates . minimize
>                $ neutralize
>                  (Set.mapMonotonic Just . unionAll $ map getSyms ts) x
>         QuotientL xs     -> f emptyStr ql xs
>         QuotientR xs     -> f emptyStr qr xs
>         Reversal x       -> renameStates . minimize $ LTK.FSA.reverse x
>         Shuffle xs       -> f emptyStr flatShuffle xs
>         StrictOrder xs
>             -> foldr (\x y -> renameStates . minimize
>                               $ autStrictOrderOverlay x y)
>                      emptyStr $ ext xs
>         Tierify ts x
>             -> renameStates . minimize
>                $ tierify (unionAll $ map getSyms ts) x
>         UpClose x        -> renameStates . minimize $ loopify x
>         Variable _       -> error "free variable in expression"
>     where f z _ [] = z
>           f _ tl xs = renameStates . minimize . tl $ ext xs
>           ext xs = let as = bigAlpha xs
>                    in map (semanticallyExtendAlphabetTo as) xs
>           bigAlpha = collapse (maybe id insert) Set.empty .
>                      collapse (union . alphabet) Set.empty
>           univLang = totalWithAlphabet (Set.singleton Nothing)
>           emptyStr = totalWithAlphabet Set.empty
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
> usedSymbols = cata usedSymbolsE
> usedSymbolsE :: ExprF (Set String) -> Set String
> usedSymbolsE e = case e of
>     Automaton a     -> collapse (maybe id insert) Set.empty $ alphabet a
>     Factor f        -> usedSymbolsF f
>     Neutralize ts x -> Set.unions (x : map usedSymsInSet ts)
>     Tierify ts x    -> Set.unions (x : map usedSymsInSet ts)
>     _               -> foldr Set.union Set.empty e
>     where usedSymbolsF (PLFactor _ _ ps)
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
>             , In . Factor <$> parsePLFactor
>             ]
>     where var (TName n : ts) = Right (In $ Variable n, ts)
>           var (x : _) = Left . unlines . pure $
>                         "not a variable: " ++
>                         showParen False (shows x) ""
>           var _ = Left $ unlines ["not a variable"]

> parseNAryExpr :: Parse Expr
> parseNAryExpr
>     = makeLifter
>       [ (["⋀", "⋂", "∧", "∩", "/\\"],  In . Conjunction)
>       , (["⋁", "⋃", "∨", "∪", "\\/"],  In . Disjunction)
>       , (["\\\\"],                     In . QuotientL)
>       , (["//"],                       In . QuotientR)
>       , ([".∙.", ".@."],               In . StrictOrder)
>       , (["∙∙", "@@"],                 In . Domination)
>       , (["∙" , "@" ],                 In . Concatenation)
>       , (["⧢", "|_|_|"],               In . Shuffle)
>       , (["⇑", ".^."],                 In . Infiltration)
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
>        [ (["↓", "$"],       In . DownClose)
>        , (["↑", "^"],       In . UpClose)
>        , (["*", "∗"],       In . Iteration)
>        , (["+"],            In . plus)
>        , (["¬", "~", "!"],  In . Negation)
>        , (["⇄", "-"],       In . Reversal)
>        ] <*> parseExpr
>       ) <|> (curry (In . uncurry Tierify) <$> pt <*> parseExpr)
>         <|> (curry (In . uncurry Neutralize) <$> pn <*> parseExpr)
>     where pt = parseDelimited ['['] (parseSeparated "," parseSymExpr)
>           pn = parseDelimited ['|'] (parseSeparated "," parseSymExpr)
>           plus e = Concatenation [e, In $ Iteration e]
 
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

> define :: String -> a -> Dictionary a -> Dictionary a
> define name value = Map.insert name value

> definition :: String -> Dictionary a -> Either String a
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
> fromSemanticAutomaton = In . Automaton . renameStates . minimize

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

Traversals

> cata :: Functor f => (f a -> a) -> Fix f -> a
> cata f = f . fmap (cata f) . out

Read1 and Show1 for ExprF, in order to allow derived Read/Show on Expr

> instance Read1 ExprF where
>     liftReadsPrec rP rL d
>         = readParen (d > app_prec)
>           (\r ->
>            case lex r of
>              [("Automaton",s)]
>                  -> [ (Automaton x, t)
>                     | (x,t) <- readsPrec (app_prec + 1) s]
>              [("Concatenation",s)] -> goN Concatenation s
>              [("Conjunction",s)]   -> goN Conjunction s
>              [("Disjunction",s)]   -> goN Conjunction s
>              [("Domination",s)]    -> goN Domination s
>              [("DownClose",s)]     -> goU DownClose s
>              [("Factor",s)]
>                  -> [ (Factor x, t)
>                     | (x,t) <- readsPrec (app_prec + 1) s]
>              [("Infiltration",s)]  -> goN Infiltration s
>              [("Iteration",s)]     -> goU Iteration s
>              [("Negation",s)]      -> goU Negation s
>              [("Neutralize",s)]
>                  -> [ (Neutralize x y, u)
>                     | (x, t) <- readsPrec (app_prec + 1) s
>                     , (y, u) <- rP (app_prec + 1) t]
>              [("Reversal",s)]      -> goU Reversal s
>              [("Shuffle",s)]       -> goN Shuffle s
>              [("StrictOrder",s)]   -> goN StrictOrder s
>              [("Tierify",s)]
>                  -> [ (Tierify x y, u)
>                     | (x, t) <- readsPrec (app_prec + 1) s
>                     , (y, u) <- rP (app_prec + 1) t]
>              [("QuotientL",s)]     -> goN QuotientL s
>              [("QuotientR",s)]     -> goN QuotientR s
>              [("UpClose",s)]       -> goU UpClose s
>              [("Variable",s)]
>                  -> [ (Variable x, t)
>                     | (x,t) <- readsPrec (app_prec + 1) s]
>              _                     -> []
>           )
>         where app_prec = 10
>               goN f s = [(f xs, t) | (xs, t) <- rL s]
>               goU f s = [(f x,  t) | (x,  t) <- rP (app_prec + 1) s]

> instance Show1 ExprF where
>     liftShowsPrec showP showL d e
>         = case e of
>             Automaton x
>                 -> showParen (d > app_prec)
>                    $ showString "Automaton " . showsPrec (app_prec+1) x
>             Concatenation xs -> goL "Concatenation " xs
>             Conjunction xs   -> goL "Conjunction " xs
>             Disjunction xs   -> goL "Disjunction " xs
>             Domination xs    -> goL "Domination " xs
>             DownClose x      -> go1 "DownClose " x
>             Factor x
>                 -> showParen (d > app_prec)
>                    $ showString "Factor " . showsPrec (app_prec+1) x
>             Infiltration xs  -> goL "Infiltration " xs
>             Iteration x      -> go1 "Iteration " x
>             Negation x       -> go1 "Negation " x
>             Neutralize s x
>                 -> showParen (d > app_prec)
>                    $ showString "Neutralize "
>                      . showsPrec (app_prec+1) s
>                      . showP (app_prec+1) x
>             Reversal x       -> go1 "Reversal " x
>             Shuffle xs       -> goL "Shuffle " xs
>             StrictOrder xs   -> goL "StrictOrder " xs
>             Tierify s x
>                 -> showParen (d > app_prec)
>                    $ showString "Neutralize "
>                      . showsPrec (app_prec+1) s
>                      . showP (app_prec+1) x
>             QuotientL xs     -> goL "QuotientL " xs
>             QuotientR xs     -> goL "QuotientR " xs
>             UpClose x        -> go1 "UpClose " x
>             Variable x
>                 -> showParen (d > app_prec)
>                    $ showString "Variable " . showString x
>         where app_prec = 10
>               goL s xs = showParen (d > app_prec)
>                          $ showString s . showL xs
>               go1 s x  = showParen (d > app_prec)
>                          $ showString s . showP (app_prec + 1) x
