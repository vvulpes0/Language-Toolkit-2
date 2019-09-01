> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module:    LTK.Porters.Pleb
> Copyright: (c) 2018-2019 Dakotah Lambert
> License:   MIT

> The (P)iecewise / (L)ocal (E)xpression (B)uilder.
> This module defines a parser for a representation of
> logical formulae over subsequence- and adjacency-factors,
> as well as a mechanism for evaluating (creating an 'FSA' from)
> the resulting expression tree.

> There are two special variables:
> 
> * @it@ describes the most recent expression, and
> 
> * @universe@ collects all symbols used.
> -}
> module LTK.Porters.Pleb ( Dictionary
>                         , Parse(..)
>                         , Env
>                         , Expr
>                         , SymSet
>                         , Token
>                         , compileEnv
>                         , groundEnv
>                         , insertExpr
>                         , fromAutomaton
>                         , fromSemanticAutomaton
>                         , makeAutomaton
>                         , doStatements
>                         , parseExpr
>                         , readPleb
>                         , restrictUniverse
>                         , tokenize) where

> import Control.Applicative ( Applicative, Alternative
>                            , empty, many, pure, some, (<*>), (<|>))
> import Data.Char (isLetter, isSpace)
> import Data.Foldable (asum)
> import Data.Functor ((<$>))
> import Data.Monoid (mconcat)
> import Data.Set (Set)
> import qualified Data.Set as Set

> import LTK.FSA
> import LTK.Factors (buildLiteral, Factor(..), required)

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
>     where isDelim c = matchingDelimiter c /= c

> -- |The environment: defined sets of symbols, defined expressions, and
> -- possibly a value for the special variable @(it)@.
> type Env = (Dictionary SymSet, Dictionary Expr, Maybe Expr)

> -- |An expression, the root of an expression tree.
> data Expr
>     = NAry NAryExpr
>     | Unary UnaryExpr
>     | Factor PLFactor
>     | Automaton (FSA Integer (Maybe String))
>       deriving (Eq, Ord, Read, Show)

> -- |A subexpression that consists of an n-ary operator and its operands.
> data NAryExpr
>     = Concatenation [Expr]
>     | Conjunction   [Expr]
>     | Disjunction   [Expr]
>     | Domination    [Expr]
>       deriving (Eq, Ord, Read, Show)

> -- |A subexpression that consists of a unary operator and its operand.
> data UnaryExpr
>     = Iteration Expr
>     | Negation Expr
>     | Tierify [SymSet] Expr
>       deriving (Eq, Ord, Read, Show)

> -- |A subexpression representing a single Piecewise-Local factor.
> data PLFactor
>     = PLFactor Bool Bool [[SymSet]]
>       deriving (Eq, Ord, Read, Show)

> -- |A set of symbols.
> type SymSet = Set String

> -- |Parse an input string and create a stringset-automaton from the result.
> -- If there is an error while parsing, the result is the string "no parse".
> readPleb :: String -> Either String (FSA Integer String)
> readPleb = maybe (Left "no parse") (Right . desemantify) .
>            either (const Nothing) (makeAutomaton . fst) .
>            doParse (parseStatements (Set.empty, Set.empty, Nothing)) .
>            tokenize

> -- |Parse an input string and update the environment
> -- according to the result of the parse.
> doStatements :: Env -> String -> Env
> doStatements d str  =  either (const d) f .
>                        doParse (parseStatements d) $
>                        tokenize str
>     where f (x, [])  =  x
>           f _        =  d

> -- |Add a new expression to the environment, call it "@(it)@".
> insertExpr :: Env -> Expr -> Env
> insertExpr (dict, subexprs, _) e = doStatements
>                                    (dict, define "it" e subexprs, Just e)
>                                    "= it it"

> -- |Transform all saved expressions into automata to prevent reevaluation.
> compileEnv :: Env -> Env
> compileEnv (dict, subexprs, e) = (dict, tmap (mapsnd f) subexprs, f <$> e)
>     where f = Automaton . renameStates . minimize . automatonFromExpr

> -- |Convert saved automata from descriptions of constraints to
> -- descriptions of stringsets.
> -- This action effectively removes metadata describing constraint types
> -- from the environment.
> groundEnv :: Env -> Env
> groundEnv (dict, subexprs, e) = (dict, tmap (mapsnd f) subexprs, f <$> e)
>     where f = Automaton . renameSymbolsBy Just . renameStates . minimize .
>               desemantify .
>               semanticallyExtendAlphabetTo universe .
>               automatonFromExpr
>           universe = either (const Set.empty) id (definition "universe" dict)

> -- |Remove any symbols not present in @(universe)@ from the environment.
> restrictUniverse :: Env -> Env
> restrictUniverse (dict, subexprs, v) = ( keep (not . isEmpty . snd) $
>                                          tmap (mapsnd restrictUniverseS) dict
>                                        , tmap (mapsnd restrictUniverseE) subexprs
>                                        , restrictUniverseE <$> v
>                                        )
>     where universe = either (const Set.empty) id (definition "universe" dict)
>           restrictUniverseS = intersection universe
>           restrictUniverseE e =
>               case e of
>                 NAry (Concatenation es)   ->  f Concatenation es
>                 NAry (Conjunction es)     ->  f Conjunction es
>                 NAry (Disjunction es)     ->  f Disjunction es
>                 NAry (Domination es)      ->  f Domination es
>                 Unary (Iteration ex)      ->  g Iteration ex
>                 Unary (Negation ex)       ->  g Negation ex
>                 Unary (Tierify ts ex)     ->  g
>                                               (Tierify
>                                                (tmap restrictUniverseS ts))
>                                               ex
>                 Factor (PLFactor h t ps)  ->  fixFactor h t $
>                                               tmap (tmap restrictUniverseS)
>                                               ps
>                 Automaton x               ->  Automaton $
>                                               contractAlphabetTo
>                                               (insert Nothing
>                                                (tmap Just universe))
>                                               x
>           f t es = NAry (t $ tmap restrictUniverseE es)
>           g t e  = Unary (t $ restrictUniverseE e)
>           fixFactor h t ps
>               | any (any isEmpty) ps
>                   = Unary (Negation (Factor (PLFactor False False [])))
>                     -- <> and ~<> are essentially True and False
>               | otherwise = Factor (PLFactor h t ps)

> -- |Create an 'FSA' from an expression tree and environment,
> -- complete with metadata regarding the constraint(s) it represents.
> makeAutomaton :: Env -> Maybe (FSA Integer (Maybe String))
> makeAutomaton (dict, _, e) = normalize <$>
>                              semanticallyExtendAlphabetTo symsets <$>
>                              automatonFromExpr <$> e
>     where symsets = either (const Set.empty) id
>                     (definition "universe" dict)

The properties of semantic automata are used here to prevent having to
pass alphabet information to the individual constructors, which in turn
prevents having to descend through the tree to find this information.

> -- |Create an 'FSA' from an expression tree,
> -- complete with metadata regarding the constraint(s) it represents.
> automatonFromExpr :: Expr -> FSA Integer (Maybe String)
> automatonFromExpr e
>     = case e of
>         NAry (Concatenation es) -> f mconcat es
>         NAry (Conjunction es)   -> f flatIntersection es
>         NAry (Disjunction es)   -> f flatUnion es
>         NAry (Domination es)    -> f (mconcat .
>                                       sepBy (totalWithAlphabet (singleton Nothing)))
>                                    es
>         Unary (Iteration ex)    -> renameStates . minimize . kleeneClosure $
>                                    automatonFromExpr ex
>         Unary (Negation ex)     -> complementDeterministic $
>                                    automatonFromExpr ex
>         Unary (Tierify ts ex)   -> tierify (unionAll ts) $
>                                    automatonFromExpr ex
>         Factor x                -> automatonFromPLFactor x
>         Automaton x             -> x
>     where f tl = renameStates . minimize . tl . automata
>           automata es  =  let a' = map automatonFromExpr es
>                           in map (semanticallyExtendAlphabetTo (bigAlpha a')) a'
>           bigAlpha     =  collapse (maybe id insert) Set.empty .
>                           collapse (union . alphabet) Set.empty

> automatonFromPLFactor :: PLFactor -> FSA Integer (Maybe String)
> automatonFromPLFactor (PLFactor h t pieces)
>     | isEmpty pieces  =  bl (Substring [] h t)
>     | isEmpty ps      =  bl (Substring p  h t)
>     | isPF            =  bl (Subsequence (concat (p:ps)))
>     | otherwise       =  renameStates . minimize . mconcat $ map bl lfs
>     where as           =  insert Nothing . tmap Just $
>                           unionAll (unionAll pieces)
>           bl           =  buildLiteral as . required
>           (p:ps)       =  tmap (tmap (tmap Just)) pieces
>           isPF         =  not h && not t &&
>                           all ((== (1 :: Integer)) . size) pieces
>           lfs          =  Substring p h False : lfs' ps
>           lfs' (x:[])  =  Substring x False t : lfs' []
>           lfs' (x:xs)  =  Substring x False False : lfs' xs
>           lfs' _       =  []

> usedSymbols :: Expr -> SymSet
> usedSymbols e = case e of
>                   NAry n       ->  usedSymbolsN n
>                   Unary u      ->  usedSymbolsU u
>                   Factor f     ->  usedSymbolsF f
>                   Automaton a  ->  collapse (maybe id insert) Set.empty
>                                    (alphabet a)
>     where usedSymbolsN (Concatenation es)  =  unionAll $ tmap usedSymbols es
>           usedSymbolsN (Conjunction es)    =  unionAll $ tmap usedSymbols es
>           usedSymbolsN (Disjunction es)    =  unionAll $ tmap usedSymbols es
>           usedSymbolsN (Domination es)     =  unionAll $ tmap usedSymbols es
>           usedSymbolsU (Iteration ex)      =  usedSymbols ex
>           usedSymbolsU (Negation ex)       =  usedSymbols ex
>           usedSymbolsU (Tierify ts ex)     =  union (unionAll ts)
>                                               (usedSymbols ex)
>           usedSymbolsF (PLFactor _ _ ps)   =  unionAll (unionAll ps)

> parseStatements :: Env -> Parse Env
> parseStatements (dict, subexprs, prev)
>  = asum $ [ start >> putFst <$>
>             (mkSyms <$> getName <*>
>              (unionAll <$>
>               parseDelimited ['(', '{']
>               (parseSeparated "," (parseSymSet dict))) <*>
>              pure dict) >>=
>             parseStatements
>           , start >>
>             (f False <$> getName <*> (Just <$> parseExpr dict subexprs)) >>=
>             parseStatements
>           , f True "it" <$> (Just <$> parseExpr dict subexprs)
>           , Parse $ \ts -> case ts of
>                              [] -> Right ((dict, subexprs, prev), [])
>                              _  -> Left "not finished"
>           ]
>    where getName = Parse $ \ts ->
>                    case ts of
>                      (TName n : ts') -> Right (n, ts')
>                      (x : _)         -> Left $
>                                         "could not find name at " ++
>                                         showParen True (shows x) ""
>                      _               -> Left "end of input looking for name"
>          start = eat "≝" [] <|> eat "=" []
>          putFst a = (a, subexprs, prev)
>          universe = either (const Set.empty) id (definition "universe" dict)
>          mkSyms name value = define "universe"
>                              (if name /= "universe"
>                               then union universe value
>                               else value) .
>                              define name value
>          f isL name me = let nd = maybe dict
>                                   (flip (define "universe") dict .
>                                    union universe .
>                                    usedSymbols)
>                                   me
>                          in ( nd
>                             , maybe subexprs (flip (define name) subexprs) me
>                             , if isL then me else prev)

> -- |Parse an expression from a 'Token' stream.
> parseExpr :: Dictionary SymSet -> Dictionary Expr -> Parse Expr
> parseExpr dict subexprs = asum
>                           [ NAry    <$>  parseNAryExpr dict subexprs
>                           , Unary   <$>  parseUnaryExpr dict subexprs
>                           , Factor  <$>  parsePLFactor dict subexprs
>                           , Parse expandVar
>                           ]
>     where expandVar (TName n : ts) = fmap (flip (,) ts) $
>                                      definition n subexprs
>           expandVar _              = Left "not a variable"

> parseNAryExpr :: Dictionary SymSet -> Dictionary Expr -> Parse NAryExpr
> parseNAryExpr dict subexprs
>     = (makeLifter
>        [ (["⋂", "∩", "/\\"],  Conjunction)
>        , (["⋃", "∪", "\\/"],  Disjunction)
>        , (["∙∙", "@@"],       Domination)
>        , (["∙" , "@" ],       Concatenation)
>        ] <*>
>        parseDelimited ['(', '{']
>        (parseSeparated "," (parseExpr dict subexprs)))

> parseUnaryExpr :: Dictionary SymSet -> Dictionary Expr -> Parse UnaryExpr
> parseUnaryExpr dict subexprs = (makeLifter
>                                 [ (["*", "∗"],       Iteration)
>                                 , (["¬", "~", "!"],  Negation)
>                                 ] <*>
>                                 parseExpr dict subexprs) <|>
>                                (Tierify <$> pt <*> parseExpr dict subexprs)
>     where pt = parseDelimited ['['] (parseSeparated "," (parseSymSet dict))

> parsePLFactor :: Dictionary SymSet -> Dictionary Expr -> Parse PLFactor
> parsePLFactor dict subexprs = combine ".." plGap <|>
>                               combine "‥" plGap <|>
>                               combine "." plCatenate <|>
>                               pplf
>     where combine s f = eat s (foldr1 f) <*>
>                         parseDelimited ['<', '⟨']
>                         (parseSeparated "," pplf)
>           pplf = parseBasicPLFactor dict <|>
>                  (Parse expandVar)
>           expandVar (TName n : ts)
>               = case v of
>                   Right (Factor x) -> Right (x, ts)
>                   _        -> Left "expression does not represent a factor"
>               where v = definition n subexprs
>           expandVar _              = Left "not a variable"

> parseBasicPLFactor :: Dictionary SymSet -> Parse PLFactor
> parseBasicPLFactor dict = (makeLifter
>                            [ (["⋊⋉", "%||%"], PLFactor True True)
>                            , (["⋊", "%|"], PLFactor True False)
>                            , (["⋉", "|%"], PLFactor False True)
>                            , ([""], PLFactor False False)
>                            ] <*>
>                            (parseDelimited ['<', '⟨']
>                             (parseSeparated "," (some (parseSymSet dict)) <|>
>                              Parse (\ts -> Right ([], ts)))))

> parseSymSet :: Dictionary SymSet -> Parse SymSet
> parseSymSet dict = Parse $ \xs ->
>                    case xs of
>                      (TName n : ts) ->
>                          fmap (flip (,) ts) (definition n dict)
>                      (TSymbol '/' : TName n : ts) ->
>                          Right . flip (,) ts $ singleton n
>                      (a:_) ->
>                            Left $ "cannot start a SymSet with " ++
>                            showParen True (shows a) ""
>                      _ -> Left "unexpected end of input in SymSet"

> makeLifter :: [([String], a)] -> Parse a
> makeLifter = asum . concatMap (map (uncurry eat) . f)
>     where f ([], _)      =  []
>           f ((x:xs), g)  =  (x, g) : f (xs, g)

> eat :: String -> a -> Parse a
> eat str f = Parse $ \ts -> if isPrefixOf ts (tmap TSymbol str)
>                            then Right (f, drop (length str) ts)
>                            else Left $ ""
>                            -- else Left $ "could not find " ++ show str

> parseDelimited :: [Char] -> Parse [a] -> Parse [a]
> parseDelimited ds pl = parseOpeningDelimiter ds >>=
>                        (\d -> (++) <$> pl <*> parseClosingDelimiter d)

> parseOpeningDelimiter :: [Char] -> Parse Char
> parseOpeningDelimiter ds = Parse openingDelimiter
>     where openingDelimiter (TSymbol x : ts)
>               | isIn ds x  = Right (x, ts)
>               | otherwise  = Left $
>                              "invalid opening delimiter: " ++
>                              show x
>           openingDelimiter _
>               = Left "unexpected end of input looking for opening delimiter"

> parseClosingDelimiter :: Char -> Parse [a]
> parseClosingDelimiter = flip eat [] . singleton .  matchingDelimiter

> parseSeparated :: String -> Parse a -> Parse [a]
> parseSeparated string p = (:) <$> p <*> (many (eat string [] >> p))



> plCatenate :: PLFactor -> PLFactor -> PLFactor
> plCatenate (PLFactor h _ xs) (PLFactor _ t ys) = PLFactor h t (pc xs ys)
>     where pc [] bs          =  bs
>           pc (a:[]) []      =  [a]
>           pc (a:[]) (b:bs)  =  (a ++ b) : bs
>           pc (a:as) bs      =  a : pc as bs

> plGap :: PLFactor -> PLFactor -> PLFactor
> plGap (PLFactor h _ xs) (PLFactor _ t ys) = PLFactor h t (xs ++ ys)



> -- |An association between names and values.
> type Dictionary a = Set (String, a)

> define :: (Ord a) => String -> a -> Dictionary a -> Dictionary a
> define name value = insert (name, value) . keep ((/= name) . fst)

> definition :: (Ord a) => String -> Dictionary a -> Either String a
> definition a = maybe
>                (Left $ "undefined variable \"" ++ a ++ "\"")
>                Right .
>                lookupMin . tmap snd . keep ((== a) . fst)
>     where lookupMin xs
>               | xs == Set.empty = Nothing
>               | otherwise       = Just (Set.findMin xs)

> -- |The base type for a combinatorial parser.
> newtype Parse a = Parse {
>       doParse :: [Token] -> Either String (a, [Token])
>     }

> instance Functor Parse where
>     fmap g (Parse f) = Parse (fmap (mapfst g) . f)

> instance Applicative Parse where
>     pure x   =  Parse (Right . (,) x . id)
>     f <*> x  =  Parse $ \s0 ->
>                 let e = doParse f s0
>                 in case e of
>                      Left s  ->  Left s
>                      Right (g, s1) ->  fmap (mapfst g) $ doParse x s1

> instance Alternative Parse where
>     empty = Parse (const (Left {- "no parse" -} ""))
>     p <|> q = Parse $ \ts ->
>               let e = doParse p ts
>               in case e of
>                    Left s -> either (Left . f s) Right (doParse q ts)
>                    _      -> e
>         where f s1 s2 = unlines $ concatMap (filter (/= "") . lines) [s1, s2]

> instance Monad Parse where
>     return x = Parse (Right . (,) x . id)
>     p >>= f = Parse $ \s0 ->
>               let e = doParse p s0
>               in case e of
>                    Left s         ->  Left s
>                    Right (a, s1)  ->  doParse (f a) s1



> -- |Generate an expression (sub)tree from an 'FSA' that
> -- contains metadata regarding the constraint(s) it represents.
> fromSemanticAutomaton :: FSA Integer (Maybe String) -> Expr
> fromSemanticAutomaton = Automaton

> -- |Generate an expression (sub)tree from an 'FSA'.
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

> mapsnd :: (b -> c) -> (a, b) -> (a, c)
> mapsnd f (a, b) = (a, f b)

> matchingDelimiter :: Char -> Char
> matchingDelimiter x = head
>                       ((map snd (keep ((== x) . fst) delimiters)) ++
>                        (map fst (keep ((== x) . snd) delimiters)) ++
>                        [x])
>     where delimiters = [ ('<', '>')
>                        , ('⟨', '⟩')
>                        , ('(', ')')
>                        , ('[', ']')
>                        , ('{', '}')
>                        ]

> sepBy :: a -> [a] -> [a]
> sepBy x (a:b:as) = a : x : sepBy x (b:as)
> sepBy _ as       = as
