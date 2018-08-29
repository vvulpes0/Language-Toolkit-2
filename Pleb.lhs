> module Pleb ( Dictionary
>             , Parse(..)
>             , Env
>             , Expr
>             , SymSet
>             , makeAutomaton
>             , doStatements
>             , parseExpr
>             , readPleb
>             , tokenize) where

> import Control.Applicative (Applicative(..), Alternative(..))
> import Data.Char (isLetter, isSpace)
> import Data.Foldable (asum)
> import Data.Functor ((<$>))
> import Data.Set (Set, lookupMin)
> import qualified Data.Set as Set

> import FSA
> import Factors (buildLiteral, Factor(..), required)

> data Token = TSymbol Char
>            | TName String
>              deriving (Eq, Ord, Read, Show)

> tokenize  :: String -> [Token]
> tokenize "" = []
> tokenize (x:xs)
>     | x == '#'    =  tokenize (dropWhile (/= '\n') xs)
>     | isSpace x   =  tokenize (dropWhile isSpace xs)
>     | isLetter x  =  uncurry (:) . mapfst TName . fmap tokenize $
>                      break (\s -> s == ',' || isDelim s || isSpace s) (x:xs)
>     | otherwise   =  TSymbol x : tokenize xs
>     where isDelim c = matchingDelimiter c /= c

> type Env = (Dictionary SymSet, Dictionary Expr, Maybe Expr)
> data Expr
>     = NAry NAryExpr
>     | Unary UnaryExpr
>     | Factor PFactor
>       deriving (Eq, Ord, Read, Show)
> data NAryExpr
>     = Concatenation [Expr]
>     | Conjunction   [Expr]
>     | Disjunction   [Expr]
>     | PRelation     [Expr]
>       deriving (Eq, Ord, Read, Show)
> data UnaryExpr
>     = Iteration Expr
>     | Negation Expr
>       deriving (Eq, Ord, Read, Show)
> data PFactor
>     = PieceFactor Sequence
>     | LocalFactor AnchoredSequence
>       deriving (Eq, Ord, Read, Show)
> data AnchoredSequence
>     = Word Sequence
>     | Head Sequence
>     | Tail Sequence
>     | Free Sequence
>       deriving (Eq, Ord, Read, Show)
> type Sequence = [SymSet]
> type SymSet = Set String

> readPleb :: String -> FSA Integer String
> readPleb = maybe (error "no parse") id .
>            either (error) (makeAutomaton . fst) .
>            doParse (parseStatements (Set.empty, Set.empty, Nothing)) .
>            tokenize

> doStatements :: Env -> String -> Env
> doStatements d str  =  either (const d) f .
>                        doParse (parseStatements d) $
>                        tokenize str
>     where f (x, [])  =  x
>           f _        =  d

> makeAutomaton :: Env -> Maybe (FSA Integer String)
> makeAutomaton (dict, _, e) = normalize <$> automatonFromExpr alphabet <$> e
>     where alphabet = union (maybe Set.empty usedSymbols e)
>                      (unionAll $ tmap snd dict)

> automatonFromExpr :: Set String -> Expr -> FSA Integer String
> automatonFromExpr as e
>     = case e of
>         NAry (Concatenation es) -> f mconcat es
>         NAry (Conjunction es)   -> f flatIntersection es
>         NAry (Disjunction es)   -> f flatUnion es
>         NAry (PRelation es)     -> f (mconcat .
>                                       sepBy (totalWithAlphabet as)) es
>         Unary (Iteration e)     -> renameStates . minimize . kleeneClosure $
>                                    automatonFromExpr as e
>         Unary (Negation e)      -> complementDeterministic $
>                                    automatonFromExpr as e
>         Factor (PieceFactor s)  -> buildLiteral as . required $
>                                    Subsequence s
>         Factor (LocalFactor x)  -> buildLiteral as . required $
>                                    g x
>     where f tl = renameStates . minimize . tl . map (automatonFromExpr as)
>           g (Word as) = Substring as True   True
>           g (Head as) = Substring as True   False
>           g (Tail as) = Substring as False  True
>           g (Free as) = Substring as False  False

> usedSymbols :: Expr -> Set String
> usedSymbols e = case e of
>                   NAry n    ->  usedSymbolsN n
>                   Unary u   ->  usedSymbolsU u
>                   Factor f  ->  usedSymbolsF f
>     where usedSymbolsN (Concatenation es)  =  unionAll $ tmap usedSymbols es
>           usedSymbolsN (Conjunction es)    =  unionAll $ tmap usedSymbols es
>           usedSymbolsN (Disjunction es)    =  unionAll $ tmap usedSymbols es
>           usedSymbolsN (PRelation es)      =  unionAll $ tmap usedSymbols es
>           usedSymbolsU (Iteration e)       =  usedSymbols e
>           usedSymbolsU (Negation e)        =  usedSymbols e
>           usedSymbolsF (PieceFactor pf)    =  unionAll pf
>           usedSymbolsF (LocalFactor f)     =  usedSymbolsA f
>           usedSymbolsA (Word s)            =  unionAll s
>           usedSymbolsA (Head s)            =  unionAll s
>           usedSymbolsA (Tail s)            =  unionAll s
>           usedSymbolsA (Free s)            =  unionAll s

> parseStatements :: Env -> Parse Env
> parseStatements (dict, subexprs, last)
>  = asum $ [ start >> putFst <$>
>             (define <$> getName <*>
>              (unionAll <$>
>               parseDelimited ['(', '{']
>               (parseSeparated "," (parseSymSet dict))) <*>
>              pure dict) >>=
>             parseStatements
>           , start >> putSnd <$>
>             (define <$> getName <*> parseExpr dict subexprs <*>
>              pure subexprs) >>=
>             parseStatements
>           , f <$> (Just <$> parseExpr dict subexprs)
>           , Parse $ \ts -> case ts of
>                              [] -> Right ((dict, subexprs, last), [])
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
>          putFst a = (a, subexprs, last)
>          putSnd b = (dict, b, last)
>          f me = (dict
>                 , maybe subexprs (flip (define "it") subexprs) me
>                 , me)

> parseExpr :: Dictionary SymSet -> Dictionary Expr -> Parse Expr
> parseExpr dict subexprs = asum
>                           [ NAry    <$>  parseNAryExpr dict subexprs
>                           , Unary   <$>  parseUnaryExpr dict subexprs
>                           , Factor  <$>  parseFactor dict
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
>        , (["‥", ".."],        PRelation)
>        , ([".", "⋄"],         Concatenation)
>        ] <*>
>        parseDelimited ['(', '{']
>        (parseSeparated "," (parseExpr dict subexprs)))

> parseUnaryExpr :: Dictionary SymSet -> Dictionary Expr -> Parse UnaryExpr
> parseUnaryExpr dict subexprs = (makeLifter
>                                 [ (["*", "∗"],       Iteration)
>                                 , (["¬", "~", "!"],  Negation)
>                                 ] <*>
>                                 parseExpr dict subexprs)

> parseFactor :: Dictionary SymSet -> Parse PFactor
> parseFactor dict = (eat ".." PieceFactor <*> parseSequence dict) <|>
>                    (eat "‥" PieceFactor <*> parseSequence dict) <|>
>                    (LocalFactor <$> parseAnchoredSequence dict)

> parseAnchoredSequence :: Dictionary SymSet -> Parse AnchoredSequence
> parseAnchoredSequence dict = (makeLifter
>                               [ (["⋊⋉", "%][%"], Word)
>                               , (["⋊", "%]"], Head)
>                               , (["⋉", "[%"], Tail)
>                               , ([""], Free)
>                               ] <*>
>                               parseSequence dict)

> parseSequence :: Dictionary SymSet -> Parse Sequence
> parseSequence dict = parseDelimited ['<', '⟨'] (many (parseSymSet dict))

> parseSymSet :: Dictionary SymSet -> Parse SymSet
> parseSymSet dict = Parse $ \xs ->
>                    case xs of
>                      (TName n : ts) ->
>                          fmap (flip (,) ts) (definition n dict)
>                      (TSymbol '/' : TName n : ts) ->
>                          Right . flip (,) ts $ singleton n
>                      (a:as) ->
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
>                            else Left $ "could not find " ++ show str

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



> type Dictionary a = Set (String, a)

> define :: (Ord a) => String -> a -> Dictionary a -> Dictionary a
> define name value = insert (name, value) . keep ((/= name) . fst)

> definition :: (Ord a) => String -> Dictionary a -> Either String a
> definition a = maybe
>                (Left $ "undefined variable \"" ++ a ++ "\"")
>                Right .
>                lookupMin . tmap snd . keep ((== a) . fst)

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
>     empty = Parse (const (Left "no parse"))
>     p <|> q = Parse $ \ts ->
>               let e = doParse p ts
>               in case e of
>                    Left s -> doParse q ts
>                    _      -> e

> instance Monad Parse where
>     return x = Parse (Right . (,) x . id)
>     p >>= f = Parse $ \s0 ->
>               let e = doParse p s0
>               in case e of
>                    Left s         ->  Left s
>                    Right (a, s1)  ->  doParse (f a) s1



> isPrefixOf :: Eq a => [a] -> [a] -> Bool
> isPrefixOf _ []  =  True
> isPrefixOf [] _  =  False
> isPrefixOf (a:as) (b:bs)
>     | a == b     =  isPrefixOf as bs
>     | otherwise  =  False

> mapfst :: (a -> b) -> (a, c) -> (b, c)
> mapfst f (a, c) = (f a, c)

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
> sepBy x as       = as
