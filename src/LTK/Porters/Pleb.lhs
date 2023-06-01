> {-# OPTIONS_HADDOCK show-extensions #-}
> {-# Language CPP #-}

#if !defined(MIN_VERSION_base)
# define MIN_VERSION_base(a,b,c) 0
#endif

> {-|
> Module:    LTK.Porters.Pleb
> Copyright: (c) 2018-2022 Dakotah Lambert
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
>        , doStatements
>        , parseExpr
>        , readPleb
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
> import Data.Set (Set)
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
>     | Infiltration  [Expr]
>     | Shuffle       [Expr]
>     | QuotientL     [Expr] -- ^@since 1.0
>     | QuotientR     [Expr] -- ^@since 1.0
>       deriving (Eq, Ord, Read, Show)

> -- |A subexpression that consists of a unary operator and its operand.
> data UnaryExpr
>     = DownClose Expr -- ^@since 1.0
>     | Iteration Expr
>     | Negation Expr
>     | Neutralize [SymSet] Expr
>     | Tierify [SymSet] Expr
>     | UpClose Expr
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
> insertExpr (dict, subexprs, _) e
>     = doStatements (dict, define "it" e subexprs, Just e) "= it it"

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
>     where f = Automaton .
>               renameSymbolsBy Just . renameStates . minimize .
>               desemantify . semanticallyExtendAlphabetTo universe .
>               automatonFromExpr
>           universe = either (const Set.empty) id (definition "universe" dict)

=====
Note:
=====

@restrictUniverse@ previously deleted symbolsets bound to the empty set.
However, it is now possible to manually define the empty set: [/a,/b].
Therefore, this cleanup step has been removed.

> -- |Remove any symbols not present in @(universe)@ from the environment.
> restrictUniverse :: Env -> Env
> restrictUniverse (dict, subexprs, v)
>     = ( tmap (mapsnd restrictUniverseS) dict
>       , tmap (mapsnd restrictUniverseE) subexprs
>       , restrictUniverseE <$> v
>       )
>     where universe           =  either (const Set.empty) id $
>                                 definition "universe" dict
>           restrictUniverseS  =  intersection universe
>           restrictUniverseE e
>               = case e
>                 of Automaton x
>                        ->  Automaton $
>                            contractAlphabetTo
>                            (insert Nothing (tmap Just universe))
>                            x
>                    Factor (PLFactor h t ps)
>                        -> fixFactor h t $ tmap (tmap restrictUniverseS) ps
>                    NAry (Concatenation es)  ->  f Concatenation es
>                    NAry (Conjunction es)    ->  f Conjunction es
>                    NAry (Disjunction es)    ->  f Disjunction es
>                    NAry (Domination es)     ->  f Domination es
>                    NAry (Infiltration es)   ->  f Infiltration es
>                    NAry (Shuffle es)        ->  f Shuffle es
>                    NAry (QuotientL es)      ->  f QuotientL es
>                    NAry (QuotientR es)      ->  f QuotientR es
>                    Unary (DownClose ex)     ->  g DownClose ex
>                    Unary (Iteration ex)     ->  g Iteration ex
>                    Unary (Negation ex)      ->  g Negation ex
>                    Unary (Neutralize ts ex)
>                        -> g (Neutralize (tmap restrictUniverseS ts)) ex
>                    Unary (Tierify ts ex)
>                        -> g (Tierify (tmap restrictUniverseS ts)) ex
>                    Unary (UpClose ex)       ->  g UpClose ex
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
> makeAutomaton (dict, _, e) = normalize
>                              . semanticallyExtendAlphabetTo symsets
>                              . automatonFromExpr <$> e
>     where symsets = either (const Set.empty) id
>                     $ definition "universe" dict

The properties of semantic automata are used here to prevent having to
pass alphabet information to the individual constructors, which in turn
prevents having to descend through the tree to find this information.

> -- |Create an 'FSA' from an expression tree,
> -- complete with metadata regarding the constraint(s) it represents.
> automatonFromExpr :: Expr -> FSA Integer (Maybe String)
> automatonFromExpr e
>     = case e
>       of Automaton x             -> x
>          Factor x                -> automatonFromPLFactor x
>          NAry (Concatenation es) -> f emptyStr mconcat es
>          NAry (Conjunction es)   -> f univLang flatIntersection es
>          NAry (Disjunction es)   -> f emptyLanguage flatUnion es
>          NAry (Domination es)
>              -> f emptyStr
>                 (mconcat .
>                  intersperse (totalWithAlphabet (singleton Nothing))
>                 ) es
>          NAry (Infiltration es)  -> f emptyStr flatInfiltration es
>          NAry (Shuffle es)       -> f emptyStr flatShuffle es
>          NAry (QuotientL es)     -> f emptyStr ql es
>          NAry (QuotientR es)     -> f emptyStr qr es
>          Unary (DownClose ex)
>              -> renameStates . minimize . subsequenceClosure $
>                 automatonFromExpr ex
>          Unary (Iteration ex)
>              -> renameStates . minimize . kleeneClosure $
>                 automatonFromExpr ex
>          Unary (Negation ex)
>              -> complementDeterministic $ automatonFromExpr ex
>          Unary (Neutralize ts ex)
>              -> renameStates . minimize . determinize
>                 . neutralize (Set.mapMonotonic Just $ unionAll ts)
>                 $ automatonFromExpr ex
>          Unary (Tierify ts ex)
>              -> tierify (unionAll ts) $ automatonFromExpr ex
>          Unary (UpClose ex)
>              -> renameStates . minimize . determinize . loopify $
>                 automatonFromExpr ex
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

> automatonFromPLFactor :: PLFactor -> FSA Integer (Maybe String)
> automatonFromPLFactor (PLFactor h t pieces)
>     = case tmap (tmap (tmap Just)) pieces of
>         []      ->  bl (Substring [] h t)
>         [p]     ->  bl (Substring p  h t)
>         (p:ps)  ->  if isPF
>                     then bl . Subsequence $ concat (p:ps)
>                     else renameStates . minimize . mconcat
>                          $ map bl lfs
>                         where lfs  =  Substring p h False : lfs' ps
>     where as           =  insert Nothing . tmap Just $
>                           unionAll (unionAll pieces)
>           bl           =  buildLiteral as . required
>           isPF         =  not h && not t &&
>                           all ((==) [()] . map (const ())) pieces
>           lfs' [x]     =  Substring x False t : lfs' []
>           lfs' (x:xs)  =  Substring x False False : lfs' xs
>           lfs' _       =  []

> usedSymbols :: Expr -> SymSet
> usedSymbols e = case e
>                 of Automaton a  ->  collapse (maybe id insert) Set.empty $
>                                     alphabet a
>                    Factor f     ->  usedSymbolsF f
>                    NAry n       ->  usedSymbolsN n
>                    Unary u      ->  usedSymbolsU u
>     where us = collapse (union . usedSymbols) Set.empty
>           usedSymbolsN (Concatenation es)  =  us es
>           usedSymbolsN (Conjunction es)    =  us es
>           usedSymbolsN (Disjunction es)    =  us es
>           usedSymbolsN (Domination es)     =  us es
>           usedSymbolsN (Infiltration es)   =  us es
>           usedSymbolsN (Shuffle es)        =  us es
>           usedSymbolsN (QuotientL es)      =  us es
>           usedSymbolsN (QuotientR es)      =  us es
>           usedSymbolsU (DownClose ex)      =  usedSymbols ex
>           usedSymbolsU (Iteration ex)      =  usedSymbols ex
>           usedSymbolsU (Negation ex)       =  usedSymbols ex
>           usedSymbolsU (Neutralize ts ex)  =  Set.union
>                                               (usedSymbols ex)
>                                               (unionAll ts)
>           usedSymbolsU (Tierify ts _)      =  unionAll ts
>           usedSymbolsU (UpClose ex)        =  usedSymbols ex
>           usedSymbolsF (PLFactor _ _ ps)   =  unionAll $ unionAll ps

> parseStatements :: Env -> Parse Env
> parseStatements (dict, subexprs, prev)
>     = asum
>       [ start
>         >> (f False <$> getName <*> (Just <$> parseExpr dict subexprs))
>         >>= parseStatements
>       , start >> putFst
>         <$> (mkSyms <$> getName <*> parseSymExpr dict <*> pure dict)
>         >>= parseStatements
>       , f True "it" . Just <$> parseExpr dict subexprs
>       , Parse $ \ts ->
>         case ts
>         of []  ->  Right ((dict, subexprs, prev), [])
>            _   ->  Left "not finished"
>       ]
>    where getName
>              = Parse $ \ts ->
>                case ts
>                of (TName n : ts') -> Right (n, ts')
>                   (x : _)
>                       -> Left $
>                          "could not find name at " ++
>                          showParen True (shows x) ""
>                   _ -> Left "end of input looking for name"
>          start = eat "≝" [] <|> eat "=" []
>          putFst a = (a, subexprs, prev)
>          universe = either (const Set.empty) id $
>                     definition "universe" dict
>          mkSyms name value
>              = define "universe"
>                (if name /= "universe"
>                 then universe `union` value
>                 else value
>                ) . define name value
>          f isL name me
>              = let nd = maybe
>                         dict
>                         (flip (define "universe") dict .
>                          union universe .
>                          usedSymbols
>                         )
>                         me
>                in ( nd
>                   , maybe subexprs (flip (define name) subexprs) me
>                   , if isL then me else prev)

> -- |Parse an expression from a 'Token' stream.
> parseExpr :: Dictionary SymSet -> Dictionary Expr -> Parse Expr
> parseExpr dict subexprs = asum
>                           [ parseNAryExpr dict subexprs
>                           , parseUnaryExpr dict subexprs
>                           , Factor  <$>  parsePLFactor dict subexprs
>                           , Parse expandVar
>                           ]
>     where expandVar (TName n : ts)
>               = flip (,) ts <$> definition n subexprs
>           expandVar _ = Left "not a variable"

> parseNAryExpr :: Dictionary SymSet -> Dictionary Expr -> Parse Expr
> parseNAryExpr dict subexprs
>     = makeLifter
>       [ (["⋀", "⋂", "∧", "∩", "/\\"],  NAry . Conjunction)
>       , (["⋁", "⋃", "∨", "∪", "\\/"],  NAry . Disjunction)
>       , (["\\\\"],                     NAry . QuotientL)
>       , (["//"],                       NAry . QuotientR)
>       , (["∙∙", "@@"],                 NAry . Domination)
>       , (["∙" , "@" ],                 NAry . Concatenation)
>       , (["⧢", "|_|_|"],               NAry . Shuffle)
>       , (["⇑", ".^."],                 NAry . Infiltration)
>       ] <*> pd
>     where pd = parseEmpty
>                <|> parseDelimited ['(', '{']
>                    (parseSeparated "," $ parseExpr dict subexprs)
>           parseEmpty = Parse $ \xs ->
>                        case xs of
>                          (TSymbol '(':TSymbol ')':ts) -> Right ([], ts)
>                          (TSymbol '{':TSymbol '}':ts) -> Right ([], ts)
>                          _ -> Left "not an empty expr"

> parseUnaryExpr :: Dictionary SymSet -> Dictionary Expr -> Parse Expr
> parseUnaryExpr dict subexprs
>     = (makeLifter
>        [ (["↓", "$"],       Unary . DownClose)
>        , (["↑", "^"],       Unary . UpClose)
>        , (["*", "∗"],       Unary . Iteration)
>        , (["+"],            NAry  . plus)
>        , (["¬", "~", "!"],  Unary . Negation)
>        ] <*> parseExpr dict subexprs
>       ) <|> (Unary <$> (Tierify <$> pt <*> parseExpr dict subexprs))
>         <|> (Unary <$> (Neutralize <$> pn <*> parseExpr dict subexprs))
>     where pt = parseDelimited ['[']
>                (parseSeparated "," (parseSymExpr dict))
>           pn = parseDelimited ['|']
>                (parseSeparated "," (parseSymExpr dict))
>           plus e = Concatenation [e, Unary $ Iteration e]

> parsePLFactor :: Dictionary SymSet -> Dictionary Expr -> Parse PLFactor
> parsePLFactor dict subexprs
>     = combine ".." plGap <|>
>       combine "‥" plGap <|>
>       combine "." plCatenate <|>
>       pplf
>     where combine s f = eat s (foldr1 f) <*>
>                         parseDelimited ['<', '⟨']
>                         (parseSeparated "," pplf)
>           pplf = parseBasicPLFactor dict <|> Parse expandVar
>           expandVar (TName n : ts)
>               = case v
>                 of Right (Factor x) -> Right (x, ts)
>                    _ -> Left "expression does not represent a factor"
>               where v = definition n subexprs
>           expandVar _ = Left "not a variable"

> parseBasicPLFactor :: Dictionary SymSet -> Parse PLFactor
> parseBasicPLFactor dict
>     = makeLifter
>       [ (["⋊⋉", "%||%"], PLFactor True True)
>       , (["⋊", "%|"], PLFactor True False)
>       , (["⋉", "|%"], PLFactor False True)
>       , ([""], PLFactor False False)
>       ]
>       <*> parseDelimited ['<', '⟨']
>           (parseSeparated "," $ some (parseSymExpr dict)
>            <|> Parse (\ts -> Right ([], ts)))

> parseSymExpr :: Dictionary SymSet -> Parse SymSet
> parseSymExpr dict
>     = (fmap Set.unions
>        . parseDelimited ['{', '(']
>        $ parseSeparated "," (parseSymExpr dict))
>       <|> ( fmap (foldr1 Set.intersection)
>           . parseDelimited ['[']
>           $ parseSeparated "," (parseSymExpr dict))
>       <|> parseSymSet dict

> parseSymSet :: Dictionary SymSet -> Parse SymSet
> parseSymSet dict
>     = Parse $ \xs ->
>       case xs
>       of (TName n : ts)
>              -> fmap (flip (,) ts) (definition n dict)
>          (TSymbol '/' : TName n : ts)
>              -> Right . flip (,) ts $ singleton n
>          (a:_)
>              -> Left $ "cannot start a SymSet with " ++
>                 showParen True (shows a) ""
>          _ -> Left "unexpected end of input in SymSet"

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
>               | otherwise  =  Left $
>                               "invalid opening delimiter: " ++
>                               show x
>           openingDelimiter _
>               = Left "unexpected end of input looking for opening delimiter"

> parseClosingDelimiter :: Char -> Parse [a]
> parseClosingDelimiter = flip eat [] . singleton . matchingDelimiter

> parseSeparated :: String -> Parse a -> Parse [a]
> parseSeparated string p = (:) <$> p <*> many (eat string [] >> p)



> plCatenate :: PLFactor -> PLFactor -> PLFactor
> plCatenate (PLFactor h _ xs) (PLFactor _ t ys) = PLFactor h t (pc xs ys)
>     where pc [] bs       =  bs
>           pc [a] []      =  [a]
>           pc [a] (b:bs)  =  (a ++ b) : bs
>           pc (a:as) bs   =  a : pc as bs

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
>                             = unlines $ concatMap (filter (/= "") . lines)
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
