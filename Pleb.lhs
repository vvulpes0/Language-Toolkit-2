> module Pleb (readPleb) where

> import FSA
> import Factors (buildLiteral, Factor(..), required)

> import Data.Char (isSpace, isLetter)
> import Data.Set (Set)

> readPleb :: String -> FSA Integer String
> readPleb s
>     | isEmpty ts = either error normalize . apply $ maybe [] id msts
>     | otherwise  = error "no parse"
>     where (msts, ts) = parsePleb (tokenize s)

> apply :: [Statement] -> Either String (FSA Integer String)
> apply sts = case es of
>               (a:[])   ->  either Left id $
>                            automatonFromExpr <$> ealphabet <*>
>                            edictionary <*> a
>               (a:b:_)  ->  Left "too many expressions"
>               _        ->  Left "no expression"
>               
>     where (es', (eas, sas)) = splitAssignments <$> splitStatements sts
>           edictionary = assignSyms . orderA $
>                         map (varsAndSyms <$> listFromSymbolSet <$>) sas
>           es = map (replaceVars (fromCollapsible eas)) es'
>           ealphabet = union <$>
>                       unionAll <$> sequenceE (map (fmap usedSymbols) es) <*>
>                       fmap (unionAll . tmap snd) edictionary

> automatonFromExpr :: Set String
>                   -> Set (String, Set String)
>                   -> Expr -> Either String (FSA Integer String)
> automatonFromExpr alphabet dictionary e
>     = case e of
>         Concatenation es  ->  f mconcat es
>         Conjunction es    ->  f intersectAll es
>         Disjunction es    ->  f unionAll es
>         Factor f          ->  automatonFromFactor alphabet dictionary f
>         Iteration e       ->  g (renameStates . minimize . kleeneClosure) e
>         Negation e        ->  g complementDeterministic e
>         PRelation es      ->  f (mconcat .
>                                  sepBy (totalWithAlphabet alphabet)) es
>         _                 ->  Left "unimplemented expr -> automaton"
>       where afe = automatonFromExpr alphabet dictionary
>             f tl = fmap (renameStates . minimize . tl) .
>                    sequenceE . map afe .
>                    listFromExprList
>             g t  = fmap t . automatonFromExpr alphabet dictionary

> automatonFromFactor :: Set String
>                     -> Set (String, Set String)
>                     -> PFactor -> Either String (FSA Integer String)
> automatonFromFactor alphabet dictionary (LocalFactor aa)
>     = case aa of
>         Word a  ->  f True  True  <$> sequenceFromAtom dictionary a
>         Head a  ->  f True  False <$> sequenceFromAtom dictionary a
>         Tail a  ->  f False True  <$> sequenceFromAtom dictionary a
>         Free a  ->  f False False <$> sequenceFromAtom dictionary a
>     where f h t ss = buildLiteral alphabet . required $ Substring ss h t
> automatonFromFactor alphabet dictionary (PieceFactor a)
>     = buildLiteral alphabet . required . Subsequence  <$>
>       sequenceFromAtom dictionary a

> sequenceFromAtom :: Set (String, Set String) -> Atom
>                  -> Either String [Set String]
> sequenceFromAtom dictionary (Atom a) = sequenceFromAtom' a
>     where sequenceFromAtom' (AtomCont (Constant x) c)
>               = (singleton x :) <$> sequenceFromAtom' c
>           sequenceFromAtom' (AtomCont (Variable x) c)
>               = (unionAll (tmap snd $ keep ((== x) . fst) dictionary) :) <$>
>                 sequenceFromAtom' c
>           sequenceFromAtom' _ = Right []



> splitStatements :: [Statement] -> ([Expr], [Assignment])
> splitStatements (ExprStatement x : xs)   = mapfst (x :) (splitStatements xs)
> splitStatements (AssignStatement x : xs) = fmap (x :) (splitStatements xs)
> splitStatements _ = ([], [])

> splitAssignments :: [Assignment]
>                  -> ([(String, Expr)], [(String, SymbolSet)])
> splitAssignments (ExprAlias p a : xs) = mapfst ((p, a):) (splitAssignments xs)
> splitAssignments (SymAlias p a : xs) = fmap ((p, a):) (splitAssignments xs)
> splitAssignments _ = ([], [])

> listFromSymbolSet :: SymbolSet -> [SymSet]
> listFromSymbolSet (SymbolSet x ssc)   =  x : cont ssc
>     where cont (SymbolSetCont x ssc)  =  x : cont ssc
>           cont SymbolSetEnd           =  []

> varsAndSyms :: [SymSet] -> (Set String, Set String)
> varsAndSyms [] = (empty, empty)
> varsAndSyms (Constant x : xs) = fmap (insert x) (varsAndSyms xs)
> varsAndSyms (Variable x : xs) = mapfst (insert x) (varsAndSyms xs)

> orderA :: (Eq a) =>
>           [(String, (Set String, a))]
>        -> [(String, (Set String, a))]
> orderA = orderA' . map (\(a, (b, c)) -> (b, (a, (b, c))))

> orderA' :: (Eq a) =>
>            [(Set String, (String, (Set String, a)))]
>         -> [(String, (Set String, a))]
> orderA' vss
>     | isEmpty vss      = [] -- Nothing left to process
>     | isEmpty initials = [] -- Cannot progress
>     | otherwise        = initials ++ orderA' (map accountForNewNames others)
>     where (initials', others)  =  partition (isEmpty . fst) vss
>           initials             =  map snd initials'
>           names                =  fromCollapsible $ map fst initials
>           accountForNewNames   =  mapfst (flip difference names)

> assignSyms :: [(String, (Set String, Set String))]
>            -> Either String (Set (String, Set String))
> assignSyms = assignSyms' empty

> assignSyms' :: Set (String, Set String)
>             -> [(String, (Set String, Set String))]
>             -> Either String (Set (String, Set String))
> assignSyms' dictionary [] = Right dictionary
> assignSyms' dictionary ((name, (vars, syms)) : xs)
>     | assigned name  =  Left ("multiple definitions of " ++ name)
>     | otherwise      =  assignSyms' next xs
>     where assigned = isIn (tmap fst dictionary)
>           expanded = unionAll . tmap snd $
>                      keep (isIn vars . fst) dictionary
>           next     = insert (name, (union expanded syms)) dictionary

> listFromExprList :: ExprList -> [Expr]
> listFromExprList (ExprList e ec)    =  e : cont ec
>     where cont (ExprListCont x ec)  =  x : cont ec
>           cont ExprListEnd          =  []

> replaceVars :: Set (String, Expr) -> Expr -> Either String Expr
> replaceVars = replaceVars' empty

> replaceVars' :: Set String -> Set (String, Expr) -> Expr -> Either String Expr
> replaceVars' names dictionary e
>     = case e of 
>         Concatenation es -> f Concatenation es
>         Conjunction es   -> f Conjunction es
>         Disjunction es   -> f Disjunction es
>         Factor _         -> Right e
>         Iteration x      -> Iteration <$> replaceVars' names dictionary x
>         Negation x       -> Negation  <$> replaceVars' names dictionary x
>         PRelation es     -> f PRelation es
>         VarExpr x        -> g x
>     where f t es = t <$> replaceVarsL names dictionary es
>           g x = let subs = fromCollapsible (keep ((== x) . fst) dictionary)
>                 in case subs of
>                      (a:[])  -> if isIn names (fst a)
>                                 then Left ("cycle detected in " ++ x)
>                                 else replaceVars' (insert x names) dictionary
>                                      (snd a)
>                      (a:b:_) -> Left ("multiple definition of " ++ x)
>                      _       -> Left ("undefined variable " ++ x)

> replaceVarsL :: Set String -> Set (String, Expr) -> ExprList
>              -> Either String ExprList
> replaceVarsL n d (ExprList e c)
>     = ExprList <$> replaceVars' n d e <*> replaceVarsLC n d c

> replaceVarsLC :: Set String -> Set (String, Expr) -> ExprListCont
>               -> Either String ExprListCont
> replaceVarsLC n d ExprListEnd = Right ExprListEnd
> replaceVarsLC n d (ExprListCont e c)
>     = ExprListCont <$> replaceVars' n d e <*> replaceVarsLC n d c

> usedSymbols :: Expr -> Set String
> usedSymbols e = case e of
>                   Concatenation es -> f es
>                   Conjunction es   -> f es
>                   Disjunction es   -> f es
>                   Factor f         -> usedSymbolsPF f
>                   Iteration x      -> usedSymbols x
>                   Negation x       -> usedSymbols x
>                   PRelation es     -> f es
>                   _                -> empty
>     where f es = usedSymbolsL es
> usedSymbolsL :: ExprList -> Set String
> usedSymbolsL (ExprList e c) =  union (usedSymbols e) (usedSymbolsL' c)
>     where usedSymbolsL' ExprListEnd = empty
>           usedSymbolsL' (ExprListCont e c)
>               = union (usedSymbols e) (usedSymbolsL' c)
> usedSymbolsPF :: PFactor -> Set String
> usedSymbolsPF (LocalFactor a) = usedSymbolsA a
> usedSymbolsPF (PieceFactor a) = usedSymbolsA (Free a)

> usedSymbolsA :: AnchoredAtom -> Set String
> usedSymbolsA aa = case aa of
>                     Word (Atom a) -> f a
>                     Head (Atom a) -> f a
>                     Tail (Atom a) -> f a
>                     Free (Atom a) -> f a
>     where f AtomEnd = empty :: Set String
>           f (AtomCont (Constant x) c) = insert x (f c)
>           f (AtomCont _ c) = f c



> data Token = TSymbol Char
>            | TName String
>              deriving (Eq, Ord, Read, Show)

> tokenize :: String -> [Token]
> tokenize "" = []
> tokenize (x:xs)
>     | x == '#'      =  tokenize (dropWhile (/= '\n') xs)
>     | isSpace x     =  tokenize (dropWhile isSpace xs)
>     | isLetter x    =  (\(a,b) -> TName a : tokenize b)
>                        (break (\s -> isIn ",{}<>⟨⟩()" s || isSpace s) (x:xs))
>     | otherwise     =  TSymbol x : tokenize xs



> data Statement = AssignStatement Assignment
>                | ExprStatement Expr
>                  deriving (Eq, Ord, Read, Show)

> data Assignment = SymAlias String SymbolSet
>                 | ExprAlias String Expr
>                   deriving (Eq, Ord, Read, Show)

> data SymbolSet = SymbolSet SymSet SymbolSetCont
>                  deriving (Eq, Ord, Read, Show)

> data SymbolSetCont = SymbolSetCont SymSet SymbolSetCont
>                    | SymbolSetEnd
>                      deriving (Eq, Ord, Read, Show)

> data Expr = Concatenation ExprList
>           | Conjunction ExprList
>           | Disjunction ExprList
>           | Factor PFactor
>           | Iteration Expr
>           | Negation Expr
>           | PRelation ExprList
>           | VarExpr String
>           deriving (Eq, Ord, Read, Show)

> data ExprList = ExprList Expr ExprListCont
>               deriving (Eq, Ord, Read, Show)

> data ExprListCont = ExprListCont Expr ExprListCont
>                   | ExprListEnd
>                   deriving (Eq, Ord, Read, Show)

> data PFactor = PieceFactor Atom
>              | LocalFactor AnchoredAtom
>                deriving (Eq, Ord, Read, Show)

> data AnchoredAtom = Word Atom
>                   | Head Atom
>                   | Tail Atom
>                   | Free Atom
>                     deriving (Eq, Ord, Read, Show)

> data Atom = Atom AtomCont
>           deriving (Eq, Ord, Read, Show)

> data AtomCont = AtomCont SymSet AtomCont
>               | AtomEnd
>                 deriving (Eq, Ord, Read, Show)

> data SymSet = Variable String
>             | Constant String
>               deriving (Eq, Ord, Read, Show)

> parsePleb :: [Token] -> (Maybe [Statement], [Token])
> parsePleb = parsePleb' []

> parsePleb' :: [Statement] -> [Token] -> (Maybe [Statement], [Token])
> parsePleb' sts [] = (Just sts, [])
> parsePleb' sts ts = let (s, ts') = parseStatement ts
>                     in maybe
>                        (Nothing, ts')
>                        (\statement -> parsePleb' (statement : sts) ts')
>                        s

> parseStatement :: [Token] -> (Maybe Statement, [Token])
> parseStatement ts = head . (++ [(Nothing, ts)]) $
>                     keep (isJust . fst)
>                     [ mapfst (fmap AssignStatement) (parseAssignment ts)
>                     , mapfst (fmap ExprStatement) (parseExpr ts)
>                     ]

> parseAssignment :: [Token] -> (Maybe Assignment, [Token])
> parseAssignment (TSymbol e : TName x : ts)
>     | isIn "=≝" e = head . (++ [(Nothing, TSymbol e : TName x : ts)]) $
>                     keep (isJust . fst)
>                     [ mapfst (fmap (ExprAlias x)) (parseExpr ts)
>                     , mapfst (fmap (SymAlias x)) (parseSymbolSet ts)
>                     ]
>     | otherwise = (Nothing, TSymbol e : TName x : ts)
> parseAssignment ts = (Nothing, ts)

> parseSymbolSet :: [Token] -> (Maybe SymbolSet, [Token])
> parseSymbolSet (TSymbol d:ts)
>     | isIn "{(" d  = (\(s, (c, xs)) -> (SymbolSet <$> s <*> c, xs))
>                      (fmap (parseSymbolSetCont d) (parseSymSet ts))
>     | otherwise     = (Nothing, TSymbol d:ts)
> parseSymbolSet _ = (Nothing, [])

> parseSymbolSetCont :: Char -> [Token] -> (Maybe SymbolSetCont, [Token])
> parseSymbolSetCont d (TSymbol ',' : TSymbol '/' : TName x : ts)
>     = mapfst (fmap (SymbolSetCont (Constant x))) (parseSymbolSetCont d ts)
> parseSymbolSetCont d (TSymbol ',' : TName x : ts)
>     = mapfst (fmap (SymbolSetCont (Variable x))) (parseSymbolSetCont d ts)
> parseSymbolSetCont d (TSymbol x:ts)
>     | x == matchingDelimiter d = (Just SymbolSetEnd, ts)
>     | otherwise                = (Nothing, TSymbol x:ts)
> parseSymbolSetCont _ ts = (Nothing, ts)

> parseExpr :: [Token] -> (Maybe Expr, [Token])
> parseExpr ts = head . (++ [(Nothing, ts)]) . keep (isJust . fst) $
>                map (flip ($) ts) fs
>     where fs = [ parseConcatenation
>                , parseConjunction
>                , parseDisjunction
>                , parseIteration
>                , parseNegation
>                , parsePRelation
>                , mapfst (fmap Factor) . parseFactor
>                , parseVarExpr
>                ]

> parseConcatenation, parseConjunction, parseDisjunction, parseIteration, parseNegation, parsePRelation, parseVarExpr :: [Token] -> (Maybe Expr, [Token])
> parseConcatenation  =  parseFExprList [".", "⋄"]         Concatenation
> parseConjunction    =  parseFExprList ["∩", "⋂", "/\\"]  Conjunction
> parseDisjunction    =  parseFExprList ["∪", "⋃", "\\/"]  Disjunction
> parseIteration      =  parseFExpr     ["*","∗"]          Iteration
> parseNegation       =  parseFExpr     ["¬", "~", "!"]    Negation
> parsePRelation      =  parseFExprList ["‥", ".."]        PRelation
> parseVarExpr ts     = case ts of
>                         (TName x : ts') -> (Just (VarExpr x), ts')
>                         _               -> (Nothing, ts)

> parseFExprList :: [String] -> (ExprList -> Expr) -> [Token]
>                -> (Maybe Expr, [Token])
> parseFExprList syms f ts = maybe
>                            (Nothing, ts)
>                            (\xs -> mapfst (fmap f) (parseExprList xs)) .
>                            maybeHead . map snd . keep fst $
>                            map (\s -> (isPrefixOf ts (tsyms s),
>                                        drop (length s) ts))
>                            syms

> parseFExpr :: [String] -> (Expr -> Expr) -> [Token] -> (Maybe Expr, [Token])
> parseFExpr syms f ts = maybe
>                        (Nothing, ts)
>                        (\xs -> mapfst (fmap f) (parseExpr xs)) .
>                        maybeHead . map snd . keep fst $
>                        map (\s -> (isPrefixOf ts (tsyms s),
>                                    drop (length s) ts))
>                        syms

> parseExprList :: [Token] -> (Maybe ExprList, [Token])
> parseExprList (TSymbol t:ts)
>     | isIn "{(" t = (\(e, (c, xs)) -> (ExprList <$> e <*> c, xs))
>                     (fmap (parseExprListCont t) (parseExpr ts))
>     | otherwise = (Nothing, TSymbol t : ts)
> parseExprList ts = (Nothing, ts)

> parseExprListCont :: Char -> [Token] -> (Maybe ExprListCont, [Token])
> parseExprListCont d (TSymbol t:ts)
>     | t == matchingDelimiter d = (Just ExprListEnd, ts)
>     | t == ',' = (\(e, (c, xs)) -> (ExprListCont <$> e <*> c, xs))
>                  (fmap (parseExprListCont d) (parseExpr ts))
>     | otherwise = (Nothing, TSymbol t : ts)
> parseExprListCont d ts = (Nothing, ts)

> parseFactor :: [Token] -> (Maybe PFactor, [Token])
> parseFactor ts = maybe
>                  (mapfst (fmap LocalFactor) (parseAnchoredAtom ts))
>                  (mapfst (fmap PieceFactor) . parseAtom)
>                  afterMarker
>     where pieceMarkers = ["..", "‥"]
>           afterMarker  =  maybeHead . map snd . keep fst $
>                           map (\m -> (isPrefixOf ts (tsyms m),
>                                       drop (length m) ts))
>                           pieceMarkers

> parseAnchoredAtom :: [Token] -> (Maybe AnchoredAtom, [Token])
> parseAnchoredAtom ts
>     | isPrefixOf ts uWord = mapfst (fmap Word)
>                             (parseAtom (drop (length uWord) ts))
>     | isPrefixOf ts aWord = mapfst (fmap Word)
>                             (parseAtom (drop (length aWord) ts))
>     | isPrefixOf ts uHead = mapfst (fmap Head)
>                             (parseAtom (drop (length uHead) ts))
>     | isPrefixOf ts aHead = mapfst (fmap Head)
>                             (parseAtom (drop (length aHead) ts))
>     | isPrefixOf ts uTail = mapfst (fmap Tail)
>                             (parseAtom (drop (length uTail) ts))
>     | isPrefixOf ts aTail = mapfst (fmap Tail)
>                             (parseAtom (drop (length aTail) ts))
>     | otherwise           = mapfst (fmap Free) (parseAtom ts)
>     where uWord = tsyms "⋊⋉"
>           uHead = tsyms "⋊"
>           uTail = tsyms "⋉"
>           aWord = tsyms "%][%"
>           aHead = tsyms "%]"
>           aTail = tsyms "[%"

> parseAtom :: [Token] -> (Maybe Atom, [Token])
> parseAtom (TSymbol x:ts)
>     | isIn "<⟨" x  = mapfst (fmap Atom) (parseAtomCont x ts)
>     | otherwise    = (Nothing, TSymbol x:ts)
> parseAtom _ = (Nothing, [])

> parseAtomCont :: Char -> [Token] -> (Maybe AtomCont, [Token])
> parseAtomCont d ts
>     | isPrefixOf ts m = (Just AtomEnd, (drop (length m) ts))
>     | otherwise       = let (s, ts') = parseSymSet ts
>                         in maybe
>                            (Nothing, ts)
>                            (\symset -> mapfst (fmap (AtomCont symset))
>                                        (parseAtomCont d ts'))
>                            s
>     where m = [TSymbol (matchingDelimiter d)]

> parseSymSet :: [Token] -> (Maybe SymSet, [Token])
> parseSymSet (TSymbol '/' : TName x : ts) = (Just (Constant x), ts)
> parseSymSet (TName x : ts)               = (Just (Variable x), ts)
> parseSymSet ts                           = (Nothing, ts)



> isJust :: Maybe a -> Bool
> isJust = maybe False (const True)

> isPrefixOf :: (Eq a) => [a] -> [a] -> Bool
> isPrefixOf  []  []  = True
> isPrefixOf  []  _   = False
> isPrefixOf  _   []  = True
> isPrefixOf (x:xs) (y:ys) = x == y && isPrefixOf xs ys

> mapfst :: (a -> c) -> (a, b) -> (c, b)
> mapfst f (a, b) = (f a, b)

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

> maybeHead :: [a] -> Maybe a
> maybeHead []     =  Nothing
> maybeHead (a:_)  =  Just a

> partition :: (a -> Bool) -> [a] -> ([a], [a])
> partition f (a : as)
>     | f a        =  mapfst (a:) (partition f as)
>     | otherwise  =  fmap (a:) (partition f as)
> partition f _    =  ([], [])

> sepBy :: a -> [a] -> [a]
> sepBy _ []     = []
> sepBy _ (a:[]) = a : []
> sepBy x (a:as) = a : x : sepBy x as

> tsyms :: String -> [Token]
> tsyms = tmap TSymbol

> sequenceE :: [Either a b] -> Either a [b]
> sequenceE = foldr (<*>) (Right []) . map (fmap (:))
