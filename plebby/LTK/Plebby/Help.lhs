> module LTK.Plebby.Help where

> import Data.Char (isSpace, toLower, toUpper)
> import Data.Either (isLeft, isRight)
> import Data.List (foldl', isPrefixOf, sortBy)
> import Data.Map (Map)
> import qualified Data.Map as Map

> type Language = String
> type HelpKey = String
> type ShortDesc = String
> type LongDesc = String

> data ArgType = ArgE
>              | ArgF
>              | ArgI
>              | ArgS
>              | ArgV
>                deriving (Eq, Ord, Read, Show)

> data Category = ClassCat
>               | CommandCat
>               | ComparisonCat
>               | ConfigCat
>               | DotCat
>               | EnvironmentCat
>               | GraphCat
>               | IOCat
>               | LearnCat
>               | SyntaxCat
>               | TutorialCat
>               deriving (Eq, Ord, Read, Show)

"Rich Text" here is a custom format.
Formatting commands are of the form %<x:string>
where x is a single character representing the kind of thing.
* a: argument
* b: bold
* c: command
* e: example
* h: header
* p: paragraph break (only active as the word "%<p:>")
* t: topic / category
* v: named variable
* -: line-break (only active as the word "%<-:>")
When breaking a rich string into words,
these sequences get broken as well:
    %<x:many words> becomes %<x:many> %<x:words>
Within a formatted region, the % sign retains the next character,
so a space following a percent sign is retained as a non-breaking space,
and the % and > characters can be encoded as %% and %>, respectively.

> spanTypes :: Map Char (String,String)
> spanTypes = Map.fromList
>             [ ('a', ("\27[4m","\27[m")) -- argument
>             , ('b', ("\27[1m","\27[m")) -- bold
>             , ('c', ("\27[1m","\27[m")) -- command
>             , ('e', ("\27[34m","\27[m")) -- example
>             , ('h', ("\27[33m","\27[m")) -- header
>             , ('p', ("","\n")) -- paragraph-break
>             , ('t', ("\27[1;32m","\27[m")) -- topic / category
>             , ('v', ("\27[1;34m","\27[m")) -- named variable
>             , ('-', ("","")) -- line-break
>             ]

> wordWrap :: Int -> String -> [String]
> wordWrap n = map (f . g) . spanLinesRS n . richWords
>     where f (x,False) = unwords x
>           f (x,True) = concat $ justifyRS n x
>           g (x,b) = ( reverse
>                       $ case reverse x of
>                           (y:ys) -> case reverse y of
>                                       (' ':zs) -> reverse zs : ys
>                                       _ -> y:ys
>                           _ -> []
>                     , b) -- remove line-final space

> spanLinesRS :: Int -> [String] -> [([String],Bool)]
> spanLinesRS n (x:xs)
>     | lengthRS x > n = ([x],False) : spanLinesRS n xs
>     | otherwise      = let (ys,zs,b) = spanLineRS n (x:xs)
>                        in (ys,b) : spanLinesRS n zs
> spanLinesRS _ _ = []

> spanLineRS :: Int -> [String] -> ([String],[String],Bool)
> spanLineRS _ []           = ([],[],False)
> spanLineRS _ ("%<-:>":xs) = (["%<-:>"],xs,False)
> spanLineRS _ ("%<p:>":xs) = (["%<p:>"],xs,False)
> spanLineRS _ (('%' : '<' : 'h' : ':' : s):xs)
>     = (["%<h:"++s],xs,False)
> spanLineRS n (x:xs)
>     | l <= n    = let (pre, post, s) = spanLineRS (n - l - 1) xs
>                   in (x:pre, post, s)
>     | otherwise = ([], x:xs, True)
>     where l = lengthRS x

> justifyRS :: Int -> [String] -> [String]
> justifyRS n xs@(x:y:ys)
>     = x : replicate s ' ' : justifyRS (n - lx - s) (y:ys)
>     where toFill = max (n - sum (map lengthRS xs)) 0
>           lx = lengthRS x
>           nx = 1 + length ys
>           s = (2*toFill + nx) `div` (2*nx)
> justifyRS _ xs = xs

> lengthRS :: String -> Int
> lengthRS = length . formatRS Map.empty

> formatRS :: Map Char (String,String) -> String -> String
> formatRS f ('%' : '<' : x : ':' : s)
>     = let (rest,w) = extract s
>       in pre ++ w ++ post ++ formatRS f rest
>     where (pre,post) = maybe ("","") id $ Map.lookup x f
>           extract ('%' : y : ys) = (y :) `fmap` extract ys
>           extract ('>' : ys) = (ys, [])
>           extract (y : ys) = (y :) `fmap` extract ys
>           extract _ = ([],[])
> formatRS f (x:xs) = x : formatRS f xs
> formatRS _ [] = []

> richWords :: String -> [String]
> richWords [] = []
> richWords xs = uncurry (:)
>                . fmap richWords
>                $ spanRichWord (dropWhile isSpace xs)

> spanRichWord :: String -> (String,String)
> spanRichWord ('%' : '<' : x : ':' : s)
>     = let p = readCommandWord s
>       in ('%' : '<' : x : ':' : snd p, fst p)
>     where readCommandWord [] = ([],">")
>           readCommandWord (y:ys)
>               | y == '%'  = fmap ((++) (y : take 1 ys))
>                             $ readCommandWord (drop 1 ys)
>               | isSpace y = ( '%' : '<' : x : ':'
>                             : dropWhile isSpace ys
>                             , ">")
>               | y == '>'  = let q = spanRichWord ys
>                             in (snd q, '>' : fst q)
>               | otherwise = fmap (y:) $ readCommandWord ys
> spanRichWord (x:xs)
>     | x `elem` ".!?" && all isSpace (take 1 xs)
>         = (x : " ", xs)
>     | isSpace x = ([],xs)
>     | otherwise = let p = spanRichWord xs
>                   in (x : fst p, snd p)
> spanRichWord [] = ([],[])

> lookupLang :: Language -> Map Language a -> Maybe a
> lookupLang lang m
>     = m Map.!? foldl' f "" (Map.keys m)
>     where f b a = if a `isPrefixOf` lang then a else b

> synopses :: Language -> Maybe Category
>          -> [(Either String Category, [ArgType], ShortDesc)]
> synopses lang cat
>     = map (uncurry f) . Map.assocs . Map.filterWithKey hasCat
>       $ helpTopics
>     where hasCat k (_,cats,_)
>               = case cat of
>                   Just CommandCat -> isLeft k
>                   Just c -> c `elem` cats
>                   _ -> isRight k
>           f t (a, _, m)
>               = (t, a, fst . maybe ("","") id $ lookupLang lang m)

> sortDescs :: Language -> [(Either String Category, a, b)]
>           -> [(Either String Category, a, b)]
> sortDescs lang = sortBy (\(a,_,_) (b,_,_) -> f a `compare` f b)
>     where f = either (map toLower) (showC lang)

> showSynopses :: Int -> Language
>              -> [(Either String Category, [ArgType], ShortDesc)]
>              -> [String]
> showSynopses width lang syns
>     = concatMap (showSynopsis sz (width - sz - 1)) compact
>     where g = either (("%<c:" ++) . (++ ">"))
>                      (("%<t:" ++) . (++ ">") . showC lang)
>           f (topic, a, d)
>               = (unwords (g topic : map (shortArg lang) a ++ ["-"]),d)
>           compact = map f syns
>           sz = maximum . map (lengthRS . fst) $ compact

> showSynopsis :: Int -> Int -> (String, ShortDesc) -> [String]
> showSynopsis left right (name, desc)
>     = zipWith f (name : repeat []) $ wordWrap right desc
>     where alignR sz s = replicate (sz - lengthRS s) ' ' ++ s
>           f s t = unwords [(alignR left s), t]

> argString :: Language -> ArgType -> (String, String)
> argString lang typ
>     = maybe ("<???>","<???>")
>       (\(a,b) -> ("<%<a:" ++ a ++ ">>", "<%<a:" ++ b ++ ">>"))
>       . (=<<) id . fmap (Map.lookup typ)
>       . lookupLang lang
>       $ Map.fromList
>         [ ( ""
>           , Map.fromList
>             [ (ArgE, ("expr", "e"))
>             , (ArgF, ("file", "f"))
>             , (ArgI, ("int", "i"))
>             , (ArgS, ("string", "s"))
>             , (ArgV, ("var", "v"))
>             ]
>           )]

> longArg :: Language -> ArgType -> String
> longArg lang = fst . argString lang

> shortArg :: Language -> ArgType -> String
> shortArg lang = snd . argString lang

> headname :: Language -> String -> String
> headname lang str
>     = maybe "" id . (=<<) id . fmap (lookupLang lang)
>       . Map.lookup str
>       $ Map.fromList
>         [ ( "CATEGORIES"
>           , Map.fromList
>             [ ("", "CATEGORIES")
>             , ("fr", "CATEGORIES")
>             ])
>         , ( "COMMAND"
>           , Map.fromList
>             [ ("", "COMMAND")
>             , ("fr", "COMMANDE")
>             ])
>         , ( "COMMANDS"
>           , Map.fromList
>             [ ("", "COMMANDS")
>             , ("fr", "COMMANDES")
>             ])
>         , ( "DESCRIPTION"
>           , Map.fromList
>             [ ("", "DESCRIPTION")
>             , ("fr", "DESCRIPTION")
>             ])
>         , ( "NAME"
>           , Map.fromList
>             [ ("", "NAME")
>             , ("fr", "NOM")
>             ])
>         , ( "TOPIC"
>           , Map.fromList
>             [ ("", "TOPIC")
>             , ("fr", "THEME")
>             ])
>         , ( "TOPICS"
>           , Map.fromList
>             [ ("", "TOPICS")
>             , ("fr", "THEMES")
>             ])
>         ]

> categories :: Map Language (Map String Category, Map Category String)
> categories = Map.fromList
>              [ ( ""
>                , bimapFromList
>                  [ ("classification", ClassCat)
>                  , ("commands", CommandCat)
>                  , ("comparison", ComparisonCat)
>                  , ("config", ConfigCat)
>                  , ("dot", DotCat)
>                  , ("environment", EnvironmentCat)
>                  , ("visualization", GraphCat)
>                  , ("i/o", IOCat)
>                  , ("inference", LearnCat)
>                  , ("language", SyntaxCat)
>                  , ("tutorial", TutorialCat)
>                  ])
>              ]
>     where bimapFromList xs
>               = (Map.fromList xs, Map.fromList $ map rev xs)
>           rev (a,b) = (b,a)

> getTopic :: Language -> String -> Either String Category
> getTopic lang xs = maybe (Left xs') Right
>                    . (=<<) id . fmap (Map.lookup xs' . fst)
>                    $ lookupLang lang categories
>     where xs' = map toLower xs

> showC :: Language -> Category -> String
> showC lang cat = maybe "" (map toUpper)
>                  . (=<<) id . fmap (Map.lookup cat . snd)
>                  $ lookupLang lang categories

> showHelp :: Int -> Language -> Either String Category -> [String]
> showHelp width lang topic'
>     = maybe (["No help for " ++ either id (showC lang) topic']) f
>       $ lookupi topic' helpTopics
>     where norm = map toLower . dropWhile (== ':')
>           lookupi t m
>               = (\x -> case x of
>                          (y:_) -> Just y
>                          _ -> Nothing)
>                 . filter ( (== either (Left . norm) Right t)
>                          . either (Left . norm) Right . fst)
>                 $ Map.assocs m
>           f (topic, (args, cats, m))
>               = let (short,long) = desc m
>                 in g ( wordWrap width
>                      $ unwords
>                        ( [ "%<h:" ++ headname lang "NAME" ++ ">"
>                          , either
>                            (("%<c:" ++) . (++ ">"))
>                            (("%<t:" ++) . (++ ">") . showC lang)
>                            topic
>                          ]
>                        ++ map (longArg lang) args
>                        ++ ["-", short, "%<p:>"]
>                        ++ [ "%<h:"
>                           ++ headname lang "DESCRIPTION" ++">" ]
>                        ++ [long]
>                        ++ if null cats then []
>                           else "%<p:>"
>                                : ( "%<h:"
>                                  ++ headname lang "CATEGORIES"
>                                  ++ ">")
>                                : showCats cats
>                        )
>                      )
>           g x = [ c ++ replicate n ' ' ++ c ] ++ x ++ commands
>           commands
>               = case topic' of
>                   Left ":help"
>                       -> case synopses lang Nothing of
>                            [] -> []
>                            xs -> []
>                                  : ("%<h:"
>                                    ++ headname lang "TOPICS"
>                                    ++ ">")
>                                  : showSynopses width lang
>                                    (sortDescs lang xs)
>                   Left _ -> []
>                   Right x
>                       -> case synopses lang (Just x) of
>                            [] -> []
>                            xs -> []
>                                  : ("%<h:"
>                                    ++ headname lang "COMMANDS"
>                                    ++ ">")
>                                  : showSynopses width lang
>                                    (sortDescs lang xs)
>           c = headname lang
>               (if isLeft topic' then "COMMAND" else "TOPIC")
>           n = width - 2*lengthRS c
>           desc m = maybe ("","") id $ lookupLang lang m
>           showCats (x:[]) = ["%<t:" ++ showC lang x ++ ">"]
>           showCats (x:xs) = ("%<c:" ++ showC lang x ++ ">,")
>                             : showCats xs
>           showCats _ = []

> helpTopics :: Map (Either String Category)
>               ( [ArgType], [Category]
>               , (Map Language (ShortDesc, LongDesc)))
> helpTopics
>     = Map.fromList
>       [ ( Left ":bindings"
>         , ( [], [EnvironmentCat]
>           , Map.fromList
>             [ ( ""
>               , ( "print list of variables and their bindings"
>                 , unwords
>                   [ "Print a list of currently-bound variables"
>                   , "and their bindings. Because expression"
>                   , "variables have large representations,"
>                   , "these representations are omitted from"
>                   , "this listing but can be displayed"
>                   , "individually with %<c::show>."
>                   ]))
>             ]))
>       , ( Left ":cequal"
>         , ( [ArgE, ArgE], [ComparisonCat]
>           , Map.fromList
>             [ ( ""
>               , ( "compare expressions for logical equivalence"
>                 , unwords
>                 [ "Determine whether the first <%<a:expr>>"
>                 , "is logically equivalent to the second,"
>                 , "whether they are equal in every possible"
>                 , "%<v:universe>."
>                 ]))
>             ]))
>       , ( Left ":cimplies"
>         , ( [ArgE, ArgE], [ComparisonCat]
>           , Map.fromList
>             [ ( ""
>               , ( "check if first <%<a:expr>> logically implies second"
>                 , unwords
>                 [ "Determine whether the first <%<a:expr>>"
>                 , "logically implies the second"
>                 , "in every possible %<v:universe>."
>                 ]))
>             ]))
>       , ( Left ":compile"
>         , ( [], [EnvironmentCat]
>           , Map.fromList
>             [ ( ""
>               , ( "convert all bound expression to automata"
>                 , unwords
>                   [ "Convert all saved expressions into automata,"
>                   , "retaining the metadata that allows the"
>                   , "expression to be alphabet-agnostic."
>                   ]))
>             ]))
>       , ( Left ":display"
>         , ( [ArgE], [GraphCat]
>           , Map.fromList
>             [ ( ""
>               , ( "display <%<a:expr>> graphically"
>                 , unwords
>                   [ "Show a normal-form automaton representation"
>                   , "of <%<a:expr>> graphically"
>                   , "using an external %<c:display> program."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::dot> %<t:VISUALIZATION>"
>                   ]))
>             ]))
>       , ( Left ":dot"
>         , ( [ArgE], [DotCat]
>           , Map.fromList
>             [ ( ""
>               , ( "print a Dot file of expression"
>                 , unwords
>                   [ "Print a GraphViz dot-format representation"
>                   , "for a normal-form automaton for <%<a:expr>>."
>                   ]))
>             ]))
>       , ( Left ":dotPSG"
>         , ( [ArgE], [DotCat]
>           , Map.fromList
>             [ ( ""
>               , ( "print powerset graph of expression as Dot"
>                 , unwords
>                   [ "Print a GraphViz dot-format representation"
>                   , "for the powerset graph of a normal-form"
>                   , "automaton for <%<a:expr>>."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::psg>"
>                   ]))
>             ]))
>       , ( Left ":dotSynmon"
>         , ( [ArgE], [DotCat]
>           , Map.fromList
>             [ ( ""
>               , ( "print syntactic monoid of expression as Dot"
>                 , unwords
>                   [ "Print a GraphViz dot-format representation"
>                   , "for the right Cayley graph of the syntactic"
>                   , "monoid of <%<a:expr>>."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::eggbox>, %<c::synmon>"
>                   ]))
>             ]))
>       , ( Left ":eggbox"
>         , ( [ArgE], [GraphCat]
>           , Map.fromList
>             [ ( ""
>               , ( "display eggbox diagram of expression"
>                 , unwords
>                   [ "Show the eggbox diagram of the syntactic monoid"
>                   , "of <%<a:expr>>, graphically."
>                   , "If the empty string is in the syntactic"
>                   , "semigroup, then it is equivalent to some"
>                   , "nonempty string, and that larger string is"
>                   , "shown in its place."
>                   , "Otherwise, the empty string is depicted"
>                   , "by a box."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::orderJ>, %<c::orderL>,"
>                   , "%<c::orderR>, %<c::synmon>, %<c::synord>"
>                   , "%<t:VISUALIZATION>"
>                   ]))
>             ]))
>       , ( Left ":equal"
>         , ( [ArgE, ArgE], [ComparisonCat]
>           , Map.fromList
>             [ ( ""
>               , ( "compare expressions for language equality"
>                 , unwords
>                   [ "Determine whether the first <%<a:expr>>"
>                   , "specifies the same language as the second"
>                   , "with respect to the current %<v:universe>."
>                   ]))
>             ]))
>       , ( Left ":ground"
>         , ( [], [EnvironmentCat]
>           , Map.fromList
>             [ ( ""
>               , ( "ground all bound expressions"
>                 , unwords
>                   [ "Convert all saved expressions into automata,"
>                   , "discarding the metadata that allows the"
>                   , "expression to be alphabet-agnostic."
>                   ]))
>             ]))
>       , ( Left ":help"
>         , ( [ArgS], []
>           , Map.fromList
>             [ ( ""
>               , ( "show help"
>                 , unwords
>                   [ "Without arguments the %<c:help> command will"
>                   , "display this brief overview of the system,"
>                   , "as well as a list of topics."
>                   , "For more information about a specific topic,"
>                   , "including specific commands, use %<p:>"
>                   , "%<e:%>% :help% topic> %<p:>"
>                   , "Individual commands have both a short synopsis"
>                   , "that appears in their topic(s),"
>                   , "as well as a long description."
>                   , "%<p:>"
>                   , "You can exit the interpreter with %<c::quit>."
>                   ]))
>             ]))
>       , ( Left ":implies"
>         , ( [ArgE, ArgE], [ComparisonCat]
>           , Map.fromList
>             [ ( ""
>               , ( "synonym for %<c::subset>"
>                 , "See %<c::subset>." ))
>             ]))
>       , ( Left ":import"
>         , ( [ArgF], [IOCat]
>           , Map.fromList
>             [ ( ""
>               , ( "read file as plebby script"
>                 , unwords
>                   [ "Read <%<a:file>> one line at a time as if its"
>                   , "contents had been typed into the interpreter."
>                   , "Specifically this means that each statement"
>                   , "must be entirely on one line, and some lines"
>                   , "may be interpreter commands (including"
>                   , "%<c::import>)."
>                   ]))
>             ]))
>       , ( Left ":isAcom"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "locally %<v:t>-threshold 1-testable"
>                 , unwords
>                   [ "Determine if <%<a:expr>> has a syntactic"
>                   , "semigroup that is both aperiodic and commutative"
>                   , "with respect to the current %<v:universe>."
>                   , "These are the languages which make decisions"
>                   , "based on the multiset of symbols that appear"
>                   , "in a word, saturating at some threshold %<v:t>."
>                   , "This is the class of locally"
>                   , "%<v:t>-threshold 1-testable languages."
>                   , "If the language is in this class,"
>                   , "then the value of this parameter, %<v:t>,"
>                   , "is provided."
>                   , "%<p:>%<h:SEE% ALSO>"
>                   , "%<c::isCB>, %<c::isLTT>"
>                   ]))
>             ]))
>       , ( Left ":isB"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "band"
>                 , unwords
>                   [ "Determine if <%<a:expr>> has a syntactic"
>                   , "semigroup in which everything is idempotent,"
>                   , "also known as a band, with respect to"
>                   , "the current %<v:universe>."
>                   ]))
>             ]))
>       , ( Left ":isCB"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "commutative band"
>                 , unwords
>                   [ "Determine if <%<a:expr>> has a syntactic"
>                   , "semigroup in which everything is idempotent"
>                   , "and everything commutes, a commutative band,"
>                   , "with respect to the current %<v:universe>."
>                   , "This is also called a semilattice. These are"
>                   , "the languages which make distinctions based on"
>                   , "the set of symbols that appear in a word."
>                   , "This is the class of locally 1-testable"
>                   , "languages, or, equivalently, the piecewise"
>                   , "1-testable languages."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::isAcom>, %<c::isLT>, %<c::isPT>"
>                   ]))
>             ]))
>       , ( Left ":isDef"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "definite"
>                 , unwords
>                   [ "Determine if <%<a:expr>> is definite with"
>                   , "respect to the current %<v:universe>. These"
>                   , "are the languages which make distinctions"
>                   , "based on the suffixes of length at most"
>                   , "%<v:k> of words."
>                   , "If the language is in this class,"
>                   , "then the value of this parameter, %<v:k>,"
>                   , "is provided."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::isGD>, %<c::isRDef>,"
>                   , "%<c::isTDef>, %<c::isMTDef>"
>                   ]))
>             ]))
>       , ( Left ":isDot1"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "dot-depth at most one"
>                 , unwords
>                   [ "Determine if <%<a:expr>> has dot-depth at most"
>                   , "one with respect to the current %<v:universe>."
>                   , "These are the languages which make distinctions"
>                   , "based on the set of subsequences of substrings"
>                   , "that appear in words. For instance, one might"
>                   , "require that \"ab\" occurs, followed somewhere"
>                   , "later by \"cd\"."
>                   ]))
>             ]))
>       , ( Left ":isFinite"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "finite"
>                 , unwords
>                   [ "Determine if <%<a:expr>> represents a finite"
>                   , "language in the current %<v:universe>."
>                   , "These are the languages"
>                   , "whose canonical automata are acyclic."
>                   ]))
>             ]))
>       , ( Left ":isFO2"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "first-order with two variables and <"
>                 , unwords
>                   [ "Determine if <%<a:expr>> represents a language"
>                   , "definable in the two-variable restriction of"
>                   , "first-order logic with general precedence"
>                   , "in the current %<v:universe>."
>                   ]))
>             ]))
>       , ( Left ":isFO2B"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "first-order with two variables and <,bet"
>                 , unwords
>                   [ "Determine if <%<a:expr>> represents a language"
>                   , "definable in the two-variable restriction of"
>                   , "first-order logic with general precedence"
>                   , "and betweenness"
>                   , "in the current %<v:universe>."
>                   ]))
>             ]))
>       , ( Left ":isFO2BF"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "first-order with two variables and <,betfac"
>                 , unwords
>                   [ "Determine if <%<a:expr>> represents a language"
>                   , "definable in the two-variable restriction of"
>                   , "first-order logic with general precedence"
>                   , "and betweenness of factors"
>                   , "in the current %<v:universe>."
>                   ]))
>             ]))
>       , ( Left ":isFO2S"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "first-order with two variables and <,+1"
>                 , unwords
>                   [ "Determine if <%<a:expr>> represents a language"
>                   , "definable in the two-variable restriction of"
>                   , "first-order logic with general precedence"
>                   , "and successor"
>                   , "in the current %<v:universe>."
>                   ]))
>             ]))
>       , ( Left ":isGD"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "generalized definite"
>                 , unwords
>                   [ "Determine if <%<a:expr>> is generalized definite"
>                   , "with respect to the current %<v:universe>. These"
>                   , "are the languages which make distinctions"
>                   , "based on the prefixes and suffixes of length at"
>                   , "most %<v:k> of words."
>                   , "If the language is in this class,"
>                   , "then the value of this parameter, %<v:k>,"
>                   , "is provided."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::isDef>, %<c::isRDef>,"
>                   , "%<c::isTDef>, %<c::isMTDef>"
>                   ]))
>             ]))
>       , ( Left ":isGLPT"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "generalized locally \"piecewise testable\""
>                 , unwords
>                   [ "Determine if <%<a:expr>> is"
>                   , "generalized locally J-trivial"
>                   , "with repsect to the current %<v:universe>."
>                   , "This is a proper superset"
>                   , "of the dot-depth-one languages."
>                   , "These languages have syntactic monoids"
>                   , "in MeJ."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c:isDot1>"
>                   ]))
>             ]))
>       , ( Left ":isGLT"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "generalized locally testable"
>                 , unwords
>                   [ "Determine if <%<a:expr>> is"
>                   , "generalized locally testable"
>                   , "with respect to the current %<v:universe>."
>                   , "This is a proper superset of both"
>                   , "the locally testable languages"
>                   , "and the piecewise testable languages."
>                   , "These languages have syntactic monoids"
>                   , "in MeJ₁."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c:isGLPT>, %<c:isLT>, %<c:isPT>"
>                   ]))
>             ]))
>       , ( Left ":isLAcom"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "locally Acom"
>                 , unwords
>                   [ "Determine if <%<a:expr>> has a syntactic"
>                   , "semigroup whose local submonoids are"
>                   , "aperiodic and commutative"
>                   , "with respect to the current %<v:universe>."
>                   , "This is a proper superclass"
>                   , "of locally threshold testable."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::isAcom>, %<c::isLTT>"
>                   ]))
>             ]))
>       , ( Left ":isLB"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "locally a band"
>                 , unwords
>                   [ "Determine if <%<a:expr>> has a syntactic"
>                   , "semigroup whose local submonoids are"
>                   , "bands, everywhere idempotent,"
>                   , "with respect to the current %<v:universe>."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::isB>"
>                   ]))
>             ]))
>       , ( Left ":isLPT"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "locally \"piecewise testable\""
>                 , unwords
>                   [ "Determine if <%<a:expr>> has a syntactic"
>                   , "semigroup whose local submonoids are"
>                   , "J-trivial"
>                   , "with respect to the current %<v:universe>."
>                   , "This is a proper superclass of dot-depth one."
>                   , "The name comes from the fact that J-trivial"
>                   , "semigroups correspond to piecewise testable"
>                   , "languages."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::isPT>"
>                   ]))
>             ]))
>       , ( Left ":isLT"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "locally testable"
>                 , unwords
>                   [ "Determine if <%<a:expr>> is locally testable"
>                   , "with respect to the current %<v:universe>."
>                   , "These are the languages which make distinctions"
>                   , "based on the substrings of length %<v:k>,"
>                   , "including length %<v:k>-1 prefixes and suffixes"
>                   , "and shorter words of length up to %<v:k>-2."
>                   ]))
>             ]))
>       , ( Left ":isLTT"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "locally threshold testable"
>                 , unwords
>                   [ "Determine if <%<a:expr>> is"
>                   , "locally threshold testable"
>                   , "with respect to the current %<v:universe>."
>                   , "These are the languages which make distinctions"
>                   , "based on the number of substrings"
>                   , "of length %<v:k>,"
>                   , "including length %<v:k>-1 prefixes and suffixes"
>                   , "and shorter words of length up to %<v:k>-2."
>                   , "Counting saturates at some threshold %<v:t>."
>                   , "These are the languages definable"
>                   , "in first-order logic with successor alone."
>                   ]))
>             ]))
>       , ( Left ":isMTDef"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "multitier definite"
>                 , unwords
>                   [ "Determine if <%<a:expr>> is multitier definite"
>                   , "with respect to the current %<v:universe>."
>                   , "These are the languages which make distinctions"
>                   , "based on the length-%<v:k> tier-suffixes"
>                   , "of words, after projection to any combination"
>                   , "of subalphabets."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::isDef>, %<c::isMTF>, %<c::isMTGD>,"
>                   , "%<c::isMTRDef>, %<c::isTDef>"
>                   ]))
>             ]))
>       , ( Left ":isMTF"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "multitier co/finite"
>                 , unwords
>                   [ "Determine if <%<a:expr>> is multitier co/finite"
>                   , "with respect to the current %<v:universe>."
>                   , "These are the languages which make distinctions"
>                   , "based on the whether the tier-projection"
>                   , "to any subalphabet is in some finite set."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::isFinite>, %<c::isMTDef>, %<c::isMTRDef>"
>                   ]))
>             ]))
>       , ( Left ":isMTGD"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "multitier generalized definite"
>                 , unwords
>                   [ "Determine if <%<a:expr>> is"
>                   , "multitier generalized definite"
>                   , "with respect to the current %<v:universe>."
>                   , "These are the languages which make distinctions"
>                   , "based on the length-%<v:k>"
>                   , "tier-prefixes and tier-suffixes of words,"
>                   , "after projection to any combination"
>                   , "of subalphabets."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::isGD>, %<c::isMTDef>, %<c::isMTRDef>"
>                   ]))
>             ]))
>       , ( Left ":isMTRDef"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "multitier reverse definite"
>                 , unwords
>                   [ "Determine if <%<a:expr>> is"
>                   , "multitier reverse definite"
>                   , "with respect to the current %<v:universe>."
>                   , "These are the languages which make distinctions"
>                   , "based on the length-%<v:k> tier-prefixes"
>                   , "of words, after projection to any combination"
>                   , "of subalphabets."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::isRDef>, %<c::isMTF>, %<c::isMTDef>,"
>                   , "%<c::isMTGD>, %<c::isTRDef>"
>                   ]))
>             ]))
>       , ( Left ":isPT"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "piecewise testable"
>                 , unwords
>                   [ "Determine if <%<a:expr>> is piecewise testable"
>                   , "with respect to the current %<v:universe>."
>                   , "These are the languages which make distinctions"
>                   , "based on the length-%<v:k>"
>                   , "subsequences of words."
>                   , "Their syntactic monoids are J-trivial."
>                   ]))
>             ]))
>       , ( Left ":isRDef"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "reverse definite"
>                 , unwords
>                   [ "Determine if <%<a:expr>> is reverse definite"
>                   , "with respect to the current %<v:universe>. These"
>                   , "are the languages which make distinctions"
>                   , "based on the prefixes of length at"
>                   , "most %<v:k> of words."
>                   , "If the language is in this class,"
>                   , "then the value of this parameter, %<v:k>,"
>                   , "is provided."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::isDef>, %<c::isGD>,"
>                   , "%<c::isTRDef>, %<c::isMTRDef>"
>                   ]))
>             ]))
>       , ( Left ":isSF"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "star-free"
>                 , unwords
>                   [ "Determine if <%<a:expr>> is star-free"
>                   , "with respect to the current %<v:universe>."
>                   , "These are the languages definable in"
>                   , "first order logic with precedence."
>                   , "Equivalently, they are the languages"
>                   , "definable with regular expressions"
>                   , "generalized to allow intersection"
>                   , "and complementation, but restricted"
>                   , "to disallow the Kleene star."
>                   , "These are all and only the languages"
>                   , "whose syntactic semigroups are aperiodic."
>                   ]))
>             ]))
>       , ( Left ":isSL"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "strictly local"
>                 , unwords
>                   [ "Determine if <%<a:expr>> is strictly local"
>                   , "with respect to the current %<v:universe>."
>                   , "These are the languages which make accept"
>                   , "all and only those words containing only"
>                   , "permissible substrings of length %<v:k>,"
>                   , "including length %<v:k>-1 prefixes and suffixes"
>                   , "and shorter words of length up to %<v:k>-2."
>                   , "If the language is in this class,"
>                   , "then the value of this parameter, %<v:k>,"
>                   , "is provided."
>                   ]))
>             ]))
>       , ( Left ":isSP"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "strictly piecewise"
>                 , unwords
>                   [ "Determine if <%<a:expr>> is strictly piecewise"
>                   , "with respect to the current %<v:universe>."
>                   , "These are the languages which make accept"
>                   , "all and only those words containing only"
>                   , "permissible subsequences of length up to %<v:k>."
>                   , "If the language is in this class,"
>                   , "then the value of this parameter, %<v:k>,"
>                   , "is provided."
>                   ]))
>             ]))
>       , ( Left ":isTDef"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "tier-based definite"
>                 , unwords
>                   [ "Determine if <%<a:expr>> is"
>                   , "tier-based definite"
>                   , "with respect to the current %<v:universe>."
>                   , "These are the languages which make distinctions"
>                   , "based on the suffixes"
>                   , "of length at most %<v:k> of words"
>                   , "after projection to some subalphabet,"
>                   , "%<v:T>."
>                   , "If the language is in this class,"
>                   , "then the tier %<v:T> and the value"
>                   , "of this parameter, %<v:k> are provided."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::isDef>, %<c::isMTDef>"
>                   ]))
>             ]))
>       , ( Left ":isTGD"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "tier-based generalized definite"
>                 , unwords
>                   [ "Determine if <%<a:expr>> is"
>                   , "tier-based generalized definite"
>                   , "with respect to the current %<v:universe>."
>                   , "These are the languages which make distinctions"
>                   , "based on the prefixes and suffixes"
>                   , "of length at most %<v:k> of words"
>                   , "after projection to some subalphabet,"
>                   , "%<v:T>."
>                   , "If the language is in this class,"
>                   , "then the tier %<v:T> and the value"
>                   , "of this parameter, %<v:k> are provided."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::isGD>, %<c::isMTGD>"
>                   ]))
>             ]))
>       , ( Left ":isTLAcom"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "tier-based locally Acom"
>                 , unwords
>                   [ "Determine if <%<a:expr>> is"
>                   , "tier-based locally Acom"
>                   , "with respect to the current %<v:universe>."
>                   , "That is, is there some subalphabet %<v:T>"
>                   , "such that after projection to %<v:T>,"
>                   , "the language satisifies %<c::isLAcom>."
>                   , "If the language is in this class,"
>                   , "then the subalphabet %<v:T> is provided."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c:isLAcom>"
>                   ]))
>             ]))
>       , ( Left ":isTLB"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "tier-based locally a band"
>                 , unwords
>                   [ "Determine if <%<a:expr>> is"
>                   , "tier-based locally a band"
>                   , "with respect to the current %<v:universe>."
>                   , "That is, is there some subalphabet %<v:T>"
>                   , "such that after projection to %<v:T>,"
>                   , "the language satisifies %<c::isLB>."
>                   , "If the language is in this class,"
>                   , "then the subalphabet %<v:T> is provided."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c:isLB>"
>                   ]))
>             ]))
>       , ( Left ":isTLPT"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "tier-based locally \"piecewise testable\""
>                 , unwords
>                   [ "Determine if <%<a:expr>> is"
>                   , "tier-based locally J-trivial"
>                   , "with respect to the current %<v:universe>."
>                   , "That is, is there some subalphabet %<v:T>"
>                   , "such that after projection to %<v:T>,"
>                   , "the language satisifies %<c::isLPT>."
>                   , "If the language is in this class,"
>                   , "then the subalphabet %<v:T> is provided."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c:isLPT>"
>                   ]))
>             ]))
>       , ( Left ":isTLT"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "tier-based locally testable"
>                 , unwords
>                   [ "Determine if <%<a:expr>> is"
>                   , "tier-based locally testable"
>                   , "with respect to the current %<v:universe>."
>                   , "That is, is there some subalphabet %<v:T>"
>                   , "such that after projection to %<v:T>,"
>                   , "the language satisifies %<c::isLT>."
>                   , "If the language is in this class,"
>                   , "then the subalphabet %<v:T> is provided."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c:isLT>"
>                   ]))
>             ]))
>       , ( Left ":isTLTT"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "tier-based locally threshold testable"
>                 , unwords
>                   [ "Determine if <%<a:expr>> is"
>                   , "tier-based locally threshold testable"
>                   , "with respect to the current %<v:universe>."
>                   , "That is, is there some subalphabet %<v:T>"
>                   , "such that after projection to %<v:T>,"
>                   , "the language satisifies %<c::isLTT>."
>                   , "If the language is in this class,"
>                   , "then the subalphabet %<v:T> is provided."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c:isLTT>"
>                   ]))
>             ]))
>       , ( Left ":isTRDef"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "tier-based generalized definite"
>                 , unwords
>                   [ "Determine if <%<a:expr>> is"
>                   , "tier-based reverse definite"
>                   , "with respect to the current %<v:universe>."
>                   , "These are the languages which make distinctions"
>                   , "based on the prefixes"
>                   , "of length at most %<v:k> of words"
>                   , "after projection to some subalphabet,"
>                   , "%<v:T>."
>                   , "If the language is in this class,"
>                   , "then the tier %<v:T> and the value"
>                   , "of this parameter, %<v:k> are provided."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::isRDef>, %<c::isMTRDef>"
>                   ]))
>             ]))
>       , ( Left ":isTrivial"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "trivial"
>                 , unwords
>                   [ "Determine if <%<a:expr>> is trivial"
>                   , "with respect to the current %<v:universe>."
>                   , "Only two languages are trivial:"
>                   , "the empty language and its complement."
>                   ]))
>             ]))
>       , ( Left ":isTSL"
>         , ( [ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "tier-based strictly locally"
>                 , unwords
>                   [ "Determine if <%<a:expr>> is"
>                   , "tier-based strictly %<v:k>-local"
>                   , "with respect to the current %<v:universe>."
>                   , "That is, is there some subalphabet %<v:T>"
>                   , "such that after projection to %<v:T>,"
>                   , "the language satisifies %<c::isSL>."
>                   , "If the language is in this class,"
>                   , "then the subalphabet %<v:T> is provided"
>                   , "as well as the %<v:k> of the strictly local"
>                   , "projection."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c:isSL>"
>                   ]))
>             ]))
>       , ( Left ":isVarietyM"
>         , ( [ArgS, ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "arbitrary *-variety"
>                 , unwords
>                   [ "Determine if the syntactic monoid of"
>                   , "<%<a:expr>>"
>                   , "satisfied the given equations and inequalities"
>                   , "with respect to the current %<v:universe>."
>                   , "The <%<a:string>> should be a valid"
>                   , "variety specification:"
>                   , "a semicolon-separated collection"
>                   , "of equalities and inequalities"
>                   , "involving universally-quantified variables"
>                   , "or the literals 1 and 0,"
>                   , "all wrapped in square brackets."
>                   , "%<p:>"
>                   , "The literal 1 refers to the identity element,"
>                   , "where 1%<v:x>=%<v:x>=%<v:x>1 for all %<v:x>."
>                   , "The literal 0 refers to a two-sided zero,"
>                   , "where 0%<v:x>=0=%<v:x>0 for all %<v:x>."
>                   , "Any single letter refers to a variable."
>                   , "Multiplication (concatenation) is denoted"
>                   , "by adjacency, and terms can be grouped"
>                   , "with parentheses."
>                   , "The * operator binds to the literal, variable,"
>                   , "or group to its left,"
>                   , "and maps that object to its unique"
>                   , "idempotent power."
>                   , "Equations are expressions"
>                   , "separated by an = sign,"
>                   , "and inequalities are expressions"
>                   , "separated by ≤ or ≥."
>                   , "The < and > symbols are synonyms for"
>                   , "≤ and ≥, respectively."
>                   , "Chains of relations are evaluated"
>                   , "by adjacent pairs:"
>                   , "[%<v:e><%<v:f>=%<v:g>]"
>                   , "indicates that the expression %<v:e>"
>                   , "is universally less than or equal to"
>                   , "the expression %<v:f>"
>                   , "in the syntactic order,"
>                   , "and that the expression %<v:f>"
>                   , "is universally equal to"
>                   , "the expression %<v:g>."
>                   , "%<p:>"
>                   , "For example, the variety of semilattices"
>                   , "(monoids that are both idempotent and"
>                   , "commutative)"
>                   , "can be specified as follows %<p:>"
>                   , "%<e:[x*=x;xy=yx]> %<p:>"
>                   , "To demonstrate that the language of"
>                   , "words which contain %<b:x> and %<b:y>"
>                   , "but not %<b:z> is a semilattice: %<p:>"
>                   , "%<e:%>% =a{/a}=b{/b}=c{/c}> %<-:>"
>                   , "%<e:%>% ⋀{a,b,¬c}> %<-:>"
>                   , "%<e:%>% :isVarietyM% [x*=x;xy=yx]% it> %<-:>"
>                   , "%<e:True>"
>                   ]))
>             ]))
>       , ( Left ":isVarietyS"
>         , ( [ArgS, ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "arbitrary +-variety"
>                 , unwords
>                   [ "Determine if the syntactic semigroup of"
>                   , "<%<a:expr>>"
>                   , "satisfied the given equations and inequalities"
>                   , "with respect to the current %<v:universe>."
>                   , "The equations are specied as in"
>                   , "%<c::isVarietyM>,"
>                   , "except that the literal 1"
>                   , "should not be used, as the neutral element"
>                   , "may not exist."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::isVarietyM>"
>                   ]))
>               ]))
>       , ( Left ":isVarietyT"
>         , ( [ArgS, ArgE], [ClassCat]
>           , Map.fromList
>             [ ( ""
>               , ( "arbitrary +-variety on a tier"
>                 , unwords
>                   [ "Determine if the projected subsemigroup of"
>                   , "<%<a:expr>>"
>                   , "satisfied the given equations and inequalities"
>                   , "with respect to the current %<v:universe>."
>                   , "The equations are specied as in"
>                   , "%<c::isVarietyM>,"
>                   , "except that the literal 1"
>                   , "should not be used, as the neutral element"
>                   , "may not exist."
>                   , "If these relations hold,"
>                   , "then the subalphabet %<v:T>"
>                   , "to which the language projects"
>                   , "is provided."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::isVarietyM> %<c::isVarietyS>"
>                   ]))
>               ]))
>       , ( Left ":Jmin"
>         , ( [ArgE], [GraphCat]
>           , Map.fromList
>             [ ( ""
>               , ( "display J-minimized form of <%<a:expr>>"
>                 , unwords
>                   [ "Show a J-minimal automaton representation"
>                   , "of <%<a:expr>> graphically."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::display>, %<c::eggbox>, %<t:VISUALIZATION>"
>                   ]))
>             ]))
>       , ( Left ":learnSL"
>         , ( [ArgI, ArgF], [LearnCat]
>           , Map.fromList
>             [ ( ""
>               , ( "infer %<v:k>-SL grammar, bind result to %<v:it>"
>                 , unwords
>                   [ "Read <%<a:file>> as a sequence of"
>                   , "newline-terminated words composed"
>                   , "of space-separated symbols,"
>                   , "and construct an <%<a:int>>-SL automaton"
>                   , "compatible with this data."
>                   , "Symbols not in the data are always rejected."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::isSL>"
>                   ]))
>             ]))
>       , ( Left ":learnSP"
>         , ( [ArgI, ArgF], [LearnCat]
>           , Map.fromList
>             [ ( ""
>               , ( "infer %<v:k>-SP grammar, bind result to %<v:it>"
>                 , unwords
>                   [ "Read <%<a:file>> as a sequence of"
>                   , "newline-terminated words composed"
>                   , "of space-separated symbols,"
>                   , "and construct an <%<a:int>>-SP automaton"
>                   , "compatible with this data."
>                   , "Symbols not in the data are always rejected."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::isSP>"
>                   ]))
>             ]))
>       , ( Left ":learnTSL"
>         , ( [ArgI, ArgF], [LearnCat]
>           , Map.fromList
>             [ ( ""
>               , ( "infer %<v:k>-TSL grammar, bind result to %<v:it>"
>                 , unwords
>                   [ "Read <%<a:file>> as a sequence of"
>                   , "newline-terminated words composed"
>                   , "of space-separated symbols,"
>                   , "and construct a tier-based"
>                   , "<%<a:int>>-SL automaton"
>                   , "compatible with this data."
>                   , "Symbols not in the data are always rejected."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::isTSL>"
>                   ]))
>             ]))
>       , ( Left ":loadstate"
>         , ( [ArgF], [IOCat]
>           , Map.fromList
>             [ ( ""
>               , ( "restore state from a file"
>                 , unwords
>                   [ "Restore a state previously written by"
>                   , "%<c::savestate> from <%<a:file>>."
>                   , "This format is not stable across updates."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::savestate>"
>                   ]))
>             ]))
>       , ( Left ":orderJ"
>         , ( [ArgE], [GraphCat]
>           , Map.fromList
>             [ ( ""
>               , ( "display Green's J-order"
>                 , unwords
>                   [ "Graphically display a Hasse diagram"
>                   , "of the order induced by Green's J-relation"
>                   , "on the given <%<a:expr>>."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::orderL>, %<c:orderR>, %<t:VISUALIZATION>"
>                   ]))
>             ]))
>       , ( Left ":orderL"
>         , ( [ArgE], [GraphCat]
>           , Map.fromList
>             [ ( ""
>               , ( "display Green's L-order"
>                 , unwords
>                   [ "Graphically display a Hasse diagram"
>                   , "of the order induced by Green's L-relation"
>                   , "on the given <%<a:expr>>."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::orderJ>, %<c:orderR>, %<t:VISUALIZATION>"
>                   ]))
>             ]))
>       , ( Left ":orderR"
>         , ( [ArgE], [GraphCat]
>           , Map.fromList
>             [ ( ""
>               , ( "display Green's R-order"
>                 , unwords
>                   [ "Graphically display a Hasse diagram"
>                   , "of the order induced by Green's R-relation"
>                   , "on the given <%<a:expr>>."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::orderJ>, %<c:orderL>, %<t:VISUALIZATION>"
>                   ]))
>             ]))
>       , ( Left ":psg"
>         , ( [ArgE], [GraphCat]
>           , Map.fromList
>             [ ( ""
>               , ( "display powerset graph of expression"
>                 , unwords
>                   [ "Show the powerset graph of"
>                   , "a normal-form automaton representation"
>                   , "of <%<a:expr>> graphically"
>                   , "using an external %<c:display> program."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::display>, %<c::dotPSG>, %<t:VISUALIZATION>"
>                   ]))
>             ]))
>       , ( Left ":quit"
>         , ( [], []
>           , Map.fromList
>             [ ( ""
>               , ( "exit plebby"
>                 , unwords
>                   [ "Leave the interpreter."
>                   , "The program also exits"
>                   , "when the input reaches end of file."
>                   ]))
>             ]))
>       , ( Left ":read"
>         , ( [ArgF], [IOCat]
>           , Map.fromList
>             [ ( ""
>               , ( "read PLEB file, bind to %<v:it>"
>                 , unwords
>                   [ "Read <%<a:file>> as a %<b:PLEB> program,"
>                   , "assimilating all bindings."
>                   , "If there are any bare expressions,"
>                   , "the last one is assigned to"
>                   , "the special variable %<v:it>."
>                   ]))
>             ]))
>       , ( Left ":readATT"
>         , ( [ArgF, ArgF, ArgF], [IOCat]
>           , Map.fromList
>             [ ( ""
>               , ( "read AT&T files, bind input-projection to %<v:it>"
>                 , unwords
>                   [ "Read an AT&T-format transducer from the three"
>                   , "<%<a:file>> arguments (transitions, input"
>                   , "symbols, and output symbols), and store"
>                   , "the input-projection of the result in the"
>                   , "special variable %<v:it>."
>                   , "If %<b:_> is given as the name"
>                   , "of a symbol table, then no file is read"
>                   , "for that table."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::readATTO>, %<c::writeATT>"
>                   ]))
>             ]))
>       , ( Left ":readATTO"
>         , ( [ArgF, ArgF, ArgF], [IOCat]
>           , Map.fromList
>             [ ( ""
>               , ( "read AT&T files, bind output-projection to %<v:it>"
>                 , unwords
>                   [ "Read an AT&T-format transducer from the three"
>                   , "<%<a:file>> arguments (transitions, input"
>                   , "symbols, and output symbols), and store"
>                   , "the output-projection of the result in the"
>                   , "special variable %<v:it>."
>                   , "If %<b:_> is given as the name"
>                   , "of a symbol table, then no file is read"
>                   , "for that table."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::readATT>, %<c::writeATT>"
>                   ]))
>             ]))
>       , ( Left ":readBin"
>         , ( [ArgF], [IOCat]
>           , Map.fromList
>             [ ( ""
>               , ( "read binary expression, bind to %<v:it>"
>                 , unwords
>                   [ "The binary format is not stable across updates."
>                   , "Read a binary file directly to its internal"
>                   , "representation, and store the result in"
>                   , "the special variable %<v:it>."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::write>"
>                   ]))
>             ]))
>       , ( Left ":readJeff"
>         , ( [ArgF], [IOCat]
>           , Map.fromList
>             [ ( ""
>               , ( "read expression in Jeff's format, bind to %<v:it>"
>                 , unwords
>                   [ "One of the file formats used in"
>                   , "the StressTyp2 database."
>                   , "Read a Jeff-file as an automaton"
>                   , "and store the result in"
>                   , "the special variable %<v:it>."
>                   ]))
>             ]))
>       , ( Left ":reset"
>         , ( [], [EnvironmentCat]
>           , Map.fromList
>             [ ( ""
>               , ( "purge the current environment"
>                 , unwords
>                   [ "Remove all bindings from the current"
>                   , "environment and return to a fresh state."
>                   ]))
>             ]))
>       , ( Left ":restoreUniverse"
>         , ( [], [EnvironmentCat]
>           , Map.fromList
>             [ ( ""
>               , ( "make %<v:universe> contain only necessary symbols"
>                 , unwords
>                   [ "Set the special variable %<v:universe>"
>                   , "to the symbol set that contains all and only"
>                   , "those symbols used in other bindings"
>                   , "in the current environment."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::restrict>"
>                   ]))
>             ]))
>       , ( Left ":restrict"
>         , ( [], [EnvironmentCat]
>           , Map.fromList
>             [ ( ""
>               , ( "remove non-%<v:universe> symbols from environment"
>                 , unwords
>                   [ "Remove all symbols that are not in the"
>                   , "current %<v:universe> from all current"
>                   , "bindings."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::restoreUniverse>"
>                   ]))
>             ]))
>       , ( Left ":savestate"
>         , ( [ArgF], [IOCat]
>           , Map.fromList
>             [ ( ""
>               , ( "save state to a file"
>                 , unwords
>                   [ "Write the current state to <%<a:file>>"
>                   , "to be loaded by %<c::savestate>."
>                   , "This format is not stable across updates."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::loadstate>"
>                   ]))
>             ]))
>       , ( Left ":show"
>         , ( [ArgV], [EnvironmentCat]
>           , Map.fromList
>             [ ( ""
>               , ( "print meaning(s)"
>                 , unwords
>                   [ "Print the current bindings of <%<v:var>>,"
>                   , "if any, or a message indicating that"
>                   , "it is not bound."
>                   , "As symbol sets and expressions are stored"
>                   , "separately, the same name can have"
>                   , "multiple meanings depending on context."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::bindings>, %<c::unset>"
>                   ]))
>             ]))
>       , ( Left ":strictSubset"
>         , ( [ArgE, ArgE], [ComparisonCat]
>           , Map.fromList
>             [ ( ""
>               , ( "compare expressions for subset relation"
>                 , unwords
>                   [ "Determine whether the first <%<a:expr>>"
>                   , "is a proper subset of the second"
>                   , "with respect to the current %<v:universe>."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::subset>"
>                   ]))
>             ]))
>       , ( Left ":subset"
>         , ( [ArgE, ArgE], [ComparisonCat]
>           , Map.fromList
>             [ ( ""
>               , ( "compare expressions for subset relation"
>                 , unwords
>                   [ "Determine whether the first <%<a:expr>>"
>                   , "is a (not necessarily proper) subset"
>                   , "of the second"
>                   , "with respect to the current %<v:universe>."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::strictSubset>"
>                   ]))
>             ]))
>       , ( Left ":synmon"
>         , ( [ArgE], [GraphCat]
>           , Map.fromList
>             [ ( ""
>               , ( "display syntactic monoid of expression"
>                 , unwords
>                   [ "Show the right Cayley graph of"
>                   , "the syntactic monoid"
>                   , "of %<a:expr> graphically"
>                   , "using an external %<c:display> program."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::display>, %<c::dotPSG>, %<t:VISUALIZATION>"
>                   ]))
>             ]))
>       , ( Left ":synord"
>         , ( [ArgE], [GraphCat]
>           , Map.fromList
>             [ ( ""
>               , ( "display syntactic order"
>                 , unwords
>                   [ "Graphically display a Hasse diagram"
>                   , "of the syntactic order"
>                   , "on the given <%<a:expr>>."
>                   , "This is the order where %<v:x> is less than"
>                   , "or equal to %<v:y> if and only if"
>                   , "for all strings %<v:u> and %<v:v>,"
>                   , "if %<v:uyv> is in the language"
>                   , "then so too is %<v:uxv>."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::orderJ>, %<c::orderL>, %<c:orderR>,"
>                   , "%<t:VISUALIZATION>"
>                   ]))
>             ]))
>       , ( Left ":unset"
>         , ( [ArgV], [EnvironmentCat]
>           , Map.fromList
>             [ ( ""
>               , ( "remove from the environment"
>                 , unwords
>                   [ "Remove all bindings for <%<v:var>>"
>                   , "from the current environment."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::bindings>, %<c::show>"
>                   ]))
>             ]))
>       , ( Left ":write"
>         , ( [ArgF, ArgE], [IOCat]
>           , Map.fromList
>             [ ( ""
>               , ( "write binary expression"
>                 , unwords
>                   [ "The binary format is not stable across updates."
>                   , "Write a binary representation of <%<a:expr>>"
>                   , "to the <%<a:file>>."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::readBin>"
>                   ]))
>             ]))
>       , ( Left ":writeATT"
>         , ( [ArgF, ArgF, ArgF, ArgE], [IOCat]
>           , Map.fromList
>             [ ( ""
>               , ( "write AT&T files"
>                 , unwords
>                   [ "Write an AT&T-format transducer to the three"
>                   , "<%<a:file>> arguments (transitions, input"
>                   , "symbols, and output symbols), to represent"
>                   , "the given <%<a:expr>>."
>                   , "If %<b:_> is given as the name"
>                   , "of a symbol table, then no file is written"
>                   , "for that table."
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<c::readATT>, %<c::readATTO>"
>                   ]))
>             ]))
>       , ( Right ClassCat
>         , ( [], []
>           , Map.fromList
>             [ ( ""
>               , ( "classification"
>                 , unwords
>                   [ "These commands determine whether a given"
>                   , "expression is in the corresponding class"
>                   , "with respect to the current %<v:universe>."
>                   ]))
>             ]))
>       , ( Right CommandCat
>         , ( [], []
>           , Map.fromList
>             [ ( ""
>               , ( "list of commands"
>                 , "Below is a list of every documented command."
>                 ))
>             ]))
>       , ( Right ComparisonCat
>         , ( [], []
>           , Map.fromList
>             [ ( ""
>               , ( "comparison"
>                 , unwords
>                   [ "These commands take two expressions"
>                   , "and determine their relationships"
>                   , "to one another. Typically this is"
>                   , "with respect to the current %<v:universe>,"
>                   , "although %<c::cequal> and %<c::cimplies>"
>                   , "query the semantics of the expressions"
>                   , "in all possible universes."
>                   ]))
>             ]))
>       , ( Right ConfigCat
>         , ( [], []
>           , Map.fromList
>             [ ( ""
>               , ( "configuration file"
>                 , unwords
>                   [ "The configuration file, located at"
>                   , "${%<v:XDG_CONFIG_HOME>}/plebby/config.ini"
>                   , "or, alternatively, at ~/.plebby"
>                   , "allows a few aspects of the interpreter"
>                   , "to be customized."
>                   , "The following keys are available: %<p:>"
>                   , "%<b:[options]> %<-:>"
>                   , "* %<b:formatting> - true/false,"
>                   , "dictates whether these messages are formatted"
>                   , "%<-:>"
>                   , "* %<b:prompt> - a string to use as a prompt."
>                   , "%<-:>"
>                   , "%<b:[programs]> %<-:>"
>                   , "* %<b:dot> - command-line to invoke %<c:dot>"
>                   , "%<-:>"
>                   , "* %<b:display> - command-line to invoke"
>                   , "%<c:display> %<-:>"
>                   , "* %<b:pager> - command-line overriding"
>                   , "${%<v:PAGER>} %<p:>"
>                   , "The prompt can be formatted with ANSI-escapes"
>                   , "followed by \"\\2\"."
>                   , "A sample configuration is as follows."
>                   , "Currently, the section headings are optional,"
>                   , "but this may change in a future release."
>                   , "%<p:>"
>                   , "%<e:[options]> %<-:>"
>                   , "%<e:formatting% =% true> %<-:>"
>                   , "%<e:prompt% =%"
>                   , "\"\\27[0;34m\\2%>\\27[m\\2% \"> %<-:>"
>                   , "%<e:[programs]> %<-:>"
>                   , "%<e:dot% =% dot% -Tpng> %<-:>"
>                   , "%<e:display% =% display> %<-:>"
>                   , "%<e:pager% =% less% -FsR>"
>                   , "%<p:>"
>                   , "Some systems have GraphViz compiled"
>                   , "with an image-viewer built in."
>                   , "On those systems, the following configuration"
>                   , "allows that viewer to be used. %<p:>"
>                   , "%<e:[programs]> %<-:>"
>                   , "%<e:dot% =% cat> %<-:>"
>                   , "%<e:display% =% dot% -Txlib>"
>                   ]))
>             ]))
>       , ( Right EnvironmentCat
>         , ( [], []
>           , Map.fromList
>             [ ( ""
>               , ( "environment manipulation"
>                 , unwords
>                   [ "These commands inspect or directly modify"
>                   , "the environment."
>                   ]))
>             ]))
>       , ( Right GraphCat
>         , ( [], []
>           , Map.fromList
>             [ ( ""
>               , ( "graphical display of automata and semigroups"
>                 , unwords
>                   [ "All commands that display graphical output"
>                   , "require the %<c:dot> and %<c:display> programs"
>                   , "to be accessible on your ${%<v:PATH>},"
>                   , "where %<c:dot> is GraphViz-compatible"
>                   , "and %<c:display> can accept a PNG-formatted"
>                   , "image over the standard input and display it"
>                   , "appropriately. ImageMagick, for example,"
>                   , "contains such a %<c:display> program."
>                   , "%<p:>"
>                   , "The keys %<v:dot> and %<v:display> in the"
>                   , "configuration file can be used to specify"
>                   , "alternative programs for this purpose,"
>                   , "although strings are not handled as robustly"
>                   , "as they might be in the shell."
>                   ]))
>             ]))
>       , ( Right IOCat
>         , ( [], []
>           , Map.fromList
>             [ ( ""
>               , ( "file input and output"
>                 , unwords
>                   [ "These commands interact with external files."
>                   ]))
>             ]))
>       , ( Right LearnCat
>         , ( [], [IOCat]
>           , Map.fromList
>             [ ( ""
>               , ( "grammatical inference"
>                 , unwords
>                   [ "Read an input file and infer a grammar"
>                   , "compatible with the words in the file."
>                   , "Unless otherwise specified,"
>                   , "the inference is some instantiation"
>                   , "of a string-extension learner."
>                   ]))
>             ]))
>       , ( Right SyntaxCat
>         , ( [], []
>           , Map.fromList
>             [ ( ""
>               , ( "overview of the language"
>                 , unwords
>                   [ "This should be filled in later."
>                   ]))
>             ]))
>       , ( Right TutorialCat
>         , ( [], []
>           , Map.fromList
>             [ ( ""
>               , ( "introductory tutorial"
>                 , unwords
>                   [ "This should be filled in later."
>                   ]))
>             ]))
>       ]
