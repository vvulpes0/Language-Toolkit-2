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
* H: subheader
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
>             , ('h', ("\27[1;33m","\27[m")) -- header
>             , ('H', ("\27[33m","\27[m")) -- header
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
> spanLineRS _ (('%' : '<' : 'H' : ':' : s):xs)
>     = (["%<H:"++s],xs,False)
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
>               , ( "tier-based reverse definite"
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
>               , ( "read Pleb file, bind to %<v:it>"
>                 , unwords
>                   [ "Read <%<a:file>> as a %<b:Pleb> program,"
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
>               , ( "compare expressions for proper subset relation"
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
>                   [ "The Piecewise-Local Expression Builder (PLEB)"
>                   , "offers a powerful logic-based system for"
>                   , "constructing and manipulating regular languages."
>                   , "The interpreter, plebby, augments this system"
>                   , "with analysis and visualization commands,"
>                   , "to empower those who study formal languages."
>                   , "In the interpreter, each line consists of"
>                   , "either a command (where the first character"
>                   , "of the line is a colon)"
>                   , "or some number of complete statements."
>                   , "A statement is either an explicit assignment,"
>                   , "or an expression to be treated as an"
>                   , "assignment to the special variable %<v:it>."
>                   , "%<p:> %<H:Basic% Syntax>"
>                   , "In general,"
>                   , "everything is written in Polish notation,"
>                   , "where each operator applies to the expression"
>                   , "or sequence of expressions"
>                   , "that follows it."
>                   , "Instead of something like"
>                   , "%<e:exp% :=% \172(x% \8743% y% \8743% z)>,"
>                   , "in the Pleb language we would write"
>                   , "%<e:=exp% \172\8896{x,y,z}>."
>                   , "This avoids the ambiguity of precedence"
>                   , "that arises with infix operators"
>                   , "and often simplifies expressions."
>                   , "%<p:>"
>                   , "Comments span to the end of a line"
>                   , "following a %<b:#> character."
>                   , "A command is a line beginning with a colon"
>                   , "followed immediately by the name of the command"
>                   , "and then zero or more whitespace-separated"
>                   , "arguments."
>                   , "For example, you can reach this page as follows."
>                   , "%<p:>"
>                   , "%<e:%>% :help% LANGUAGE>"
>                   , "%<p:>"
>                   , "See the other available topics"
>                   , "for more information,"
>                   , "including a complete list of commands."
>                   , "%<p:>"
>                   , "%<e:%>% :help% COMMANDS>"
>                   , "%<p:>"
>                   , "The rest of this topic describes"
>                   , "the Pleb language, as implemented"
>                   , "in the interpreter."
>                   , "Note that Pleb files (unlike the interpreter)"
>                   , "allow for multiline statements,"
>                   , "but have no support for the interpreter commands"
>                   , "that allow for visualization and analysis."
>                   , "See %<c::read> and %<c::import>"
>                   , "for more on this distinction."
>                   , "%<p:>"
>                   , "Symbol sets and expressions"
>                   , "will be described shortly."
>                   , "An assignment is the %<b:=> sign,"
>                   , "then optionally some whitespace,"
>                   , "followed by a name, some whitespace,"
>                   , "and then a symbol set or an expression."
>                   , "The whitespace may be omitted before"
>                   , "certain characters, such as the opening"
>                   , "brace of a set union."
>                   , "%<p:>"
>                   , "A name is a letter as defined by Unicode"
>                   , "followed by any sequence of characters"
>                   , "other than whitespace or any of the following:"
>                   , "%<b:[>, %<b:]>,"
>                   , "%<b:(>, %<b:)>,"
>                   , "%<b:{>, %<b:}>,"
>                   , "%<b:%<>, %<b:%>>,"
>                   , "or %<b:,>."
>                   , "Note that %<b:#> is allowed in names;"
>                   , "comments must be separated"
>                   , "from names by whitespace or one of these"
>                   , "other breaking symbols."
>                   , "%<p:>"
>                   , "A symbol set (%<v:symbols>)"
>                   , "can be specified as: %<p:>"
>                   , "* A singleton: a name immediately preceded"
>                   , "by a slash (%<b:/>%<v:name>)"
>                   , "%<-:>"
>                   , "* A union: one or more sets"
>                   , "enclosed by braces (%<b:{>...%<b:}>)"
>                   , "or parentheses (%<b:(>...%<b:)>)"
>                   , "%<-:>"
>                   , "* An intersection: one or more sets"
>                   , "enclosed by square brackets (%<b:[>...%<b:]>),"
>                   , "or %<-:>"
>                   , "* A variable: a name not preceded by a slash."
>                   , "%<p:>"
>                   , "Every symbol that appears in an assignment"
>                   , "is also added to the special symbol set"
>                   , "%<v:universe>."
>                   , "This is a variable like any other,"
>                   , "and can be explicitly rebound if desired."
>                   , "In general, it is good practice to define"
>                   , "your intended working alphabet"
>                   , "with a sequence of assignments"
>                   , "such as the following:"
>                   , "%<p:>"
>                   , "%<e:%>% =a{/a}=b{/b}=c{/c}>"
>                   , "%<p:>"
>                   , "This defines %<v:a>, %<v:b>, and %<v:c>"
>                   , "as the singleton sets corresponding"
>                   , "to their names."
>                   , "Equivalently, one could write the following:"
>                   , "%<p:>"
>                   , "%<e:%>% =a% /a% =b% /b% =c% /c>"
>                   , "%<p:>"
>                   , "In this case,"
>                   , "the spaces surrounding the singletons"
>                   , "are mandatory,"
>                   , "as neither the slash nor the equal sign"
>                   , "is a name-breaking character."
>                   , "In either case, this allows the use of"
>                   , "the names %<v:a>, %<v:b>, and %<v:c>"
>                   , "as symbols in expressions"
>                   , "without having to prefix them by slash."
>                   , "Notice that this line consists of"
>                   , "three distinct assignments."
>                   , "A new statement begins where another ends."
>                   , "Statements may not span multiple lines,"
>                   , "but lines act as transactions:"
>                   , "an error anywhere on the line"
>                   , "prevents all statements on that line"
>                   , "from executing."
>                   , "%<p:>"
>                   , "An expression is a variable,"
>                   , "a piecewise-local factor,"
>                   , "the application of a monadic operator,"
>                   , "or the application of a variadic operator."
>                   , "Variables are bare names,"
>                   , "just as for symbol sets."
>                   , "Expressions and symbol sets"
>                   , "have their own unique lookup tables,"
>                   , "so the same name might refer"
>                   , "to an expression and to a symbol set"
>                   , "in different contexts."
>                   , "%<p:> %<H:Factors>"
>                   , "The basic form of a factor"
>                   , "is a sequence of symbol sets"
>                   , "between angle-brackets"
>                   , "(%<b:\10216>...%<b:\10217>)."
>                   , "Whitespace indicates adjacency,"
>                   , "while commas allow for arbitrary"
>                   , "intervening material."
>                   , "For example, %<b:\10216/a /b,/c /a\10217>"
>                   , "asserts that there is an %<b:ab>"
>                   , "substring, followed at some point"
>                   , "by a %<b:ca> substring later in the word."
>                   , "One can anchor the leftmost substring"
>                   , "to the left edge of the word"
>                   , "with %<b:\8906>,"
>                   , "or the rightmost to the right edge"
>                   , "with %<b:\8905>."
>                   , "If both anchors are used,"
>                   , "they must be given in order"
>                   , "with no intervening whitespace."
>                   , "For instance, %<b:\8906\8905\10216/a\10217>"
>                   , "asserts that the word is precisely"
>                   , "%<b:a>, with no additional material"
>                   , "on either side."
>                   , "%<p:>"
>                   , "There are two operators that combine factors"
>                   , "and return factors as results."
>                   , "The %<b:.\10216>...%<b:\10217> syntax"
>                   , "merges the factors such that"
>                   , "the rightmost substring of one"
>                   , "must be adjacent to the leftmost of the next."
>                   , "The %<b:..\10216>...%<b:\10217> syntax"
>                   , "merges them with arbitrary gaps."
>                   , "In either case,"
>                   , "only the outermost anchors are retained."
>                   , "Internal anchors are forgotten entirely."
>                   , "For example,"
>                   , "%<b:.\10216\10216/a\10217,\10216/b,/c\10217"
>                         ++ ",\10216/a\10217\10217>"
>                   , "is equivalent to"
>                   , "%<b:\10216/a /b,/c /a\10217>."
>                   , "The real power of this approach"
>                   , "becomes apparent when the internal factors"
>                   , "are variables."
>                   , "%<p:>"
>                   , "There are ASCII equivalents for each of"
>                   , "the symbols here."
>                   , "Angle-brackets can be replaced by"
>                   , "the less-than and greater-than signs."
>                   , "The left-anchor is equivalent to"
>                   , "%<b:%%|>,"
>                   , "and the right to %<b:|%%>."
>                   , "Thus %<b:%%||%%%</a,{/b,/c}%>>"
>                   , "represents the set of words"
>                   , "that begin with %<b:a>"
>                   , "and end with either %<b:b> or %<b:c>."
>                   , "%<p:> %<H:Monadic% Operators>"
>                   , "This section describes the operators"
>                   , "which accept only a single argument."
>                   , "The operator applies to the expression"
>                   , "that follows it."
>                   , "Every operator has a Unicode version"
>                   , "and one or more plain-ASCII versions."
>                   , "They are listed in order of preference,"
>                   , "separated by a vertical bar,"
>                   , "but are for all intents and purposes"
>                   , "equivalent."
>                   , "%<p:>"
>                   , "%<b:\172> | %<b:~> | %<b:!> %<-:>"
>                   , "Logical negation."
>                   , "Equivalent to the set complement."
>                   , "Note that the semantics of this operation"
>                   , "(and all others)"
>                   , "is preserved under changing the alphabet."
>                   , "In particular,"
>                   , "this is not a relative complement."
>                   , "%<p:>"
>                   , "%<b:*> | %<b:\8727> %<-:>"
>                   , "Iteration closure."
>                   , "Accept words which can be decomposed"
>                   , "into the concatenation of zero or more"
>                   , "copies of the operand."
>                   , "Note: factor-expressions"
>                   , "that are not fully anchored"
>                   , "may have arbitrary strings"
>                   , "at the non-anchored ends."
>                   , "%<p:>"
>                   , "%<b:+> %<-:>"
>                   , "The expression %<b:+>%<v:x>"
>                   , "is equivalent to"
>                   , "%<b:\8729(>%<v:x>%<b:,*>%<v:x>%<b:)>."
>                   , "%<p:>"
>                   , "%<b:\8593> | %<b:^> %<-:>"
>                   , "Upward closure."
>                   , "Accept all and only those strings"
>                   , "that can be formed by inserting"
>                   , "zero or more symbols"
>                   , "into a string accepted by the operand."
>                   , "%<p:>"
>                   , "%<b:\8644> | %<b:-> %<-:>"
>                   , "Reversal."
>                   , "%<p:>"
>                   , "%<b:\8595> | %<b:$> %<-:>"
>                   , "Downward closure."
>                   , "Accept all and only those strings"
>                   , "that can be formed by deleting"
>                   , "zero or more symbols"
>                   , "from a string accepted by the operand."
>                   , "%<p:>"
>                   , "%<b:[> <%<v:symbols>> [ %<b:,> <%<v:symbols>>"
>                   , "... ] %<b:]> %<-:>"
>                   , "Tier projection."
>                   , "This is one or more symbol sets,"
>                   , "separated by commas"
>                   , "with the whole wrapped in square brackets."
>                   , "The union of the symbol sets"
>                   , "specifies a tier of salient symbols"
>                   , "on which to apply the operand."
>                   , "This yields the language of all words"
>                   , "whose projection to this tier"
>                   , "satisfies the operand."
>                   , "%<p:>"
>                   , "%<b:|> <%<v:symbols>> [ %<b:,> <%<v:symbols>>"
>                   , "... ] %<b:|> %<-:>"
>                   , "Tier neutralization."
>                   , "This is one or more symbol sets,"
>                   , "separated by commas"
>                   , "with the whole surrounded by vertical bars."
>                   , "The union of the symbol sets"
>                   , "specifies a tier of neutral symbols"
>                   , "on which to apply the operand."
>                   , "This yields the language of all words"
>                   , "whose projection to symbols not in this set"
>                   , "satisfies the operand."
>                   , "Where the tier-projection operator"
>                   , "states which symbols are to be retained,"
>                   , "this operator states which are to be ignored."
>                   , "In this sense, they compute the same operation,"
>                   , "but the semantics differ"
>                   , "when the %<v:universe> changes."
>                   , "%<p:> %<H:Variadic% Operators>"
>                   , "This section describes the operators"
>                   , "which accept any number of arguments,"
>                   , "including zero."
>                   , "The operator applies to the following"
>                   , "group of expressions,"
>                   , "which is a pair of parentheses (%<b:(>...%<b:)>)"
>                   , "or braces (%<b:{>...%<b:}>)"
>                   , "surrounding a comma-separated list"
>                   , "of expressions."
>                   , "Generally, braces are preferred"
>                   , "for commutative operations"
>                   , "and parentheses for others,"
>                   , "but the two are entirely interchangeable."
>                   , "The base case for empty lists"
>                   , "is specified for each operation individually."
>                   , "As with the monadic operators,"
>                   , "the synonyms are listed in order of preference,"
>                   , "separated by a vertical bar."
>                   , "%<p:>"
>                   , "%<b:\8896> | %<b:\8743> | %<b:\8898>"
>                   , "| %<b:\8745> | %<b:/\\> %<-:>"
>                   , "Set intersection (logical conjunction)."
>                   , "The empty intersection"
>                   , "is the universal language, %<b:\10216\10217>."
>                   , "%<p:>"
>                   , "%<b:\8897> | %<b:\8744> | %<b:\8899>"
>                   , "| %<b:\8745> | %<b:\\/> %<-:>"
>                   , "Set union (logical disjunction)."
>                   , "The empty union"
>                   , "is the empty language, %<b:\172\10216\10217>."
>                   , "%<p:>"
>                   , "%<b:\8729> | %<b:@> %<-:>"
>                   , "Concatenation."
>                   , "Note that non-anchored ends"
>                   , "of factor-expressions automatically allow"
>                   , "arbitrary strings to occur,"
>                   , "so this concatenation may not be"
>                   , "what one expects."
>                   , "It may be better to use the %<b:.%<>...%<b:%>>"
>                   , "form to adjoin factors."
>                   , "The empty concatenation is the empty string,"
>                   , "%<b:\8906\8905\10216\10217>."
>                   , "%<p:>"
>                   , "%<b:\8729\8729> | %<b:@@> %<-:>"
>                   , "Gapped concatenation."
>                   , "Equivalent to normal concatenation,"
>                   , "except that arbitrary strings may be inserted"
>                   , "between the operands."
>                   , "The empty gapped concatenation"
>                   , "is the empty string,"
>                   , "%<b:\8906\8905\10216\10217>."
>                   , "%<p:>"
>                   , "%<b:\10722> | %<b:|_|_|> %<-:>"
>                   , "Shuffle product."
>                   , "The shuffle product of %<v:A> and %<v:B>"
>                   , "is the set of words formed by taking"
>                   , "a word from %<v:A> and"
>                   , "a word from %<v:B> and interleaving them."
>                   , "The empty shuffle is the empty string,"
>                   , "%<b:\8906\8905\10216\10217>."
>                   , "%<p:>"
>                   , "%<b:\8657> | %<b:.^.> %<-:>"
>                   , "Infiltration product."
>                   , "The infiltration product of %<v:A> and %<v:B>"
>                   , "is the set of words formed by taking"
>                   , "a word from %<v:A> and"
>                   , "a word from %<v:B> and interleaving them,"
>                   , "with overlaps."
>                   , "That is, if the two words both contain"
>                   , "the symbol %<v:x>, the interleaving"
>                   , "might contain only one instance of %<v:x>"
>                   , "if the order requirements are fulfilled."
>                   , "The empty infiltration is the empty string,"
>                   , "%<b:\8906\8905\10216\10217>."
>                   , "%<p:>"
>                   , "%<b:\\\\> %<-:>"
>                   , "Left-quotient."
>                   , "The quotient %<v:A>\\%<v:B>"
>                   , "is the set of strings that can be appended"
>                   , "to strings in %<v:A>"
>                   , "in order to obtain a string in %<v:B>."
>                   , "This generalizes the Brzozowski derivative."
>                   , "The empty quotient is the empty string,"
>                   , "%<b:\8906\8905\10216\10217>."
>                   , "%<p:>"
>                   , "%<b://> %<-:>"
>                   , "Right-quotient."
>                   , "The quotient %<v:B>/%<v:A>"
>                   , "is the set of strings that can be prepended"
>                   , "to strings in %<v:A>"
>                   , "in order to obtain a string in %<v:B>."
>                   , "This generalizes the Brzozowski derivative."
>                   , "The empty quotient is the empty string,"
>                   , "%<b:\8906\8905\10216\10217>."
>                   , "%<p:> %<h:EXAMPLES>"
>                   , "For a more in-depth worked example,"
>                   , "see the %<t:TUTORIAL>."
>                   , "Meanwhile, some simple examples follow."
>                   , "%<p:>"
>                   , "Define %<v:even-a> as the set of words"
>                   , "which contain an even number of occurrences"
>                   , "of the letter %<b:a>,"
>                   , "and ensure the %<v:universe> contains at least"
>                   , "{%<b:a>,%<b:b>,%<b:c>}."
>                   , "%<p:>"
>                   , "%<e:%>% =a% /a% =b% /b% =c% /c> %<-:>"
>                   , "%<e:%>% =even-a% [a]*\8906\8905\10216a% a\10217>"
>                   , "%<p:>"
>                   , "Define a constraint %<v:harmony>"
>                   , "asserting that words which contain"
>                   , "%<b:o> or %<b:u>"
>                   , "do not contain"
>                   , "%<b:e> or %<b:i>, and vice versa."
>                   , "%<p:>"
>                   , "%<e:%>% =a{/a}=e{/e}=i{/i}=o{/o}=u{/u}> %<-:>"
>                   , "%<e:%>% =t{/t}=k{/k}=p{/p}> %<-:>"
>                   , "%<e:%>% =harmony% \172\8896{\10216{o,u}\10217,"
>                         ++ "\10216{e,i}\10217}>"
>                   , "%<p:>"
>                   , "The same constraint as above,"
>                   , "but expressed as a union."
>                   , "%<p:>"
>                   , "%<e:%>% =a{/a}=e{/e}=i{/i}=o{/o}=u{/u}> %<-:>"
>                   , "%<e:%>% =t{/t}=k{/k}=p{/p}> %<-:>"
>                   , "%<e:%>% =harmony% \8897{\172\10216{o,u}\10217,"
>                         ++ "\172\10216{e,i}\10217}>"
>                   , "%<p:>"
>                   , "Test the two %<v:harmony> expressions"
>                   , "for logical equivalence"
>                   , "in every possible %<v:universe>."
>                   , "%<p:>"
>                   , "%<e:%>% =a{/a}=e{/e}=i{/i}=o{/o}=u{/u}> %<-:>"
>                   , "%<e:%>% =t{/t}=k{/k}=p{/p}> %<-:>"
>                   , "%<e:%>% :cequal"
>                         ++ "% \172\8896{\10216{o,u}\10217,"
>                         ++ "\10216{e,i}\10217}"
>                         ++ "% \8897{\172\10216{o,u}\10217,"
>                         ++ "\172\10216{e,i}\10217}> %<-:>"
>                   , "%<e:True>"
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<t:TUTORIAL>"
>                   ]))
>             ]))
>       , ( Right TutorialCat
>         , ( [], []
>           , Map.fromList
>             [ ( ""
>               , ( "introductory tutorial"
>                 , unwords
>                   [ "This topic walks through the process of"
>                   , "defining a language via logical constraints"
>                   , "and analyzing the result."
>                   , "It is recommended that you have read"
>                   , "the %<t:LANGUAGE> topic first."
>                   , "Examples are shown in the Unicode syntax,"
>                   , "so if your environment is not configured"
>                   , "for easy input of these symbols"
>                   , "then you will want to be familiar"
>                   , "with their ASCII synonyms."
>                   , "See also the %<t:VISUALIZATION> topic,"
>                   , "for information on the prerequisite"
>                   , "commands for visual analysis."
>                   , "Notably: the GraphViz tools should be installed"
>                   , "(for %<c:dot>),"
>                   , "and you should have some sort of %<c:display>"
>                   , "program that can take a PNG image"
>                   , "on the standard input and display it,"
>                   , "such as that which comes with ImageMagick."
>                   , "Finally, you may wish to open a separate"
>                   , "interpreter session in order to follow"
>                   , "along with this guide."
>                   , "Examples will be shown as interpreter sessions."
>                   , "The default prompt will be shown"
>                   , "on lines that should be typed,"
>                   , "and any output will be shown"
>                   , "on unprefixed lines."
>                   , "For example, you might have gotten here"
>                   , "by running the following command:"
>                   , "%<p:>"
>                   , "%<e:%>% :help TUTORIAL>"
>                   , "%<p:> %<H:Constraints% and% System% Test>"
>                   , "As a reminder from the %<t:LANGUAGE> topic,"
>                   , "everything is written in Polish notation,"
>                   , "where each operator applies to the expression"
>                   , "or sequence of expressions"
>                   , "that follows it."
>                   , "Instead of something like"
>                   , "%<e:exp% :=% \172(x% \8743% y% \8743% z)>,"
>                   , "in the Pleb language we would write"
>                   , "%<e:=exp% \172\8896{x,y,z}>."
>                   , "This avoids the ambiguity of precedence"
>                   , "that arises with infix operators"
>                   , "and often simplifies expressions."
>                   , "%<p:>"
>                   , "To begin, start by defining an alphabet"
>                   , "and two simple constraints."
>                   , "%<p:>"
>                   , "%<e:%>% =a% /a% =b% /b> %<-:>"
>                   , "%<e:%>% =substr% \10216a% b\10217> %<-:>"
>                   , "%<e:%>% =subseq% \10216a,b\10217>"
>                   , "%<p:>"
>                   , "If everything was typed correctly,"
>                   , "then there will have been no output."
>                   , "You can verify that the variables"
>                   , "have been saved using the %<c::bindings>"
>                   , "command:"
>                   , "%<e:%>% :bindings> %<-:>"
>                   , "%<e:#% Symbol% aliases:> %<-:>"
>                   , "%<e:a% <-% {a}> %<-:>"
>                   , "%<e:b% <-% {b}> %<-:>"
>                   , "%<e:universe% <-% {a,% b}> %<-:>"
>                   , "%<e:#% Expression% aliases:> %<-:>"
>                   , "%<e:{subseq,% substr}>"
>                   , "%<p:>"
>                   , "Symbol sets are listed alongside"
>                   , "their expansions,"
>                   , "while expressions are merely listed."
>                   , "Meanings of individual variables can also be"
>                   , "display with %<c::show>,"
>                   , "including expressions,"
>                   , "although it should be noted that expressions"
>                   , "are shown in an internal format"
>                   , "that is likely to change between releases."
>                   , "%<p:>"
>                   , "%<e:%>% :show% universe> %<-:>"
>                   , "%<e:universe% <-% {a,% b}> %<-:>"
>                   , "%<e:%>% :show% subseq> %<-:>"
>                   , "%<e:subseq% <-% [...% the% long% internal"
>                         ++ "% representation% ...]>"
>                   , "%<p:>"
>                   , "Usually, the %<c::bindings> listing is enough."
>                   , "In any case, there should now be two"
>                   , "defined expressions,"
>                   , "%<v:substr> and %<v:subseq>."
>                   , "The first is a constraint"
>                   , "requiring that %<b:ab> occurs as a substring,"
>                   , "and the second requires that %<b:a>...%<b:b>"
>                   , "occurs as a subsequence."
>                   , "When the alphabet contains"
>                   , "only these two symbols,"
>                   , "these two constraints define the same language:"
>                   , "%<p:>"
>                   , "%<e:%>% :equal% substr% subseq> %<-:>"
>                   , "%<e:True>"
>                   , "%<p:>"
>                   , "However, they are not logically equivalent"
>                   , "constructions.  Over a larger alphabet,"
>                   , "they will not produce the same language."
>                   , "The %<c::cequal> command tests"
>                   , "for logical equivalence as opposed to"
>                   , "language equality:"
>                   , "%<p:>"
>                   , "%<e:%>% :cequal% substr% subseq> %<-:>"
>                   , "%<e:False>"
>                   , "%<p:>"
>                   , "If the substring occurs,"
>                   , "then so too does the subsequence."
>                   , "But the reverse does not necessarily hold"
>                   , "in general."
>                   , "%<p:>"
>                   , "%<e:%>% :cimplies% substr% subseq> %<-:>"
>                   , "%<e:True> %<-:>"
>                   , "%<e:%>% :cimplies% subseq% substr> %<-:>"
>                   , "%<e:False>"
>                   , "%<p:>"
>                   , "Notice, %<c::cimplies> %<v:x> %<v:y>"
>                   , "asks if %<v:x> implies %<v:y>"
>                   , "in every possible %<v:universe>."
>                   , "Adding a third symbol to the alphabet"
>                   , "breaks the equality of the languages."
>                   , "%<p:>"
>                   , "%<e:%>% =c% /c> %<-:>"
>                   , "%<e:%>% :equal% substr% subseq> %<-:>"
>                   , "%<e:False>"
>                   , "%<p:>"
>                   , "One simple way to see that these do not"
>                   , "define the same language is to display them"
>                   , "as finite-state automata."
>                   , "The differences should be visually apparent."
>                   , "%<p:>"
>                   , "%<e:%>% :display% substr> %<-:>"
>                   , "%<e:%>% :display% subseq>"
>                   , "%<p:>"
>                   , "If the %<c:dot> and %<c:display>"
>                   , "programs were properly installed"
>                   , "and were able to be located,"
>                   , "then two graphs should have appeared."
>                   , "Otherwise, you may want to install them,"
>                   , "check your path settings,"
>                   , "and possibly edit your %<t:CONFIG> file."
>                   , "Once you can see the graphs,"
>                   , "note the target of %<b:c>"
>                   , "from the central state."
>                   , "For the substring, the %<b:c> returns to"
>                   , "the start state,"
>                   , "while for the subsequence"
>                   , "it loops on that central state."
>                   , "This transition is what distinguishes"
>                   , "the two constraints."
>                   , "Notice that you did not need to redefine"
>                   , "%<v:substr> and %<v:subseq>"
>                   , "in order to account for the larger alphabet."
>                   , "The semantics of the constraints"
>                   , "are preserved through %<v:universe> changes."
>                   , "%<p:> %<H:Building% a% Linguistic% Pattern>"
>                   , "This section details how to construct"
>                   , "and analyze a complete pattern."
>                   , "First, clear the workspace so that"
>                   , "earlier bindings do not pollute the space:"
>                   , "%<p:>"
>                   , "%<e:%>% :reset> %<-:>"
>                   , "%<e:%>% :bindings> %<-:>"
>                   , "%<e:#% Symbol% aliases:> %<-:>"
>                   , "%<e:#% Expression% aliases:> %<-:>"
>                   , "%<e:{}>"
>                   , "%<p:>"
>                   , "With the environment empty,"
>                   , "some symbols can be defined for phonemes."
>                   , "The language to be constructed"
>                   , "will exhibit a few rules:"
>                   , "%<p:>"
>                   , "* Regressive nasal spreading %<-:>"
>                   , "* Regressive vowel backness harmony, and %<-:>"
>                   , "* Word-final devoicing"
>                   , "%<p:>"
>                   , "To properly see these rules in action,"
>                   , "the alphabet should contain"
>                   , "vowels, nasals, and both voiced and voiceless"
>                   , "oral stops."
>                   , "The following should suffice."
>                   , "%<p:>"
>                   , "%<e:%>% =a% /a% =e% /e% =i% /i% =o% /o% =u% /u>"
>                         ++ " %<-:>"
>                   , "%<e:%>% =\227% /\227% =\7869% /\7869"
>                         ++ "% =\297% /\297% =\245% /\245"
>                         ++ "% =\361% /\361> %<-:>"
>                   , "%<e:%>% =p% /p% =t% /t% =k% /k> %<-:>"
>                   , "%<e:%>% =b% /b% =d% /d% =g% /g> %<-:>"
>                   , "%<e:%>% =m% /m% =n% /n>"
>                   , "%<p:>"
>                   , "For the sake of convenience,"
>                   , "other symbol sets can be defined"
>                   , "to represent phonological features."
>                   , "%<p:>"
>                   , "%<e:%>% =back+{o,\245,u,\361}> %<-:>"
>                   , "%<e:%>% =back-{a,\227,e,\7869,i,\297}> %<-:>"
>                   , "%<e:%>% =low+{a,\227}> %<-:>"
>                   , "%<e:%>% =low-{e,\7869,i,\297,o,\245,u,\361}>"
>                   , "%<-:>"
>                   , "%<e:%>% =obs+{p,b,t,d,k,g}> %<-:>"
>                   , "%<e:%>% =obs-{back+,back-,m,n}> %<-:>"
>                   , "%<e:%>% =cons+{obs+,m,n}> %<-:>"
>                   , "%<e:%>% =cons-{back+,back-}> %<-:>"
>                   , "%<e:%>% =voi+{b,d,g,m,n,cons-}> %<-:>"
>                   , "%<e:%>% =voi-{p,t,k}> %<-:>"
>                   , "%<e:%>% =nas+{\227,\7869,\297,\245,\361,m,n}>"
>                   , "%<-:>"
>                   , "%<e:%>% =nas-{a,e,i,o,u,p,b,t,d,k,g}>"
>                   , "%<p:>"
>                   , "The nasal spreading rule"
>                   , "will nasalize spans of vowels"
>                   , "that precede a nasal stop."
>                   , "These will be the only instances"
>                   , "of nasalized vowels."
>                   , "On the surface, this means that"
>                   , "nasal vowels cannot immediately precede"
>                   , "non-nasals,"
>                   , "nor can they end a word,"
>                   , "and non-nasal vowels cannot"
>                   , "immediately precede nasals."
>                   , "%<p:>"
>                   , "%<e:%>% =nspread% \172\8897{"
>                         ++ "\10216[nas+,cons-]% [nas-]\10217,"
>                         ++ "\8905\10216[nas+,cons-]\10217,"
>                         ++ "\10216[nas-,cons-]% [nas+]\10217"
>                         ++ "}>"
>                   , "%<p:>"
>                   , "The harmony rule will force the backness of"
>                   , "non-low vowels to match"
>                   , "the first one encountered"
>                   , "from right-to-left (as it is regressive)."
>                   , "On the surface, this simply means"
>                   , "that non-low back vowels"
>                   , "and non-low non-back vowels"
>                   , "do not occur in the same word."
>                   , "%<p:>"
>                   , "%<e:%>% =harmony% \172\8896{"
>                         ++ "\10216[back+,low-]\10217,"
>                         ++ "\10216[back-,low-]\10217}>"
>                   , "%<p:>"
>                   , "Finally,"
>                   , "the word-final devoicing rule will transform"
>                   , "a final voiced obstruent into a voiceless one."
>                   , "This means that, on the surface,"
>                   , "no word ends with a voiced obstruent."
>                   , "This can be expressed as follows:"
>                   , "%<p:>"
>                   , "%<e:%>% =wfd \172\8905\10216[voi+,obs+]\10217>"
>                   , "%<p:>"
>                   , "The language as a whole will be"
>                   , "the set of all words which satisfy"
>                   , "all of these constraints."
>                   , "Placing the expression on a line to itself"
>                   , "will assign this to the special variable"
>                   , "%<v:it>."
>                   , "%<p:>"
>                   , "%<e:%>% \8896{nspread,harmony,wfd}>"
>                   , "%<p:>"
>                   , "At this point, you could %<c::display> %<v:it>"
>                   , "to see the resulting language"
>                   , "as an automaton,"
>                   , "but with twelve states it is a bit large"
>                   , "for that to provide much useful information."
>                   , "Instead, you might verify that words"
>                   , "are in or out of the language"
>                   , "using %<c::subset>:"
>                   , "%<p:>"
>                   , "%<e:%>% :subset% "
>                         ++ "\8906\8905\10216k% \297% n% t% a% p\10217"
>                         ++ "% it> %<-:>"
>                   , "%<e:True> %<-:>"
>                   , "%<e:%>% :subset% "
>                         ++ "\8906\8905\10216k% e% t% u\10217"
>                         ++ "% it> %<-:>"
>                   , "%<e:False>"
>                   , "%<p:>"
>                   , "The first word is accepted,"
>                   , "as it adheres to all of the constraints."
>                   , "The second is rejected,"
>                   , "as it has disharmony in its vowels."
>                   , "If you can determine the surface constraints"
>                   , "that arise from rules,"
>                   , "then you can construct any (regular) language"
>                   , "in this way."
>                   , "Notice that some clearly absurd words"
>                   , "are accepted:"
>                   , "%<p:>"
>                   , "%<e:%>% :subset% "
>                         ++ "\8906\8905\10216e% k% t% k% i\10217"
>                         ++ "% it> %<-:>"
>                   , "%<e:True>"
>                   , "%<p:>"
>                   , "Consider what kinds of constraints"
>                   , "you might need to add"
>                   , "in order to reasonably restrict"
>                   , "the syllable structure,"
>                   , "or to enforce some sort of OCP."
>                   , "%<p:> %<H:Analysis>"
>                   , "Using the classification commands,"
>                   , "one can gain insight regarding the structure"
>                   , "of a language defined in this way."
>                   , "A strictly local constraint"
>                   , "forbids certain local substrings"
>                   , "from appearing."
>                   , "For instance, the nasal spreading"
>                   , "rule places restrictions"
>                   , "on what symbols may appear"
>                   , "in the vicinity of nasals."
>                   , "%<p:>"
>                   , "%<e:%>% :isSL% nspread> %<-:>"
>                   , "%<e:True,% k=2>"
>                   , "%<p:>"
>                   , "The %<v:k> in this output is the size"
>                   , "of the longest forbidden substrings."
>                   , "The word-final devoicing constraint"
>                   , "is also strictly local with %<v:k>=2,"
>                   , "as the word boundary counts toward the length."
>                   , "%<p:>"
>                   , "%<e:%>% :isSL% wfd> %<-:>"
>                   , "%<e:True,% k=2>"
>                   , "%<p:>"
>                   , "However, the harmony constraint is not"
>                   , "strictly local."
>                   , "And as its long-distance effects are not"
>                   , "neutralized by the intersection,"
>                   , "the language as a whole is also"
>                   , "not strictly local."
>                   , "%<p:>"
>                   , "%<e:%>% :isSL% harmony> %<-:>"
>                   , "%<e:False> %<-:>"
>                   , "%<e:%>% :isSL% it> %<-:>"
>                   , "%<e:False>"
>                   , "%<p:>"
>                   , "This means that membership in the language"
>                   , "cannot be entirely determined"
>                   , "by looking at the individual substrings"
>                   , "that appear."
>                   , "Some early substring might affect"
>                   , "whether a later one is valid."
>                   , "That is what we saw with %<b:ketu>."
>                   , "The early %<b:e> cannot coexist"
>                   , "with the later %<b:u>."
>                   , "%<p:>"
>                   , "Strictly piecewise constraints deal"
>                   , "exclusively in this kind"
>                   , "of long-distance pattern."
>                   , "Where strictly local constraints restrict"
>                   , "local substrings,"
>                   , "strictly piecewise constraints restrict"
>                   , "long-distance subsequences."
>                   , "This harmony pattern is strictly piecewise,"
>                   , "but none of the other components are,"
>                   , "nor is the language as a whole."
>                   , "%<p:>"
>                   , "%<e:%>% :isSP% harmony> %<-:>"
>                   , "%<e:True,% k=2> %<-:>"
>                   , "%<e:%>% :isSP% nspread> %<-:>"
>                   , "%<e:False> %<-:>"
>                   , "%<e:%>% :isSP% wfd> %<-:>"
>                   , "%<e:False> %<-:>"
>                   , "%<e:%>% :isSP% it> %<-:>"
>                   , "%<e:False>"
>                   , "%<p:>"
>                   , "Another way of discussing"
>                   , "long-distance constraints"
>                   , "is the notion that they may apply"
>                   , "only after projection to a tier"
>                   , "of salient symbols."
>                   , "Every constraint here is the application"
>                   , "of a strictly local constraint"
>                   , "to some tier-projection,"
>                   , "called tier-based strictly local."
>                   , "%<p:>"
>                   , "%<e:%>% :isTSL% nspread> %<-:>"
>                   , "%<e:True,% T={a,% b,% d,% e,% g,% i,% k,% m,"
>                         ++ "% n,% o,% p,% t,% u,"
>                         ++ "% \227,% \7869,% \297,% \245,% \361"
>                         ++ "},% k=2> %<-:>"
>                   , "%<e:%>% :isTSL% harmony> %<-:>"
>                   , "%<e:True,% T={e,% i,% o,% u,"
>                         ++ "% \7869,% \297,% \245,% \361"
>                         ++ "},% k=2> %<-:>"
>                   , "%<e:%>% :isTSL% wfd> %<-:>"
>                   , "%<e:True,% T={a,% b,% d,% e,% g,% i,% k,% m,"
>                         ++ "% n,% o,% p,% t,% u,"
>                         ++ "% \227,% \7869,% \297,% \245,% \361"
>                         ++ "},% k=2>"
>                   , "%<p:>"
>                   , "Unlike strictly local and strictly piecewise,"
>                   , "however, the tier-based strictly local class"
>                   , "is not closed under intersection."
>                   , "So the language as a whole is not"
>                   , "tier-based strictly local."
>                   , "(It is, by definition, multiple-tier-based"
>                   , "strictly local, although there is currently"
>                   , "no known algorithm to determine whether"
>                   , "a given language lies in that class.)"
>                   , "%<p:>"
>                   , "%<e:%>% :isTSL% it> %<-:>"
>                   , "%<e:False>"
>                   , "%<p:>"
>                   , "Read up on some of the other %<t:CLASSIFICATION>"
>                   , "commands and determine whether the constraints"
>                   , "or the language as a whole"
>                   , "appear in any other classes."
>                   , "%<p:> %<H:Saving>"
>                   , "There is currently no stable way"
>                   , "to save the system of constraints"
>                   , "in a way that preserves their semantics."
>                   , "However, the %<c::savestate>"
>                   , "and %<c::write> commands will save files"
>                   , "that can be restored with"
>                   , "%<c::loadstate> or %<c::readBin>, respectively,"
>                   , "that represent constraint systems."
>                   , "These files are not guaranteed to work"
>                   , "across updates to the language toolkit."
>                   , "Working from a Pleb file"
>                   , "and reloading it with"
>                   , "%<c::reset> and %<c::read>"
>                   , "is also an option."
>                   , "However, if you do not need the ability"
>                   , "to maintain the constraint semantics"
>                   , "through changes to the %<v:universe>,"
>                   , "then %<c::writeATT> offers a stable"
>                   , "format that is interoperable with"
>                   , "OpenFST and several other tools."
>                   , "You can save the file and symbol definitions"
>                   , "as follows."
>                   , "%<p:>"
>                   , "%<e:%>% :writeATT% tutorial.att% tutorial.syms"
>                         ++ "% _% it>"
>                   , "%<p:>"
>                   , "Later, you can reload this file"
>                   , "as an automaton"
>                   , "(rather than as a constraint system)"
>                   , "with %<c::readATT>."
>                   , "%<p:>"
>                   , "%<e:%>% :readATT% tutorial.att% tutorial.syms"
>                         ++ "% _>"
>                   , "%<p:>"
>                   , "The symbol table file (tutorial.syms)"
>                   , "is actually unnecessary for files"
>                   , "saved by %<c:plebby> itself,"
>                   , "but may be meaningful when dealing"
>                   , "with other tools."
>                   , "%<p:>"
>                   , "This concludes the tutorial."
>                   , "For more information,"
>                   , "see the %<c::help> pages"
>                   , "for the various other topics"
>                   , "and commands."
>                   , "Go forth and explore."
>                   , "Define some languages and analyze them."
>                   , "And have fun!"
>                   , "%<p:> %<h:SEE% ALSO>"
>                   , "%<t:CONFIG>, %<t:LANGUAGE>"
>                   ]))
>             ]))
>       ]
