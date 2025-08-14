> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module : LTK.Porters
> Copyright : (c) 2018-2020,2022-2023,2025 Dakotah Lambert
> License   : MIT
> 
> This module provides methods to convert automata to and from
> various formats.
> -}

> module LTK.Porters
>        ( -- *Conversions
>          -- |In the following definitions,
>          -- @(Type t)@ is shorthand for @(String -> t)@.
>          from
>        , fromE
>        , to
>        -- *Formats
>        -- |We use types to create a bit of magic
>        -- in order to read and write automata in
>        -- various formats.
>        , Type
>        , Dot(Dot)
>        , EggBox(EggBox)
>        , SyntacticOrder(SyntacticOrder)
>        , SyntacticSemilattice(SyntacticSemilattice)
>        , Jeff(Jeff)
>        , Pleb(Pleb)
>        , ATT(ATT)
>        , ATTO(ATTO)
>        , Corpus(Corpus)
>        -- *Miscellaneous
>        , formatSet
>        , transliterate
>        , transliterateString
>        , untransliterate
>        , untransliterateString
>        , Importable(..)
>        , Exportable(..)
>        ) where

> import LTK.FSA          (FSA, renameStates, renameSymbolsBy
>                         , syntacticMonoid
>                         , syntacticSemilattice
>                         )
> import LTK.Porters.ATT  ( exportATT
>                         , invertATT
>                         , readATT
>                         )
> import LTK.Porters.Corpus (readCorpus)
> import LTK.Porters.Dot  (exportDot, formatSet)
> import LTK.Porters.EggBox (exportEggBox)
> import LTK.Porters.SyntacticOrder (exportSyntacticOrder)
> import LTK.Porters.SyntacticSemilattice (exportSyntacticSemilattice)
> import LTK.Porters.Jeff ( exportJeff
>                         , readJeff
>                         , transliterate
>                         , transliterateString
>                         , untransliterate
>                         , untransliterateString
>                         )
> import LTK.Porters.Pleb (readPleb)

> -- |A type that can be written from an 'FSA'.
> class Exportable t
>     where fromFSA  ::  (Ord n, Ord e, Show n, Show e) =>
>                        (t -> t) -> FSA n e -> String

> -- |A type that can be read and turned into an 'FSA'.
> class Importable t
>     where toFSA :: (t -> t) -> String -> Either String (FSA Integer String)

> -- |Create an 'FSA' from a @String@ treated as the given 'Type'.
> from :: (Importable i) => Type i -> String -> FSA Integer String
> from ty = either error id . fromE ty

> -- |Try to create an 'FSA' from a @String@ treated as the given 'Type'.
> fromE :: (Importable i) =>
>          Type i -> String -> Either String (FSA Integer String)
> fromE = toFSA

> -- |Create a @String@ from an 'FSA', formatted appropriately for
> -- the given 'Type'.
> to :: (Ord n, Ord e, Show n, Show e, Exportable x) =>
>       Type x -> FSA n e -> String
> to = fromFSA

> -- |An importable or exportable format.
> type Type t = t -> t

=== Instances for Jeff's format

> -- |Jeff's format.
> newtype Jeff = Jeff Jeff

> instance Exportable Jeff
>     where fromFSA _ = exportJeff

> instance Importable Jeff
>     where toFSA _ = fmap renameStates . readJeff

=== instances for Dot format

> -- |The GraphViz Dot format.
> newtype Dot = Dot Dot

> instance Exportable Dot
>     where fromFSA _ = exportDot

=== instances for EggBox (in Dot format)

> -- |The egg-box in GraphViz Dot format.
> newtype EggBox = EggBox EggBox -- ^@since 1.1

> instance Exportable EggBox
>     where fromFSA _ = exportEggBox . syntacticMonoid

=== instances for SyntacticOrder (in Dot format)

> -- |A Hasse diagram of the syntactic order.
> --
> -- @since 1.1
> newtype SyntacticOrder = SyntacticOrder SyntacticOrder
> instance Exportable SyntacticOrder
>     where fromFSA _ = exportSyntacticOrder . syntacticMonoid

=== instances for SyntacticSemilattice (in Dot format)

> -- |A Hasse diagram of the syntactic semilattice.
> newtype SyntacticSemilattice
>     = SyntacticSemilattice SyntacticSemilattice
> instance Exportable SyntacticSemilattice
>     where fromFSA _ = exportSyntacticSemilattice . syntacticSemilattice


=== instances for Pleb format

> -- |The format defined by the (P)iecewise / (L)ocal (E)xpression (B)uilder.
> newtype Pleb = Pleb Pleb

> instance Importable Pleb
>     where toFSA _ = readPleb

=== instances for ATT format

> -- |The AT&T finite-state transducer format, input projection
> --
> -- @since 0.3
> newtype ATT = ATT ATT

> instance Importable ATT
>     where toFSA _ = Right . readATT

> instance Exportable ATT
>     where fromFSA _ = exportATT

> -- |The AT&T finite-state transducer format, output projection
> --
> -- @since 0.3
> newtype ATTO = ATTO ATTO

> instance Importable ATTO
>     where toFSA _ = Right . readATT . invertATT

> instance Exportable ATTO
>     where fromFSA _ = invertATT . exportATT

> -- |A corpus of strings
> --
> -- @since 0.3
> newtype Corpus = Corpus Corpus

> instance Importable Corpus
>     where toFSA _ = Right .
>                     renameStates . renameSymbolsBy (:[]) .
>                     readCorpus . lines
