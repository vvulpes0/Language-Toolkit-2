> {-# OPTIONS_HADDOCK show-extensions #-}
> {-|
> Module : LTK.Porters
> Copyright : (c) 2018-2019 Dakotah Lambert
> License   : BSD-style, see LICENSE
> 
> This module provides methods to convert automata to and from
> various formats.
> -}

> module LTK.Porters ( -- *Conversions
>                      -- |In the following definitions,
>                      -- @(Type t)@ is shorthand for @(String -> t)@.
>                      from
>                    , fromE
>                    , to
>                    -- *Formats
>                    -- |We use types to create a bit of magic
>                    -- in order to read and write automata in
>                    -- various formats.
>                    , Dot(Dot)
>                    , Jeff(Jeff)
>                    , Pleb(Pleb)
>                    -- *Miscellaneous
>                    , formatSet
>                    , transliterate
>                    , transliterateString
>                    , untransliterate
>                    , untransliterateString
>                    , Importable
>                    , Exportable
>                    ) where

> import LTK.FSA          (FSA, renameStates)
> import LTK.Porters.Dot  (exportDot, formatSet)
> import LTK.Porters.Jeff ( readJeff
>                         , exportJeff
>                         , transliterate
>                         , transliterateString
>                         , untransliterate
>                         , untransliterateString)
> import LTK.Porters.Pleb ( readPleb )

> -- |A type that can be written from an 'FSA'.
> class Exportable t where
>     fromFSA  ::  (Ord n, Ord e, Show n, Show e) => FSA n e -> t
>     extract  ::  t -> String

> -- |A type that can be read and turned into an 'FSA'.
> class Importable t where
>     toFSA       ::  t -> Either String (FSA Integer String)

> -- |Create an 'FSA' from a @String@ treated as the given 'Type'.
> from :: (Importable i) => Type i -> String -> FSA Integer String
> from ty = either error id . fromE ty

> -- |Try to create an 'FSA' from a @String@ treated as the given 'Type'.
> fromE :: (Importable i) => Type i -> String -> Either String (FSA Integer String)
> fromE ty = toFSA . ty

> -- |Create a @String@ from an 'FSA', formatted appropriately for
> -- the given 'Type'.
> to :: (Ord n, Ord e, Show n, Show e, Exportable x) =>
>       Type x -> FSA n e -> String
> to ty = extract . flip asTypeOf (ty "") . fromFSA

> type Type t = String -> t

=== Instances for Jeff's format

> -- |Jeff's format.
> newtype Jeff = Jeff String

> instance Exportable Jeff where
>     fromFSA           =  Jeff . exportJeff
>     extract (Jeff s)  =  s

> instance Importable Jeff where
>     toFSA  =  fmap renameStates . readJeff . extract

=== instances for Dot format

> -- |The GraphViz Dot format.
> newtype Dot = Dot String

> instance Exportable Dot where
>     fromFSA          =  Dot . exportDot
>     extract (Dot s)  =  s

=== instances for Pleb format

> newtype Pleb = Pleb String

> instance Importable Pleb where
>     toFSA (Pleb s) = readPleb s