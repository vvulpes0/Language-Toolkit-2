# Contents
* [Introduction](#introduction)
* [Formatting](#formatting)
  * [Breaking Lines](#breaking-lines)
  * [Indentation](#indentation)
  * [If conditionals](#if-conditionals)
  * [Case conditionals](#case-conditionals)
  * [Lists, tuples, and records](#lists-tuples-and-records)
  * [Special alignment](#special-alignment)
  * [Exports](#exports)
  * [Imports](#imports)
* [Documentation](#documentation)
* [Naming conventions](#naming-conventions)

# Introduction
This codebase has been evolving for years,
and as is the norm for academic projects
this evolution was guided more by results
than by elegance.
Some of the code may not exemplify the standards
proposed by this document.
That said, we believe they should be used as guiding principles
for the structure of newly introduced code.

# Formatting
## Line Length
Please try to avoid lines longer than 72 characters.
Consider 80 a hard limit.

## Breaking lines
Try to break after a composition (`.`) or application (`$`) operator
if possible.
If that won't work, but there is another binary operator that would,
feel free to break after that.
Otherwise just do what makes sense.
Either of the following can be considered acceptable:

```haskell
> f g xs = map g
>          xs

> f g xs = map
>          g
>          xs
```

But try to avoid combinations like this:

```haskell
> f g xs = map
>          g xs
```

## Indentation
Don't use tabs.
There is no indentation, only alignment.
The exception to this rule is that
a `where` clause, a guard, or a dropped equals sign
should be indented by four spaces,
while all other things should be aligned in an appropriate way.
Examples:

```haskell
> derivative :: (Num a) => [a] -> [a]
> derivative = drop 1 .
>              zipWith (*) exponents
>     where exponents = iterate (+ 1) 1

> filter :: (a -> Bool) -> [a] -> [a]
> filter _ []  =  []
> filter p (x:xs)
>     | p x        =  p x : filter p xs
>     | otherwise  =  filter p xs
```

## If conditionals
Generally, prefer guards.
But if you have an if statement,
it should be aligned at the keywords.
That said, if it is fairly short
then it can remain on one line.
Examples:

```haskell
> foo = if condition
>       then trueCase
>       else falseCase

> bar = if x then a else b
```

## Case conditionals
Align at the keywords, and when reasonable align your arrows:

```haskell
> foobar x = case x
>            of Just j   ->  foo j
>               Nothing  ->  bar
```

Note that this example would be preferentially written as:

```haskell
> foobar = maybe bar foo
```

## Lists, tuples, and records
Use the comma-first style when broken across lines:

```haskell
> directions = [ East
>              , North
>              , West
>              , South
>              ]

> aPair = ( firstElement
>         , secondElement
>         )

> data FSA n e
>     = FSA
>       { alphabet         ::  Set e
>       , transitions      ::  Set (Transition n e)
>       , initials         ::  Set (State n)
>       , finals           ::  Set (State n)
>       , isDeterministic  ::  Bool
>       } deriving (Show, Read)
```

## Special alignment
When aligning `::` or `=`, or the `->` of case conditions,
surround the symbols by two spaces rather than one:

```haskell
map f (x:xs)  =  f x : map xs
map _ _       =  []

double = map (* 2) -- only one space here
```

## Exports
Short export lists can go on a single line:

```haskell
> module Main (main) where
```

Long export lists should be formatted like tuples:

```haskell
> module LTK.Porters.ATT
>        ( embedSymbolsATT
>        , extractSymbolsATT
>        , invertATT
>        -- *Importing
>        , readATT
>        -- *Exporting
>        , exportATT
>        ) where
```

Export lists should be ordered in a useful way,
perhaps with section headings as shown above.

## Imports
Group imports into three categories separated by blank lines:
* [Standard libraries][1]
* Third-party libraries
  (separate groups of related libraries with blank lines as well)
* Libraries that are a part of the project

[1]: https://downloads.haskell.org/~ghc/latest/docs/html/libraries/index.html

Within each category, place qualified imports last.
For non-qualified imports in the first two categories,
use fully explicit import lists
ordered alphabetically, with types first,
then normal functions,
then symbolic operators.
For example:

```haskell
> module Main (main) where

> import Control.DeepSeq (NFData, ($!!))
> import System.IO ( IOMode(WriteMode)
>                  , hFlush
>                  , hPutStr
>                  , withFile
>                  )
> import qualified Data.Set as Set

> import Control.Parallel.Strategies
>        ( parListChunk
>        , rdeepseq
>        , using
>        )

> import LTK.FSA
```

# Documentation
As shown above, where appropriate,
export lists should have section headings.

Use the [Haddock][haddock] documentation format.
Every exported entity should be documented:

[haddock]: https://haskell-haddock.readthedocs.io/en/latest/markup.html

```haskell
> -- |True iff the automaton recognizes a Star-Free stringset.
> isSF :: (Ord n, Ord e) => FSA n e -> Bool
```

Long documentation can be split across lines:

```haskell
> -- |Determine the tier alphabet for which
> -- the given FSA is a preprojection.
> -- This could simply be the entire alphabet of the FSA.
> -- Precondition: the given FSA must be in normal form.
> tier :: (Ord n, Ord e) => FSA n e -> Set e
```

We use (Bird-style) Literate Haskell,
so liberal insertion of comments on algorithms
or other useful information is not only accepted,
but expected.  For example, an excerpt from `FSA.lhs`:

```fundamental
For the difference A - B, the finals states are those that are
accepting in A and non-accepting in B.

Note that the relative complement requires functionality.  Consider
the case of (A - B) where B is nondeterministic in such a way that
there exists a string w for which a computation leads to both an
accepting state qa and a non-accepting state qn.  Suppose that w leads
to an accepting state in A, qf.  Then the cartesian construction will
contain both (qf, qa) and (qf, qn).

When selecting states to be accepting, (qf, qn) will be included since
qn is non-accepting in B, and (qf, qa) will be excluded since qa is
accepting in B.  This is not what we want, as it means that w is still
accepted.  Thus we cannot use the cartesian construction to gain an
advantage over the naive implementation of (A & not B).
```

This type of long, free-form comment is encouraged
in cases like this where intuitions and reality may diverge.
Note the lack of line-initial `> ` marks.

# Naming conventions
Use `camelCase` for functions and values,
and `UpperCamelCase` for classes, types, and constructors.

Make use of the hierarchical module structure.

Write functions in a way that assumes use of partial application:

```haskell
> minimizeOver r fsa = ...
> minimize = minimizeOver nerode
```

From this perspective `isSubsetOf` in `Data.Set` is &ldquo;wrong&rdquo;.
The `isSubsetOf` in `LTK.Containers` uses the partial-application
order, while that in `Data.Set` assumes an infix usage.
