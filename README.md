# The Language Toolkit
![Current Version](https://img.shields.io/badge/version-1.0-informational.svg)
![Licence](https://img.shields.io/github/license/vvulpes0/Language-Toolkit-2)
![Issues](https://img.shields.io/github/issues/vvulpes0/Language-Toolkit-2)

A Haskell library for working with constraint-based descriptions of languages
and associated tools.

## Table of contents
* [Introduction](#introduction)
* [Features](#features)
* [Installation](#installation)
* [Using the library](#using-the-library)
* [Running plebby](#running-plebby)
* [Running classify](#running-classify)
* [Running factorize](#running-factorize)

## Introduction
At its core, this is yet another library
for working with finite-state automata.
What differentiates the Language Toolkit from others in this area
is its focus on the classes of languages that can be defined
by the set of factors that do or do not occur.
For example,
&ldquo;no _a_ comes anywhere before a _b_&rdquo;
is a constraint that describes such a language.
Importantly, one can define constraints using only the symbols relevant
to the constraint itself,
then combine them later in a way that preserves their semantics
even in a larger alphabet.

## Features
* Define languages with constraints
* Determine the complexity class of a language
* Extract constraints from languages
* Decide whether a language satisfies a constraint

## Installation
Ensure that you have the Glasgow Haskell Compiler (GHC) and cabal-install
installed on your system.
The easiest way is to install the
[Haskell Platform](https://www.haskell.org/platform/).
Official support extends only to GHC 8.0 (May 2016) and newer,
but older versions might work.
For relatively new versions of cabal-install,
you can install everything with at most two commands:

    cabal v2-install all
    cabal v2-install --lib LTK # if you want the library installed globally

If you are using a 1.x version of cabal-install,
you will have to use this single command instead:

    cabal install

In the end, you will have installed the LTK library (if desired)
as well as its five bundled executables:
* classify
* dotify
* factorize
* make-non-strict-constraints
* plebby

There are some \*nix manual pages in the `man` directory.
You can copy those to an appropriate location for your system
if you want.

## Using the library
To get access to most provided functions import LTK as a whole:

    import LTK

There are several sub-modules that can be imported individually,
which are fully documented in the
[Haddock documentation](https://vvulpes0.github.io/Language-Toolkit-2/docs/haddock/).


## Running plebby
The main program,
plebby is an interactive interpreter for the
Pleb file format,
which is described in detail in the included \*nix manual page `pleb.5`.
No special initialization is needed, just run the program:

    plebby

The brings you to a REPL.
In addition to the Pleb syntax, you will want to know two special commands:

* :help, to get a list of available commands, and
* :quit, to exit the interpreter

A full description of the interpreter itself is
in the included manual page `plebby.1`.


## Running classify
Several decision algorithms are supported by `plebby`.
However, one may want to use these in a batch processing system.
One can provide a single automaton to `classify` via the standard input,
selecting its interpretation format by means of the
`-a` (AT&T, input), `-A` (AT&T, output), `-j` (Jeff), or `-p` (PLEB)
flags.  The classes in which you are interested should be passed as
command line arguments:
a `CLASS` is valid iff `plebby` has a corresponding `:isCLASS` command.
The default is for the utility to exit successfully iff any one of the
provided classes contains the given pattern;
the `-u` option changes the interpretation so that only if all of the
classes contain the pattern will the exit status be success.

    printf '*⋊⋉⟨/a /b⟩\n' | classify -p SP SL LT
    [ ("SP",False)
    , ("SL",True)
    , ("LT",True)
    ]

The output is able to be read directly into Haskell as a list of
(String,Bool) pairs, in case that is useful.

For complete documentation, see the `classify.1` manual page.


## Running factorize
The other primary program, along with `plebby` and `classify`.
This takes AT&T-format automata as input,
using the output-projection of the transducer as the pattern.
First, `cd` to a directory you want to factor things in.
You may then factor some kinds of languages
automatically by simply running, for example, the following:

    factorize /path/to/111_final.att

You can pass multiple files to do several factorizations in parallel,
and the results all go into a `Results` directory.

Some constraints cannot currently be extracted automatically.
The `make-non-strict-constraints` program generates ones that
cover the dataset this project was originally developed around.
If you want to use these, you can use the following initialization:

    mkdir Compiled # if you haven't already done so
    cd Compiled
    make-non-strict-constraints
    printf 'Compiled/%s\n' * | grep -v constraints > constraints
    cd ..

and then subsequently run factorize itself as before:

    factorize [files]
