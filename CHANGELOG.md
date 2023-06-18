# Changelog

## Version 1.1 — 2023-06-18
### Added
* preliminary French translation of manual pages
* basic Emacs mode for syntax highlighting
* classification procedures
  + isAcom (aperiodic and commutative)
  + isLAcom (locally isAcom)
  + isFO2BF (two-variable FO with betweenness of factors)
  + isVariety (Plebby has one command each for *, +, and tier)
  + isMTF, isMTDef, isMTRDef, isMTGD (simple multitier classes)
* Porters
  + egg-box diagrams
  + graphs of syntactic orders
* Pleb syntax
  + empty variadics
  + reversal (`⇄`)
  + upward closures (`↑`, or `loopify` in the library)
  + shuffle products (`⧢` or `autShuffle` in the library)
  + symbol neutralization (`|syms|`, or `neutralize` in the library)
  + nonempty iteration (`+e` equivalent to `@(e,*e)`)
* Plebby commands
  + `:cequal` and `:cimplies` to account for the semantics
  + `:eggbox` (display the egg-box)
  + `:synord` (display syntactic order)
* Plebby configuration file
### Changed
* bugfix: omega function works in properly regular semigroups
* performance enhancement: faster FO2(S) test
* performance enhancement: faster (co)finite test
* performance enhancement: faster SP test

## Version 1.0.1 — 2022-03-28
### Changed
* fixed a mistest in `classify`, as well as a severe performance issue

## Version 1.0 (initial hackage release) — 2022-03-15
### Added
* `classify` command
* LTK.Algebra module and new decision procedures `LTK.Decide.*`
  + B
  + CB
  + Definite, (T)(R)Def restrictions on suffixes or prefixes (on tiers)
  + Finite
  + FO2, FO2S, FO2B: definable in two-variable FO with <, (<,+1), (<,bet)
  + GD: generalized definite, prefixes AND suffixes
  + GLPT: generalization of LPT
  + GLT: generalization of LT
  + LPT: locally J-trivial, contains combinations of piecewise-local factors
  + TLPT: tier-based LPT
  + Trivial: accepts ALL strings, or NO strings
  + associated `:isCLASS` plebby commands
* LTK.DecideM: classify monoids, to avoid recomputation
* left- and right-quotients in `LTK.FSA` and in PLEB
* union and intersection of symbol sets wherever they may appear in PLEB
* downward closure in PLEB
* `:Jmin` plebby command for displaying a graph of J-classes
### Changed
* **`dotify` now uses AT&T format instead of Jeff format**
* **`factorize` now uses AT&T format instead of Jeff format**
* improved AT&T import and export
### Removed
* stress-specific symbols in `LTK.Factors`

## Version 0.3 — 2020-09-16
### Added
* AT&T import and export `LTK.Porters.ATT`
* prefix-tree import from corpus `LTK.Porters.Corpus`
* string-extension learners `LTK.Learn.*`
* more `plebby` commands
  + AT&T import and export `:readATT`, `:readATTO`, `:writeATT`
  + learners `:learnSL`, `:learnSP`, `:learnTSL`
### Changed
* extraction is now a submodule: `LTK.Extract.SL` not `LTK.ExtractSL`, etc

## Version 0.2 — 2019-09-01
### Added
* more decision algorithms `LTK.Decide.*`
  + LT: locally testable, defined by sets of k-substrings
  + LTT: locally threshold-testable, FO[+1]
  + PT: piecewise-testable, defined by sets of k-subsequences
  + SF: star-free, aperiodic, star-height zero
  + SL: the decider formerly in `LTK.ExtractSL`
  + SP: the decider formerly in `LTK.ExtractSP`
  + TLT: tier-based LT
  + TLTT: tier-based LTT
  + TSL: tier-based strictly local
### Changed
* factor extraction is now `LTK.Extract.*`

## Version 0.1 — 2019-08-23
* moved to a Cabal-based installation format
* removed several exploratory files
* add computations over tiers

## Version 0.01a — 2018-12-20
* initial full public release
