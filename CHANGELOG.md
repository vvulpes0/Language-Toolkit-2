# Changelog

## Version NEXT
### Added
* egg-box display (a Porter, and `:eggbox` in Plebby)
* French translation of manual pages
* basic Emacs mode for syntax highlighting
### Changed
* performance enhancements: faster FO2(S) test

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