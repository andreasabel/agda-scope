# Agda Scoping [![Build Status](https://travis-ci.org/andreasabel/agda-scope.svg?branch=master)](https://travis-ci.org/andreasabel/agda-scope)
Notes and prototypes concerning Agda's scope checker

* `notes/agdaShadowing.md`: See below

* `notes/modcal.tex`: WIP: formalization of well-scoped hierarchical modules

* `core/`: Scope Checker for small Agda fragment in Agda (WIP)
* `pure/`: Minimal calculus of hierarchical modules implemented in Haskell
* `micro/`: Minimal calculus of hierarchical modules implemented in Agda
* `src/`: Haskell to Agda data type translation (using Template Haskell)

## RFC Agda shadowing rules

This [note](https://andreasabel.github.io/agda-scope/notes/agdaShadowing.pdf)
proposes a changed semantics of the Agda module system allowing
shadowing of definitions in parent modules
(see [issue #3801](https://github.com/agda/agda/issues/3801)).

Feel free to discuss my proposal on the
[issue tracker](https://github.com/andreasabel/agda-scope/issues).
