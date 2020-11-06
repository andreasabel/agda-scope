# Agda Scoping [![Build Status](https://travis-ci.org/andreasabel/agda-scope.svg?branch=master)](https://travis-ci.org/andreasabel/agda-scope)
Notes and prototypes concerning Agda's scope checker.  Content:

* [`notes/agdaShadowing.md`](https://github.com/andreasabel/agda-scope/blob/master/notes/agdaShadowing.md): See below
  ([PDF](https://andreasabel.github.io/agda-scope/notes/agdaShadowing.pdf))

* [`notes/modcal.tex`](https://github.com/andreasabel/agda-scope/blob/master/notes/modcal.tex): WIP: formalization of well-scoped hierarchical modules
   ([PDF](https://andreasabel.github.io/agda-scope/notes/modcal.pdf))

* [`core/`](https://github.com/andreasabel/agda-scope/blob/master/core/):
  Scope Checker for small Agda fragment in Agda (WIP)

* [`pure/`](https://github.com/andreasabel/agda-scope/blob/master/pure/):
  Minimal calculus of hierarchical modules implemented in Haskell

* [`micro/`](https://github.com/andreasabel/agda-scope/blob/master/micro/):
  Minimal calculus of hierarchical modules implemented in Agda

* [`src/`](https://github.com/andreasabel/agda-scope/blob/master/src/):
  Haskell to Agda data type translation (using Template Haskell)

## RFC Agda shadowing rules

This [note](https://andreasabel.github.io/agda-scope/notes/agdaShadowing.pdf)
proposes a changed semantics of the Agda module system allowing
shadowing of definitions in parent modules
(see [Agda issue #3801](https://github.com/agda/agda/issues/3801)).

Feel free to discuss my proposal on the
[issue tracker](https://github.com/andreasabel/agda-scope/issues).
