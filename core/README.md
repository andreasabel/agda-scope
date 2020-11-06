# A core calculus for Agda's module system

Build and run tests with
```
  make
```
Requires Agda, Alex, BNFC, GHC, and Happy.

* [`ModuleCalculus.cf`](https://github.com/andreasabel/agda-scope/blob/master/core/ModuleCalculus.cf): LBNF grammar
* [`test/`](https://github.com/andreasabel/agda-scope/blob/master/test/): example files in the calculus

Definition of fragment and status of implementation:
- [x] modules
- [ ] module parameters
- [ ] `open` statements
- [ ] import directives `using` and `renaming`
- [ ] `private` and `public`
- [x] type signatures
- [ ] interesting expressions
