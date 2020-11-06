# A microscopic calculus of hierarchical modules

Supports:
- [x] Non-parameterized module definitions `module x where ...`
- [x] References to modules via `open x.y.z using ()`

Build and run tests with
```
  make
```
Requires Agda, Alex, BNFC, GHC, and Happy.

* [`ModuleCalculus.cf`](https://github.com/andreasabel/agda-scope/blob/master/micro/ModuleCalculus.cf): LBNF grammar
* [`test/`](https://github.com/andreasabel/agda-scope/blob/master/test/): example files in the calculus
