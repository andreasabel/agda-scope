-- Andreas, 2019-05-04 example to test the scope checker

module Top where
{ module A where {}
  module A where {} -- illegal shadowing
  module _ = A      -- A ambiguous
}
