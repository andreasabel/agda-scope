-- Andreas, 2019-05-04 example to test the scope checker

module ScopeErr where
  module A where
  module A where    -- illegal shadowing
  open A using ()   -- A ambiguous
