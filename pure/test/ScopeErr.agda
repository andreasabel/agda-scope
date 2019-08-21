-- Andreas, 2019-05-04 / 2019-08-21 example to test the scope checker

module ScopeErr where
  module A where
  module A where    -- illegal shadowing
  open A            -- A ambiguous
