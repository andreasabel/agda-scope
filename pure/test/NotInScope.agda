-- Andreas, 2019-05-04 / 2019-08-21 example to test the scope checker

module NotInScope where
  module A where
  open B      -- B not in scope
