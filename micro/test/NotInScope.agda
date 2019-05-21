-- Andreas, 2019-05-04 example to test the scope checker

module NotInScope where
  module A where
  open B using ()     -- B not in scope
