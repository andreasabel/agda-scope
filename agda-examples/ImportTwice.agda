module _ where

module M where
  module N where

open M renaming (module N to O)

module T1 = O
-- module T2 = N  -- not in scope
