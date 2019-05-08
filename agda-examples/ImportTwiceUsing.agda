module _ where

module M where
  module N where

open M using (module N) renaming (module N to O)  -- illegal in Agda 2.6.0
