module _ where

module M where
  module N where
  module O where

open M using (module O) renaming (module N to O)  -- illegal in Agda-2.6.0

module T2 = O
