module _ where

module M where
  module N where

open M using (module N)
open M using () renaming (module N to O)  -- legal in Agda

module T1 = N
module T2 = O
