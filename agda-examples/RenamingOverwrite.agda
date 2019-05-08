module _ where

module M where
  module N where
    module N where

open M using () renaming (module N to M)  -- legal in Agda-2.6.0

module T0 = M.N.N
-- module T1 = M.N -- error: ambiguous
-- module T2 = M   -- error: ambiguous
