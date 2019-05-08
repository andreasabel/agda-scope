module _ where

module M where
  module A where

module N1 where
  open M public

module N2 where
  open M public

open N1
open N2

module T = A  -- unambiguous name, but ambiguous resolution (via N1 or N2)
