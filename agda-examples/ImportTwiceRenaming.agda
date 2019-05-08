module Top where

module M where
  module N where

open M using () renaming (N to O; N to P)  -- illegal in Agda 2.6.0
