module AST.Data.Text.Array where
open import AST.GHC.Types
mutual
  data Array : Set where
    ArrayC : ByteArray# → Array 

{-# FOREIGN GHC import Data.Text.Array #-}

{-# COMPILE GHC Array = data Array ( Array ) #-}

 
