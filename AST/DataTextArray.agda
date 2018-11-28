module AST.DataTextArray where
open import AST.GHCPrim
mutual
  data Array : Set where
    ArrayC : ByteArray# → Array 

{-# COMPILE GHC Array = data Array ( ArrayC ) #-}

 
