module AST.DataTextArray where
open import AST.GHCPrim
mutual
  data Array : Set where
    ArrayC : ByteArray# → Array 

{-# FOREIGN GHC Array = Array ( ArrayC ) #-}

 
