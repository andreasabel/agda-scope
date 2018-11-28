module AST.AgdaUtilsFileName where
open import AST.DataTextInternal
mutual
  data AbsolutePath : Set where
    AbsolutePathC : Text → AbsolutePath 

{-# COMPILE GHC AbsolutePath = data AbsolutePath ( AbsolutePathC ) #-}

 
