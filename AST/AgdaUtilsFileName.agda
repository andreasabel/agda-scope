module AST.AgdaUtilsFileName where
open import AST.DataTextInternal
mutual
  data AbsolutePath : Set where
    AbsolutePathC : Text → AbsolutePath 

{-# FOREIGN GHC AbsolutePath = AbsolutePath ( AbsolutePathC ) #-}

 
