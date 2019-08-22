module AST.Agda.Utils.FileName where
open import AST.GHC.Types
mutual
  data AbsolutePath : Set where
    AbsolutePathC : Text → AbsolutePath 

{-# FOREIGN GHC import Agda.Utils.FileName #-}

{-# COMPILE GHC AbsolutePath = data AbsolutePath ( AbsolutePath ) #-}

 
