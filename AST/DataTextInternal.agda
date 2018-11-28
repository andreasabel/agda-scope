module AST.DataTextInternal where
open import AST.DataTextArray
open import AST.GHCTypes
mutual
  data Text : Set where
    TextC : Array → Int → Int → Text 

{-# FOREIGN GHC Text = Text ( TextC ) #-}

