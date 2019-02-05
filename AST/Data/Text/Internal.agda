module AST.Data.Text.Internal where
open import AST.GHC.Types
mutual
  data Text : Set where
    TextC : Array → Int → Int → Text 

{-# FOREIGN GHC import Data.Text.Internal #-}

{-# COMPILE GHC Text = data Text ( Text ) #-}

