module AST.DataSetInternal where
open import AST.GHCTypes
mutual
  data SSet ( a : Set ) : Set where
    BinC : Size → a → (SSet  a) → (SSet  a) → SSet a
    TipC : SSet a
  
  Size :  Set
  Size  = Int

{-# FOREIGN GHC SSet = SSet ( BinC | TipC ) #-}

 
