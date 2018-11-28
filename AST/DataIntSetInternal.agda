module AST.DataIntSetInternal where
open import AST.GHCTypes
mutual
  BitMap :  Set
  BitMap  = Word
  
  data IntSet : Set where
    BinC : Prefix → Mask → IntSet → IntSet → IntSet 
    TipC : Prefix → BitMap → IntSet 
    NilC : IntSet 
  
  Mask :  Set
  Mask  = Int
  
  Prefix :  Set
  Prefix  = Int

{-# FOREIGN GHC IntSet = IntSet ( BinC | TipC | NilC ) #-}

 
