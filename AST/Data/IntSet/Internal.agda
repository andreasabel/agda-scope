module AST.Data.IntSet.Internal where
open import AST.GHC.Types
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

{-# FOREIGN GHC import Data.IntSet.Internal #-}

{-# COMPILE GHC IntSet = data IntSet ( Bin | Tip | Nil ) #-}

 
