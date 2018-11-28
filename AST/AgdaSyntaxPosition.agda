module AST.AgdaSyntaxPosition where
open import Data.Empty
open import Data.Maybe
open import AST.AgdaUtilsFileName
open import AST.DataSequenceInternal
open import AST.GHCInt
mutual
  data IntervalP ( a : Set ) : Set where
    IntervalC : (PositionP  a) → (PositionP  a) → IntervalP a
  
  IntervalWithoutFile :  Set
  IntervalWithoutFile  = (IntervalP  ⊥)
  
  data PositionP ( a : Set ) : Set where
    PnC : a → Int32 → Int32 → Int32 → PositionP a
  
  Range :  Set
  Range  = (RangeP  SrcFile)
  
  data RangeP ( a : Set ) : Set where
    NoRangeC : RangeP a
    RangeC : a → (Seq  IntervalWithoutFile) → RangeP a
  
  SrcFile :  Set
  SrcFile  = (Maybe  AbsolutePath)

{-# COMPILE GHC IntervalP = data IntervalP ( IntervalC ) #-}

{-# COMPILE GHC PositionP = data PositionP ( PnC ) #-}

{-# COMPILE GHC RangeP = data RangeP ( NoRangeC | RangeC ) #-}

 
