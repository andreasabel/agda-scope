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

{-# FOREIGN GHC IntervalP = IntervalP ( IntervalC ) #-}

{-# FOREIGN GHC PositionP = PositionP ( PnC ) #-}

{-# FOREIGN GHC RangeP = RangeP ( NoRangeC | RangeC ) #-}

 
