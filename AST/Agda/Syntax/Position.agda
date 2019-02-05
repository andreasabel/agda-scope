module AST.Agda.Syntax.Position where
open import Data.Empty
open import AST.Agda.Utils.FileName
open import AST.Data.Sequence.Internal
open import AST.GHC.Types
open import AST.Data.Strict.Maybe as ADSM
mutual
  data Interval' ( a : Set ) : Set where
    IntervalC : (Position'  a) → (Position'  a) → Interval' a
  
  IntervalWithoutFile :  Set
  IntervalWithoutFile  = (Interval'  ⊥)
  
  data Position' ( a : Set ) : Set where
    PnC : a → Int32 → Int32 → Int32 → Position' a
  
  Range :  Set
  Range  = (Range'  SrcFile)
  
  data Range' ( a : Set ) : Set where
    NoRangeC : Range' a
    RangeC : a → (Seq  IntervalWithoutFile) → Range' a
  
  SrcFile :  Set
  SrcFile  = (ADSM.Maybe  AbsolutePath)

{-# FOREIGN GHC import Agda.Syntax.Position #-}

{-# COMPILE GHC Interval' = data Interval' ( Interval ) #-}

{-# COMPILE GHC Position' = data Position' ( Pn ) #-}

{-# COMPILE GHC Range' = data Range' ( NoRange | Range ) #-}

 
