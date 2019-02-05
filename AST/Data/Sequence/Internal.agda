module AST.Data.Sequence.Internal where
open import AST.GHC.Types
mutual
  data Digit ( a : Set ) : Set where
    OneC : a → Digit a
    TwoC : a → a → Digit a
    ThreeC : a → a → a → Digit a
    FourC : a → a → a → a → Digit a
  
  data Elem ( a : Set ) : Set where
    ElemC : a → Elem a
  
  data FingerTree ( a : Set ) : Set where
    EmptyTC : FingerTree a
    SingleC : a → FingerTree a
    DeepC : Int → (Digit  a) → (FingerTree  (Node  a)) → (Digit  a) → FingerTree a
  
  data Node ( a : Set ) : Set where
    Node2C : Int → a → a → Node a
    Node3C : Int → a → a → a → Node a
  
  data Seq ( a : Set ) : Set where
    SeqC : (FingerTree  (Elem  a)) → Seq a

{-# FOREIGN GHC import Data.Sequence.Internal #-}

{-# COMPILE GHC Digit = data Digit ( One | Two | Three | Four ) #-}

{-# COMPILE GHC Elem = data Elem ( Elem ) #-}

{-# COMPILE GHC FingerTree = data FingerTree ( EmptyT | Single | Deep ) #-}

{-# COMPILE GHC Node = data Node ( Node2 | Node3 ) #-}

{-# COMPILE GHC Seq = data Seq ( Seq ) #-}

 
