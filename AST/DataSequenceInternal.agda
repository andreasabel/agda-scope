module AST.DataSequenceInternal where
open import AST.GHCTypes
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

{-# FOREIGN GHC Digit = Digit ( OneC | TwoC | ThreeC | FourC ) #-}

{-# FOREIGN GHC Elem = Elem ( ElemC ) #-}

{-# FOREIGN GHC FingerTree = FingerTree ( EmptyTC | SingleC | DeepC ) #-}

{-# FOREIGN GHC Node = Node ( Node2C | Node3C ) #-}

{-# FOREIGN GHC Seq = Seq ( SeqC ) #-}

 
