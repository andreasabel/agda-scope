module AST.Agda.Syntax.Fixity where
open import AST.Agda.Syntax.Notation
open import AST.Agda.Syntax.Position
open import AST.GHC.Types
mutual
  data Associativity : Set where
    NonAssocC : Associativity 
    LeftAssocC : Associativity 
    RightAssocC : Associativity 
  
  data Fixity : Set where
    FixityC : Range → PrecedenceLevel → Associativity → Fixity 
  
  data Fixity' : Set where
    Fixity'C : Fixity → Notation → Range → Fixity' 
  
  data PrecedenceLevel : Set where
    UnrelatedC : PrecedenceLevel 
    RelatedC : Integer → PrecedenceLevel 

{-# FOREIGN GHC import Agda.Syntax.Fixity #-}

{-# COMPILE GHC Associativity = data Associativity ( NonAssoc | LeftAssoc | RightAssoc ) #-}

{-# COMPILE GHC Fixity = data Fixity ( Fixity ) #-}

{-# COMPILE GHC Fixity' = data Fixity' ( Fixity' ) #-}

{-# COMPILE GHC PrecedenceLevel = data PrecedenceLevel ( Unrelated | Related ) #-}

 
