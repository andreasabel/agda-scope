module AST.AgdaSyntaxFixity where
open import AST.AgdaSyntaxNotation
open import AST.AgdaSyntaxPosition
open import AST.GHCIntegerType
mutual
  data Associativity : Set where
    NonAssocC : Associativity 
    LeftAssocC : Associativity 
    RightAssocC : Associativity 
  
  data Fixity : Set where
    FixityC : Range → PrecedenceLevel → Associativity → Fixity 
  
  data FixityP : Set where
    FixityPC : Fixity → Notation → Range → FixityP 
  
  data PrecedenceLevel : Set where
    UnrelatedC : PrecedenceLevel 
    RelatedC : Integer → PrecedenceLevel 

{-# COMPILE GHC Associativity = data Associativity ( NonAssocC | LeftAssocC | RightAssocC ) #-}

{-# COMPILE GHC Fixity = data Fixity ( FixityC ) #-}

{-# COMPILE GHC FixityP = data FixityP ( FixityPC ) #-}

{-# COMPILE GHC PrecedenceLevel = data PrecedenceLevel ( UnrelatedC | RelatedC ) #-}

 
