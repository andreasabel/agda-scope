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

{-# FOREIGN GHC Associativity = Associativity ( NonAssocC | LeftAssocC | RightAssocC ) #-}

{-# FOREIGN GHC Fixity = Fixity ( FixityC ) #-}

{-# FOREIGN GHC FixityP = FixityP ( FixityPC ) #-}

{-# FOREIGN GHC PrecedenceLevel = PrecedenceLevel ( UnrelatedC | RelatedC ) #-}

 
