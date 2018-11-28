module AST.AgdaSyntaxConcreteName where
open import Data.List
open import AST.AgdaSyntaxCommon
open import AST.AgdaSyntaxPosition
mutual
  data Name : Set where
    NameC : Range → (List (NamePart)) → Name 
    NoNameC : Range → NameId → Name 
  
  data NamePart : Set where
    HoleC : NamePart 
    IdC : RawName → NamePart 
  
  data QName : Set where
    QualC : Name → QName → QName 
    QNameC : Name → QName 

{-# FOREIGN GHC Name = Name ( NameC | NoNameC ) #-}

{-# FOREIGN GHC NamePart = NamePart ( HoleC | IdC ) #-}

{-# FOREIGN GHC QName = QName ( QualC | QNameC ) #-}

 
