module AST.Agda.Syntax.Concrete.Name where
open import Data.List
open import AST.Agda.Syntax.Common
open import AST.Agda.Syntax.Position
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

{-# FOREIGN GHC import Agda.Syntax.Concrete.Name #-}

{-# COMPILE GHC Name = data Name ( Name | NoName ) #-}

{-# COMPILE GHC NamePart = data NamePart ( Hole | Id ) #-}

{-# COMPILE GHC QName = data QName ( Qual | QName ) #-}

 
