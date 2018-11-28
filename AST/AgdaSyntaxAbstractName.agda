module AST.AgdaSyntaxAbstractName where
open import Data.List
open import AST.AgdaSyntaxCommon
open import AST.AgdaSyntaxConcreteName
open import AST.AgdaSyntaxFixity
open import AST.AgdaSyntaxPosition
mutual
  data ModuleName : Set where
    MNameC : (List (Name)) → ModuleName 
  
  data Name : Set where
    NameC : NameId → Name → Range → FixityP → Name 
  
  data QName : Set where
    QNameC : ModuleName → Name → QName 

{-# COMPILE GHC ModuleName = data ModuleName ( MNameC ) #-}

{-# COMPILE GHC Name = data Name ( NameC ) #-}

{-# COMPILE GHC QName = data QName ( QNameC ) #-}

 
