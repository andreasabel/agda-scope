module AST.AgdaSyntaxAbstractName where
open import Data.List
open import AST.AgdaSyntaxCommon
import AST.AgdaSyntaxConcreteName
open import AST.AgdaSyntaxFixity
open import AST.AgdaSyntaxPosition
mutual
  data ModuleName : Set where
    MNameC : (List (Name)) → ModuleName 
  
  data Name : Set where
    NameC : NameId → Name → Range → FixityP → Name 
  
  data QName : Set where
    QNameC : ModuleName → Name → QName 

{-# FOREIGN GHC ModuleName = ModuleName ( MNameC ) #-}

{-# FOREIGN GHC Name = Name ( NameC ) #-}

{-# FOREIGN GHC QName = QName ( QNameC ) #-}

 
