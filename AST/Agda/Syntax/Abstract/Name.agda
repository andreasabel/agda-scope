module AST.Agda.Syntax.Abstract.Name where
open import Data.List
open import AST.Agda.Syntax.Common
import AST.Agda.Syntax.Concrete.Name as C
open import AST.Agda.Syntax.Fixity
open import AST.Agda.Syntax.Position
mutual
  data ModuleName : Set where
    MNameC : (List (Name)) → ModuleName 
  
  data Name : Set where
    NameC : NameId → C.Name → Range → Fixity' → Name 
  
  data QName : Set where
    QNameC : ModuleName → Name → QName 

{-# FOREIGN GHC import Agda.Syntax.Abstract.Name #-}

{-# COMPILE GHC ModuleName = data ModuleName ( MName ) #-}

{-# COMPILE GHC Name = data Name ( Name ) #-}

{-# COMPILE GHC QName = data QName ( QName ) #-}

 
