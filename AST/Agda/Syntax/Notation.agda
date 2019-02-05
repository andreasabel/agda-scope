module AST.Agda.Syntax.Notation where
open import Data.List
open import AST.Agda.Syntax.Common
open import AST.GHC.Types
mutual
  data GenPart : Set where
    BindHoleC : Int → GenPart 
    NormalHoleC : (NamedArg  Int) → GenPart 
    WildHoleC : Int → GenPart 
    IdPartC : RawName → GenPart 
  
  Notation :  Set
  Notation  = (List (GenPart))

{-# FOREIGN GHC import Agda.Syntax.Notation #-}

{-# COMPILE GHC GenPart = data GenPart ( BindHole | NormalHole | WildHole | IdPart ) #-}

 
