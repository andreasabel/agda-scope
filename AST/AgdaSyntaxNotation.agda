module AST.AgdaSyntaxNotation where
open import Data.List
open import AST.AgdaSyntaxCommon
open import AST.GHCTypes
mutual
  data GenPart : Set where
    BindHoleC : Int → GenPart 
    NormalHoleC : (NamedArg  Int) → GenPart 
    WildHoleC : Int → GenPart 
    IdPartC : RawName → GenPart 
  
  Notation :  Set
  Notation  = (List (GenPart))

{-# FOREIGN GHC GenPart = GenPart ( BindHoleC | NormalHoleC | WildHoleC | IdPartC ) #-}

 
