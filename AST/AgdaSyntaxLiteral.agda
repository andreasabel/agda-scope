module AST.AgdaSyntaxLiteral where
open import Data.Char
open import Data.String
open import AST.AgdaSyntaxAbstractName
open import AST.AgdaSyntaxCommon
open import AST.AgdaSyntaxPosition
open import AST.AgdaUtilsFileName
open import AST.GHCIntegerType
open import AST.GHCTypes
open import AST.GHCWord
mutual
  data Literal : Set where
    LitNatC : Range → Integer → Literal 
    LitWord64C : Range → Word64 → Literal 
    LitFloatC : Range → Double → Literal 
    LitStringC : Range → String → Literal 
    LitCharC : Range → Char → Literal 
    LitQNameC : Range → QName → Literal 
    LitMetaC : Range → AbsolutePath → MetaId → Literal 

{-# COMPILE GHC Literal = data Literal ( LitNatC | LitWord64C | LitFloatC | LitStringC | LitCharC | LitQNameC | LitMetaC ) #-}

 
