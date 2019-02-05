module AST.Agda.Syntax.Literal where
open import Data.Char
open import AST.Agda.Syntax.Abstract.Name
open import AST.Agda.Syntax.Common
open import AST.Agda.Syntax.Position
open import AST.Agda.Utils.FileName
open import AST.GHC.Types
mutual
  data Literal : Set where
    LitNatC : Range → Integer → Literal 
    LitWord64C : Range → Word64 → Literal 
    LitFloatC : Range → Double → Literal 
    LitStringC : Range → String → Literal 
    LitCharC : Range → Char → Literal 
    LitQNameC : Range → QName → Literal 
    LitMetaC : Range → AbsolutePath → MetaId → Literal 

{-# FOREIGN GHC import Agda.Syntax.Literal #-}

{-# COMPILE GHC Literal = data Literal ( LitNat | LitWord64 | LitFloat | LitString | LitChar | LitQName | LitMeta ) #-}

 
