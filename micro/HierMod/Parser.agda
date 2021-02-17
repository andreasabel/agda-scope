-- Agda bindings for the Haskell parsers.
-- Generated by BNFC.

module HierMod.Parser where

open import Agda.Builtin.Bool using () renaming (Bool to #Bool)
open import Agda.Builtin.Char using () renaming (Char to Char)
open import Agda.Builtin.List using () renaming (List to #List)
open import Agda.Builtin.String using () renaming
  ( String to #String
  ; primStringFromList to #stringFromList
  )

open import HierMod.AST using
  ( Program
  ; Decl
  ; Decls
  ; ImportDirective
  ; QName
  )

{-# FOREIGN GHC import Prelude (Bool, Char, Double, Integer, String, (.)) #-}
{-# FOREIGN GHC import qualified Data.Text #-}
{-# FOREIGN GHC import qualified HierMod.ErrM #-}
{-# FOREIGN GHC import HierMod.Par #-}
{-# FOREIGN GHC import qualified HierMod.Layout #-}

-- Error monad of BNFC

data Err A : Set where
  ok  : A → Err A
  bad : #List Char → Err A

{-# COMPILE GHC Err = data HierMod.ErrM.Err
  ( HierMod.ErrM.Ok
  | HierMod.ErrM.Bad
  ) #-}

-- Happy parsers

postulate
  parseProgram : #Bool → #String → Err Program
  parseDecl : #Bool → #String → Err Decl
  parseDecls : #Bool → #String → Err Decls
  parseImportDirective : #Bool → #String → Err ImportDirective
  parseQName : #Bool → #String → Err QName

{-# COMPILE GHC parseProgram = \ tl -> pProgram . HierMod.Layout.resolveLayout tl . myLexer #-}
{-# COMPILE GHC parseDecl = \ tl -> pDecl . HierMod.Layout.resolveLayout tl . myLexer #-}
{-# COMPILE GHC parseDecls = \ tl -> pDecls . HierMod.Layout.resolveLayout tl . myLexer #-}
{-# COMPILE GHC parseImportDirective = \ tl -> pImportDirective . HierMod.Layout.resolveLayout tl . myLexer #-}
{-# COMPILE GHC parseQName = \ tl -> pQName . HierMod.Layout.resolveLayout tl . myLexer #-}
