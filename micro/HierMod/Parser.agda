-- Agda bindings for the Haskell parsers.
-- Generated by BNFC.

module HierMod.Parser where

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
  ; QName
  )

{-# FOREIGN GHC import qualified Data.Text #-}
{-# FOREIGN GHC import HierMod.Abs #-}
{-# FOREIGN GHC import HierMod.ErrM #-}
{-# FOREIGN GHC import HierMod.Par #-}

-- Error monad of BNFC

data Err A : Set where
  ok : A → Err A
  bad : #List Char → Err A

{-# COMPILE GHC Err = data Err
  ( Ok
  | Bad
  ) #-}

-- Happy parsers

postulate
  parseProgram : #String → Err Program
  parseDecl : #String → Err Decl
  parseDecls : #String → Err Decls
  parseQName : #String → Err QName

{-# COMPILE GHC parseProgram = pProgram . myLexer . Data.Text.unpack #-}
{-# COMPILE GHC parseDecl = pDecl . myLexer . Data.Text.unpack #-}
{-# COMPILE GHC parseDecls = pDecls . myLexer . Data.Text.unpack #-}
{-# COMPILE GHC parseQName = pQName . myLexer . Data.Text.unpack #-}