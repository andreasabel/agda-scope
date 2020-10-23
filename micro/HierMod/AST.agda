-- Agda bindings for the Haskell abstract syntax data types.
-- Generated by BNFC.

module HierMod.AST where

open import Agda.Builtin.Char using () renaming (Char to Char)
open import Agda.Builtin.Float public using () renaming (Float to Double)
open import Agda.Builtin.Int   public using () renaming (Int to Integer)
open import Agda.Builtin.List using () renaming (List to #List)
open import Agda.Builtin.String using () renaming
  ( String to #String
  ; primStringFromList to #stringFromList
  )

{-# FOREIGN GHC import Prelude (Bool, Char, Double, Integer, String, (.)) #-}
{-# FOREIGN GHC import qualified Data.Text #-}
{-# FOREIGN GHC import qualified HierMod.Abs #-}
{-# FOREIGN GHC import HierMod.Print (printTree) #-}

data Name : Set where
  name : #String → Name

{-# COMPILE GHC Name = data HierMod.Abs.Name (HierMod.Abs.Name) #-}

mutual

  data Program : Set where
    prg : (x : Name) (d : Decls) → Program

  {-# COMPILE GHC Program = data HierMod.Abs.Program (HierMod.Abs.Prg) #-}

  data Decl : Set where
    modl : (x : Name) (d : Decls) → Decl
    ref  : (q : QName) → Decl

  {-# COMPILE GHC Decl = data HierMod.Abs.Decl
    ( HierMod.Abs.Modl
    | HierMod.Abs.Ref
    ) #-}

  data Decls : Set where
    dNil  : Decls
    dSnoc : (d₁ : Decls) (d₂ : Decl) → Decls

  {-# COMPILE GHC Decls = data HierMod.Abs.Decls
    ( HierMod.Abs.DNil
    | HierMod.Abs.DSnoc
    ) #-}

  data QName : Set where
    qName : (x : Name) → QName
    qual  : (x : Name) (q : QName) → QName

  {-# COMPILE GHC QName = data HierMod.Abs.QName
    ( HierMod.Abs.QName
    | HierMod.Abs.Qual
    ) #-}

dSg : Decl → Decls
dSg = λ d → dSnoc dNil d

-- Binding the pretty printers.

postulate
  printProgram : Program → #String
  printDecl    : Decl → #String
  printDecls   : Decls → #String
  printQName   : QName → #String
  printName    : Name → #String

{-# COMPILE GHC printProgram = \ p -> Data.Text.pack (printTree (p :: HierMod.Abs.Program)) #-}
{-# COMPILE GHC printDecl = \ d -> Data.Text.pack (printTree (d :: HierMod.Abs.Decl)) #-}
{-# COMPILE GHC printDecls = \ d -> Data.Text.pack (printTree (d :: HierMod.Abs.Decls)) #-}
{-# COMPILE GHC printQName = \ q -> Data.Text.pack (printTree (q :: HierMod.Abs.QName)) #-}
{-# COMPILE GHC printName = \ x -> Data.Text.pack (printTree (x :: HierMod.Abs.Name)) #-}
