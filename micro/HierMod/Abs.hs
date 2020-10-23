-- Haskell data types for the abstract syntax.
-- Generated by the BNF converter.

{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module HierMod.Abs where

import Prelude (Char, Double, Integer, String)
import qualified Prelude as C (Eq, Ord, Show, Read)
import qualified Data.String

import qualified Data.Text

newtype Name = Name Data.Text.Text
  deriving (C.Eq, C.Ord, C.Show, C.Read, Data.String.IsString)

data Program = Prg Name Decls
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Decl = Modl Name Decls | Ref QName
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Decls = DNil | DSnoc Decls Decl
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data QName = QName Name | Qual Name QName
  deriving (C.Eq, C.Ord, C.Show, C.Read)

dSg :: Decl -> Decls
dSg d = DSnoc DNil d

