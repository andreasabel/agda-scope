module Concrete where

open import Data.List.Base using (List; []; _∷_)
open import Data.String using (String)
open import Data.String.Unsafe public using (_≟_)

Name = String
QName = List String

data Exp : Set where
  ident : QName → Exp
  univ  : Exp

mutual
  data Decl : Set where
    axiom : (ty : Exp) → Decl
    mDecl : (x : Name) (ds : Decls) → Decl

  Decls = List Decl
