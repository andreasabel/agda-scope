open import Library

module Concrete where

open import Library public using (_≟_)

Name = String
QName = List String

data Exp : Set where
  ident : QName → Exp
  univ  : Exp

mutual
  data Decl : Set where
    axiom : (x : Name) (ty : Exp) → Decl
    mDecl : (x : Name) (ds : Decls) → Decl

  Decls = List Decl

unqual : Name → Exp
unqual x = ident (x ∷ [])

example : Decl
example = mDecl "Top"           -- module Top
    ( axiom "A" univ            --   A : Set
    ∷ axiom "a" (unqual "A")    --   a : A
    ∷ mDecl "M"                 --   module M
      ( axiom "b" (unqual "A")  --     b : A
      ∷ axiom "c" (unqual "A")  --     c : A
      ∷ [])
    ∷ axiom "d" (ident ("M" ∷ "c" ∷ []))    --   d : M.c
    ∷ [])
