-- Printing well-scoped syntax back to concrete syntax.

open import Library

module AbstractToConcrete where

import Concrete as C
import WellScoped as A

mutual
  a→c-Name : ∀{k xs s} → A.Name k xs s → C.QName
  a→c-Name (A.symb x)    = x ∷ []
  a→c-Name (A.modl x)    = x ∷ []
  a→c-Name (A.child x n) = x ∷⁺ a→c-LName n

  a→c-LName : ∀{k xs s} → A.LName k xs s → C.QName
  a→c-LName (A.lname j x) = a→c-Name x

a→c-SName : ∀{k xs s} → A.SName k xs s → C.QName
a→c-SName (A.sname i x) = a→c-LName x

a→c-Exp : ∀{s} → A.Exp s → C.Exp
a→c-Exp (A.ident x) = C.ident (a→c-SName x)
a→c-Exp A.univ      = C.univ

mutual

  a→c-Decl : ∀{sc s} → A.Decl sc s → C.Decl
  a→c-Decl (A.sDecl x ty) = C.axiom x (a→c-Exp ty)
  a→c-Decl (A.mDecl x ds) = C.mDecl x (a→c-Decls ds)

  a→c-Decls : ∀{sc rs rs'} → A.Decls sc rs rs' → C.Decls
  a→c-Decls A.[]       = []
  a→c-Decls (d A.∷ ds) = a→c-Decl d ∷ a→c-Decls ds
