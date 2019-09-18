-- Translation from parsed syntax to restricted syntax.

module ParsedToConcrete where

open import Library
import Concrete as C
import ModuleCalculus.AST as P

-- Translation monad

data P2CError : Set where
  unsupported : P2CError

M : Set → Set
M = P2CError ⊎_

fail : ∀{A : Set} → M A
fail = inj₁ unsupported

open RawMonad {M = M} (monad _ _)

-- Type class for translation from parsed syntax to concrete syntax

record P→C (P C : Set) : Set where
  field p→c : P → M C

open P→C {{...}} public

instance
  p→c-List : ∀{P C} {{p→c : P→C P C}} → P→C (List P) (List C)
  p→c-List .p→c = mapM (monad _ _) p→c

  p→c-List⁺ : ∀{P C} {{p→c : P→C P C}} → P→C (List⁺ P) (List⁺ C)
  p→c-List⁺ .p→c (x ∷ xs) = zipWith _∷_ (p→c x) (mapM (monad _ _) p→c xs)

  p→c-Name : P→C P.Ident C.Name
  p→c-Name .p→c = return ∘ P.printIdent

  p→c-QName : P→C P.QName C.QName
  p→c-QName .p→c (P.qName x)  = _∷ [] <$> p→c x
  p→c-QName .p→c (P.qual x q) = zipWith _∷⁺_ (p→c x) (p→c q)

  p→c-Exp : P→C P.Exp C.Exp
  p→c-Exp .p→c P.eUniv   = return C.univ
  p→c-Exp .p→c (P.eId q) = C.ident <$> p→c q
  p→c-Exp .p→c (P.eApp e₁ e₂) = fail
  p→c-Exp .p→c (P.ePi bs e)   = fail
  p→c-Exp .p→c (P.eLam x e)   = fail

  {-# TERMINATING #-}
  p→c-Decl : P→C P.Decl C.Decl
  p→c-Decl .p→c (P.decl _m x e)        = zipWith C.axiom (p→c x) (p→c e)
  p→c-Decl .p→c (P.module' _m x [] ds) = zipWith C.mDecl (p→c x) (p→c ds)
  -- Module parameters not supported yet:
  p→c-Decl .p→c (P.module' m x (b ∷ bs) ds) = fail
  p→c-Decl .p→c (P.spec m x q is ds)        = fail
  p→c-Decl .p→c (P.open' x m)               = fail
  p→c-Decl .p→c (P.def x e)                 = fail

  p→c-Program : P→C P.Program C.Decl
  p→c-Program .p→c (P.prg x ds) = zipWith C.mDecl (p→c x) (p→c ds)

-- Embedding concrete syntax into parsed syntax

record C→P (C P : Set) : Set where
  field c→p : C → P

open C→P {{...}} public

instance
  c→p-List : ∀{C P} {{c→p : C→P C P}} → C→P (List C) (List P)
  c→p-List .c→p = map c→p

  c→p-Name : C→P C.Name P.Ident
  c→p-Name .c→p = P.ident

  {-# TERMINATING #-}
  c→p-QName : C→P C.QName P.QName
  c→p-QName .c→p (x ∷ [])       = P.qName (c→p x)
  c→p-QName .c→p (x ∷ (y ∷ ys)) = P.qual  (c→p x) (c→p (y ∷ ys))

  c→p-Exp : C→P C.Exp P.Exp
  c→p-Exp .c→p C.univ      = P.eUniv
  c→p-Exp .c→p (C.ident q) = P.eId (c→p q)

  {-# TERMINATING #-}
  c→p-Decl : C→P C.Decl P.Decl
  c→p-Decl .c→p (C.axiom x e)  = P.decl    P.public' (c→p x) (c→p e)
  c→p-Decl .c→p (C.mDecl x ds) = P.module' P.public' (c→p x) [] (c→p ds)
