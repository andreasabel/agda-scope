{-# OPTIONS --allow-unsolved-metas #-}

open import Library; open Dec using (yes; no)
import Mutual.AST as C

module WellScoped where

interleaved mutual

  data Cxt : Set
  data Ty (Γ : Cxt) : Set

  variable
    Γ Δ : Cxt
    A B C : Ty Γ

  data Cxt where
    ε : Cxt
    _▷_ : (Γ : Cxt) (A : Ty Γ) → Cxt

  data Entry : Cxt → Set where
    here  : Entry (Γ ▷ A)
    there : (x : Entry Γ) → Entry (Γ ▷ A)

  variable
    x y : Entry Γ

  data Ty Γ where
    set : Ty Γ
    def : (x : Entry Γ) → Ty Γ
    arr : (A B : Ty Γ) → Ty Γ

data Exp (Γ : Cxt) : Set where
  def : (x : Entry Γ) → Exp Γ
  app : (f e : Exp Γ) → Exp Γ

data Decl (Γ : Cxt) : Set where
  sig : (x : C.Ident) (A : Ty Γ) → Decl Γ
  def : (x : Entry Γ) (e : Exp Γ) → Decl Γ

Clauses : Cxt → Set
Clauses Γ = List (Exp Γ)

data CxtDeco (D : Set) : Cxt → Set where
  ε   : CxtDeco D ε
  _▷_ : CxtDeco D Γ → D → CxtDeco D (Γ ▷ A)

Program : Cxt → Set
Program Γ = CxtDeco (Clauses Γ) Γ

private variable
  D E : Set

decoUpdate : Entry Γ → (D → D) → CxtDeco D Γ → CxtDeco D Γ
decoUpdate here      f (Δ ▷ d) = Δ ▷ f d
decoUpdate (there x) f (Δ ▷ e) = decoUpdate x f Δ ▷ e

decoMap : (D → E) → CxtDeco D Γ → CxtDeco E Γ
decoMap f ε       = ε
decoMap f (Δ ▷ d) = decoMap f Δ ▷ f d

-- Weakening

mutual
  data _≤_ : (Γ Δ : Cxt) → Set where
    wid  : Γ ≤ Γ
    _▷ˡ_ : (ρ : Γ ≤ Δ) (A : Ty Γ) → (Γ ▷ A) ≤ Δ
    -- _▷_  : (ρ : Γ ≤ Δ) (A : Ty Δ) → (Γ ▷ wkTy ρ A) ≤ (Δ ▷ A)

  variable
    ρ : Γ ≤ Δ

  wkEntry : (ρ : Γ ≤ Δ) → Entry Δ → Entry Γ
  wkEntry wid      x         = x
  wkEntry (ρ ▷ˡ _) x         = there (wkEntry ρ x)
  -- wkEntry (ρ ▷  _) here      = here
  -- wkEntry (ρ ▷  _) (there x) = there (wkEntry ρ x)

  wkTy : (ρ : Γ ≤ Δ) → Ty Δ → Ty Γ
  wkTy ρ set = set
  wkTy ρ (def x) = def (wkEntry ρ x)
  wkTy ρ (arr A B) = arr (wkTy ρ A) (wkTy ρ B)

wk1Exp : Exp Γ → Exp (Γ ▷ A)
wk1Exp (def x) = def (there x)
wk1Exp (app f e) = app (wk1Exp f) (wk1Exp e)

wk1Clauses : Clauses Γ → Clauses (Γ ▷ A)
wk1Clauses = map wk1Exp

wk1Program : Program Γ → Program (Γ ▷ A)
wk1Program P = decoMap wk1Clauses P ▷ []

-- -}
