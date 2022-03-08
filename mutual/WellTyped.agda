module WellTyped where

open import Library
open import WellScoped using (Cxt; Γ; Δ; _≤_; ρ; Ty; A; B; wkTy)
open Cxt; open _≤_; open Ty

wε : Γ ≤ ε
wε {Γ = ε} = wid
wε {Γ = Γ ▷ A} = wε ▷ˡ _

wk1 : (Γ ▷ A) ≤ Γ
wk1 = wid ▷ˡ _

wk1Ty : Ty Γ → Ty (Γ ▷ A)
wk1Ty = wkTy wk1

variable
  Φ : Cxt

_∙_ : Γ ≤ Δ → Δ ≤ Φ → Γ ≤ Φ
wid      ∙ σ = σ
(ρ ▷ˡ A) ∙ σ = (ρ ∙ σ) ▷ˡ A

drop1 : Γ ≤ (Δ ▷ A) → Γ ≤ Δ
drop1 = _∙ wk1

data Ref : (Γ : Cxt) → Ty Γ → Set where
  here  :                 Ref (Γ ▷ A) (wk1Ty A)
  there : (x : Ref Γ A) → Ref (Γ ▷ B) (wk1Ty A)

data Tm (Γ : Cxt) (B : Ty Γ) : Set where
  def : (x : Ref Γ B) → Tm Γ B
  app : (t : Tm Γ (arr A B)) (u : Tm Γ A) → Tm Γ B

Clauses : (Γ : Cxt) → Ty Γ → Set
Clauses Γ A = List (Tm Γ A)

-- data CxtDeco (Γ : Cxt) : (Δ : Cxt) (ρ : Γ ≤ Δ → Ty Δ → Set) → Set where
--   ε : CxtDeco Γ ε D
--   _▷_ : CxtDeco Γ Δ D → D → CxtDeco Γ (Δ ▷ A) D

-- Γ ≤ Δ → Tm Δ A → A ≤ B → Tm Γ B
-- (ρ : Γ ⇒ Δ)
-- Tm(ρ) : Tm Δ → Tm Γ

-- T A = A → Int
-- _∘_ : (A → B) → T B → T A

data CxtDeco (Γ : Cxt) (D : Ty Γ → Set) : ∀ Δ → Γ ≤ Δ → Set where

  ε   : (ρ : Γ ≤ ε)
      → CxtDeco Γ D ε ρ

  _▷_ : CxtDeco Γ D Δ (drop1 ρ)
      → D (wkTy (drop1 ρ) A)
      → CxtDeco Γ D (Δ ▷ A) ρ

Program : Cxt → Set
Program Γ = CxtDeco Γ (Clauses Γ) Γ wid

-- -}
-- -}
-- -}
-- -}
