{-# OPTIONS --allow-unsolved-metas #-}


module TypeChecker where

open import Library; open Dec using (yes; no)
import WellScoped as A
open import WellScoped using (Cxt; ε; _▷_; Γ; Δ; _≤_; ρ; Ty; A; B; wkTy; equalEntry; equalTy)
open Cxt; open _≤_; open Ty
open import WellTyped

data TypeError : Set where
  functionExpected : _
  typeMismatch     : _

printTypeError : TypeError → String
printTypeError functionExpected = "function expected"
printTypeError typeMismatch     = "type mismatch"

-- Monad for the type checker

M : Set → Set
M = TypeError ⊎_

open RawMonad {M = M} (monad _ _)
open RawApplicative {F = M} (applicative _ _) using () renaming (_⊛_ to _<*>_)
open TraversableM {M = M} (monad _ _)

pattern fail err = inj₁ err

coerce : (t : Tm Γ A) (B : Ty Γ) → M (Tm Γ B)
coerce {A = A} t B with equalTy A B
... | yes refl = return t
... | no _     = fail typeMismatch

inferRef : (x : A.Entry Γ) → ∃ (Ref Γ)
inferRef {Γ = Γ ▷ A}  A.here     = wk1Ty A , here
inferRef {Γ = Γ ▷ A} (A.there x) = bimap wk1Ty there $ inferRef x

mutual
  inferExp : A.Exp Γ → M (∃ (Tm Γ))
  inferExp (A.def x)   = return $ map₂ def $ inferRef x
  inferExp (A.app f e) = do
    arr A B , t ← inferExp f
      where
      _ → fail functionExpected
    u ← checkExp A e
    return (B , app t u)

  checkExp : (A : Ty Γ) → A.Exp Γ → M (Tm Γ A)
  checkExp A e = do
    B , t ← inferExp e
    coerce t A

checkClauses : (A : Ty Γ) → A.Clauses Γ → M (Clauses Γ A)
checkClauses A = mapM (checkExp A)

checkCxtDeco
  : (ρ : Γ ≤ Δ)
  → A.CxtDeco (A.Clauses Γ) Δ
  → M (CxtDeco Γ (Clauses Γ) Δ ρ)

checkCxtDeco ρ (_▷_ {A = A} p cl) = do
  p'  ← checkCxtDeco (drop1 ρ) p
  cl' ← checkClauses (wkTy (drop1 ρ) A) cl
  return (p' ▷ cl')

checkCxtDeco ρ ε = return (ε ρ)

checkProgram : A.Program Γ → M (Program Γ)
checkProgram = checkCxtDeco wid

-- -}
