
{-# OPTIONS --allow-unsolved-metas #-}

open import Library renaming (_≟_ to _==_)

module ScopeChecker where

import Mutual.AST as C
open import WellScoped as A

injIdent : Injective C.ident
injIdent refl = refl

_≟_ : (x y : C.Ident) → Dec (x ≡ y)
C.ident x ≟ C.ident y = Dec.cong injIdent $ x == y

-- Scope errors

data ScopeError : Set where
  notInScope : (x : C.Ident) → ScopeError

printScopeError : ScopeError → String
printScopeError (notInScope (C.ident x)) = "not in scope: " String.++ x

-- Scopes

Scope : Cxt → Set
Scope = CxtDeco C.Ident

-- Programs with name decoration

SProgram : Cxt → Set
SProgram Γ = Scope Γ × Program Γ

-- Monad for the scope checker

M : Set → Set
M = ScopeError ⊎_

open RawMonad {F = M} (monad _ _)
-- open RawApplicative {F = M} (applicative _ _) using () renaming (_⊛_ to _<*>_)

pattern fail err = inj₁ err

scopeLookup : Scope Γ → C.Ident → M (Entry Γ)
scopeLookup ε       x = fail (notInScope x)
scopeLookup (Δ ▷ y) x =
  case x ≟ y of λ where
    (Dec.yes _) → return here
    (Dec.no  _) → there <$> scopeLookup Δ x


checkTy : Scope Γ → C.Ty → M (Ty Γ)
checkTy Δ C.tSet         = return set
checkTy Δ (C.tId x)      = def <$> scopeLookup Δ x
checkTy Δ (C.tArr s _ t) = arr <$> checkTy Δ s <*> checkTy Δ t

checkExp : Scope Γ → C.Exp → M (Exp Γ)
checkExp Δ (C.eId x)    = def <$> scopeLookup Δ x
checkExp Δ (C.eApp f e) = app <$> checkExp Δ f <*> checkExp Δ e

checkDecl : Scope Γ → C.Decl → M (Decl Γ)
checkDecl Δ (C.sig x t) = sig x <$> checkTy Δ t
checkDecl Δ (C.def x e) = def <$> scopeLookup Δ x <*> checkExp Δ e

snocDecl : SProgram Γ → Decl Γ → ∃ SProgram
snocDecl (Δ , P) (sig x A) = (_ ▷ A) , (Δ ▷ x) , wk1Program P  -- weaken the clauses
snocDecl (Δ , P) (def x e) = _ , Δ , decoUpdate x (e ∷_) P

checkDecls : C.Decls → M (∃ SProgram)
checkDecls (C.sg d) = snocDecl (ε , ε) <$> checkDecl ε d
checkDecls (C.snoc ds d) = do
  Γ , Δ , P ← checkDecls ds
  snocDecl (Δ , P) <$> checkDecl Δ d

checkProgram : C.Program -> M (∃ Program)
checkProgram (C.prg ds) = do
  Γ , Δ , P ← checkDecls ds
  return (Γ , P)

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
