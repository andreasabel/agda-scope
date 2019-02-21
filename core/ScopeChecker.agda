module ScopeChecker where

open import Category.Functor using (RawFunctor)
open import Category.Applicative using (RawApplicative)
open import Category.Monad using (RawMonad) -- ; return; _>>=_)

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Categorical.Left using (functor; applicative; monad)

import Concrete as C
import WellScoped as A
open A

-- Scope map
--

-- data ScSkel : Skel → Set where
--   symb : (x : C.Name) → ScSkel symb
--   modl : (x : C.Name) {ss : Skels} → ScSkels ss → ScSkel (modl ss)

postulate
  ScMap : Scope → Set

-- Scope errors

data ScopeError : Set where

-- Monad for the scope checker
-- TODO

M : Set → Set
M = ScopeError ⊎_

open RawFunctor     {F = M} (functor _ _)
open RawApplicative {F = M} (applicative _ _)
open RawMonad       {M = M} (monad _ _)

checkExp : (e : C.Exp) (sc : Scope) (Γ : ScMap sc) → M (A.Exp sc)
checkExp e sc = {!!}
