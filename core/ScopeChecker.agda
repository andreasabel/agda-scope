module ScopeChecker where

open import Category.Functor using (RawFunctor)
open import Category.Applicative using (RawApplicative)
open import Category.Monad using (RawMonad) -- ; return; _>>=_)

open import Data.List using (List; []; _∷_)

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Categorical.Left using (functor; applicative; monad)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Concrete as C
import WellScoped as A
open A hiding (module Example)

-- Scope map
--

-- data ScSkel : Skel → Set where
--   symb : (x : C.Name) → ScSkel symb
--   modl : (x : C.Name) {ss : Skels} → ScSkels ss → ScSkel (modl ss)

postulate
  ScMap : Scope → Set

-- Scope errors

data ScopeError : Set where
  notInScope : ∀ (x : C.QName) (k : NameKind) (sc : Scope) → ScopeError
  -- Internal errors:
  notEqual : (x y : C.Name) → ScopeError

pattern fail err = inj₁ err

-- Monad for the scope checker
-- TODO

M : Set → Set
M = ScopeError ⊎_

-- open RawFunctor     {F = M} (functor _ _)
-- open RawApplicative {F = M} (applicative _ _)
open RawMonad       {M = M} (monad _ _)

_<|>_ : ∀{A} → M A → M A → M A
fail x <|> m' = m'
m      <|> m' = m

eqCName : (x y : C.Name) → M (x ≡ y)
eqCName x y with x C.≟ y
... | yes p = return p
... | no ¬p = fail (notEqual x y)

mutual
  lookupD : (x : C.QName) (k : NameKind) (s : Skel) → M (Name k s)
  lookupD (x ∷ []) symb (symb y) = do
    refl ← eqCName x y
    return symb
  lookupD (x ∷ []) modl (modl y ss) = do
    refl ← eqCName x y
    return modl
  lookupD (x ∷ xs) k (modl y ss) = do
    refl ← eqCName x y
    child <$> lookupL xs k ss
  lookupD x k _ = fail (notInScope x k [])

  lookupL : (x : C.QName) (k : NameKind) (ss : Skels) → M (LName k ss)
  lookupL x k [] = fail (notInScope x k [])
  lookupL x k (s ∷ ss)
    =   (lname here! <$> lookupD x k s)
    <|> (wkLName <$> lookupL x k ss)

lookup : (x : C.QName) (k : NameKind) (sc : Scope) → M (SName k sc)
lookup x k [] = fail (notInScope x k [])
lookup x k (s ∷ sc)
  =   (gname here! <$> lookupL x k s)
  <|> (wkSName     <$> lookup x k sc)

checkExp : (e : C.Exp) (sc : Scope) → M (A.Exp sc)
checkExp C.univ      sc = return A.univ
checkExp (C.ident x) sc = A.def <$> lookup x symb sc

-- Example.

module Example where

  open A.Example

  scope : Scope
  scope = (skel ∷ []) ∷ []

  qname : C.QName
  qname = "Top" ∷ "M" ∷ "c" ∷ []

  test = checkExp (C.ident qname) scope
