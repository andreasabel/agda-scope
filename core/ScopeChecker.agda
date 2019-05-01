open import Library

module ScopeChecker where

import Concrete as C
import WellScoped as A
open A hiding (module Example)

-- Scope errors

data ScopeError : Set where
  notInScope : (x : C.QName) (k : NameKind) (sc : Scope) → ScopeError
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


module DeprecatedLookup where

  -- Looking up a qualified name in module skeletons.

  mutual
    lookupD : (xs : C.QName) (k : NameKind) (s : Skel) → M (Name k xs s)
    lookupD (x ∷ []) symb (symb y) = do
      refl ← eqCName x y
      return (symb x)
    lookupD (x ∷ []) modl (modl y ss) = do
      refl ← eqCName x y
      return (modl x)
    lookupD (x ∷ (z ∷ zs)) k (modl y ss) = do
      refl ← eqCName x y
      child x <$> lookupL (z ∷ zs) k ss
    lookupD xs k _ = fail (notInScope xs k [])

    lookupL : (xs : C.QName) (k : NameKind) (ss : Skels) → M (LName k xs ss)
    lookupL xs k [] = fail (notInScope xs k [])
    lookupL xs k (s ∷ ss)
      =   (lname here! <$> lookupD xs k s)
      <|> (wkLName <$> lookupL xs k ss)

  -- Looking up a qualified name in the scope.

  lookup : (xs : C.QName) (k : NameKind) (sc : Scope) → M (SName k xs sc)
  lookup xs k [] = fail (notInScope xs k [])
  lookup xs k (s ∷ sc)
    =   (sname here! <$> lookupL xs k s)
    <|> (wkSName     <$> lookup xs k sc)


-- Looking up a qualified name in the scope.

lookup : (xs : C.QName) (k : NameKind) (sc : Scope) → M (SName k xs sc)
lookup xs k sc = case sname? k xs sc of λ where
  (yes n) → return n
  (no ¬n) → fail (notInScope xs k sc)

-- Scope checking expressions.

checkExp : (e : C.Exp) (sc : Scope) → M (A.Exp sc)
checkExp C.univ       sc = return A.univ
checkExp (C.ident xs) sc = A.ident <$> lookup xs symb sc

-- Scope checking declarations.

mutual
  checkDecl : (d : C.Decl) (sc : Scope) → M (∃ λ s → A.Decl sc s)

  checkDecl (C.axiom x ty) sc = do
    -- TODO: check whether x is shadowing something illegally
    ty' ← checkExp ty sc
    return (symb x , sDecl x ty')

  checkDecl (C.mDecl x ds) sc = do
    -- TODO: check whether x is shadowing something illegally
    rs , ds' ← checkDecls ds sc []
    return (modl x rs , mDecl x ds')

  checkDecls : (ds : C.Decls) (sc : Scope) (rs : Skels) → M (∃ λ rs' → A.Decls sc rs rs')
  checkDecls []       sc rs = return (rs , [])
  checkDecls (d ∷ ds) sc rs = do
    s   , d'  ← checkDecl  d  (rs ∷ sc)
    rs' , ds' ← checkDecls ds sc (s ∷ rs)
    return (rs' , d' ∷ ds')

-- Example.

module Example1 where

  open A.Example

  scope : Scope
  scope = (skel ∷ []) ∷ []

  qname : C.QName
  qname = "Top" ∷ "M" ∷ "c" ∷ []

  test = checkExp (C.ident qname) scope

module Example2 where

  module AE = A.Example

  test = checkDecl C.example []

  _ : test ≡ return (_ , AE.example)
  _ = refl
