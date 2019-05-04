open import Library

module ScopeChecker where

import Concrete as C
open import WellScoped as A

-- Scope errors

data ScopeError : Set where
  notInScope : (x : C.QName) (sc : Scope) → ScopeError
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

-- Looking up a qualified name in the scope.

lookup : (xs : C.QName) (sc : Scope) → M (SName xs sc)
lookup xs sc = case sname? xs sc of λ where
  (yes n) → return n
  (no ¬n) → fail (notInScope xs sc)

-- Scope checking declarations.

mutual
  checkDecl : (d : C.Decl) (sc : Scope) → M (A.Decl sc d)

  checkDecl (C.ref xs) sc = do
    -- TODO: check where xs is ambiguous
    ys ← lookup xs sc
    return (ref ys)

  checkDecl (C.modl x ds) sc = do
    -- TODO: check whether x is shadowing something illegally
    ds' ← checkDecls ds sc
    return (modl x ds')

  checkDecls : (ds : C.Decls) (sc : Scope) → M (A.Decls sc ds)
  checkDecls C.dNil   sc = return dNil
  checkDecls (C.dSnoc ds d) sc = do
    ds' ← checkDecls ds sc
    d'  ← checkDecl  d  (ds ∷ sc)
    return (dSnoc ds' d')

checkProgram : (prg : C.Program) → M (A.Program prg)
checkProgram (C.prg x ds) = A.prg x <$> checkDecls ds []

{-
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

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
