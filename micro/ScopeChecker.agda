open import Library

module ScopeChecker where

import Concrete as C
open import WellScoped as A

-- Scope errors

data ScopeError : Set where
  notInScope : ∀{xs : C.QName} {sc} (¬n : ¬ SName xs sc) → ScopeError
  shadows    : ∀{xs sc} (n : SName xs sc) → ScopeError
  ambiguous  : ∀{xs sc} (n₁ n₂ : SName xs sc) (ns : List (SName xs sc)) → ScopeError

printScopeError : ScopeError → String
printScopeError (notInScope {xs = xs} ¬n)       = "not in scope: " String.++ C.printQName xs
printScopeError (shadows    {xs = xs} n)        = "illegal shadowing of " String.++ C.printQName xs
printScopeError (ambiguous  {xs = xs} n₁ n₂ ns) = "ambiguous name: " String.++ C.printQName xs

-- Monad for the scope checker

M : Set → Set
M = ScopeError ⊎_

open RawMonad {M = M} (monad _ _)

pattern fail err = inj₁ err

-- Looking up a qualified name in the scope.

lookup : (xs : C.QName) (sc : Scope) → M (SName xs sc)
lookup xs sc = case sname? xs sc of λ where
  (yes n) → return n
  (no ¬n) → fail (notInScope ¬n)

-- Scope checking declarations.

mutual
  checkDecl : (d : C.Decl) (sc : Scope) → M (A.Decl sc d)

  checkDecl (C.ref xs) sc with slookupAll xs sc
  ... | enum (n ∷ [])       _ = return (ref n)
  ... | enum []            ¬n = fail (notInScope λ n → case ¬n n of λ())
  ... | enum (n₁ ∷ n₂ ∷ ns) _ = fail (ambiguous n₁ n₂ ns)

  checkDecl (C.modl x ds) sc with sname? (C.qName x) sc
  -- Agda <= 2.6.0 style shadowing rules: x must not be in scope
  ... | yes n = fail (shadows n)
  ... | no  _ = do
    ds' ← checkDecls ds sc
    return (modl x ds')

  checkDecls : (ds : C.Decls) (sc : Scope) → M (A.Decls sc ds)
  checkDecls C.dNil         sc = return dNil
  checkDecls (C.dSnoc ds d) sc = do
    ds' ← checkDecls ds sc
    d'  ← checkDecl  d  (ds ∷ sc)
    return (dSnoc ds' d')

checkProgram : (prg : C.Program) → M (A.Program prg)
checkProgram (C.prg x ds) = A.prg x <$> checkDecls ds []

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
