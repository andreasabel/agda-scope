
{-# OPTIONS --allow-incomplete-matches #-}

open import Library

module ScopeChecker where

import Concrete as C
open import WellScoped as A

-- Scope errors

data ScopeError : Set where
  notInScope' : (xs : C.QName) → ScopeError
  notInScope  : (¬n : ¬ SName p xs sc) → ScopeError
  shadows     : (n : SName p xs sc) → ScopeError
  ambiguous   : (n₁ n₂ : SName p xs sc) (ns : List (SName p xs sc)) → ScopeError

printScopeError : ScopeError → String
printScopeError (notInScope' xs)                = "not in scope: " String.++ C.printQName xs
printScopeError (notInScope {xs = xs} ¬n)       = "not in scope: " String.++ C.printQName xs
printScopeError (shadows    {xs = xs} n)        = "illegal shadowing of " String.++ C.printQName xs
printScopeError (ambiguous  {xs = xs} n₁ n₂ ns) = "ambiguous name: " String.++ C.printQName xs

-- Monad for the scope checker

M : Set → Set
M = ScopeError ⊎_

open RawMonad {F = M} (monad _ _)

pattern fail err = inj₁ err

-- Scope checking declarations.

mutual
  checkDecl : (d : C.Decl) (sc : Scope) → M (A.Decl sc d)

  -- Agda <= 2.6.1 style: current site may not shadow parents
  checkDecl (C.opn xs dir) sc with slookupAll C.priv xs sc
  ... | enum (n ∷ [])       _ = return (opn n dir)
  ... | enum []            ¬n = fail (notInScope λ n → case ¬n n of λ())
  ... | enum (n₁ ∷ n₂ ∷ ns) _ = fail (ambiguous n₁ n₂ ns)
  -- -- ALT: current site may shadow parents
  -- checkDecl (C.opn xs dir) sc with sclookup C.priv xs sc
  -- ... | (n ∷ [])       = return (opn n dir)
  -- ... | []             = fail (notInScope' xs)
  -- ... | (n₁ ∷ n₂ ∷ ns) = fail (ambiguous n₁ n₂ ns)

  -- Agda <= 2.6.1 style shadowing rules: x must not be in scope
  -- checkDecl (C.modl x ds) sc with sname? (C.qName x) sc
  -- ... | yes n = fail (shadows n)
  -- ... | no  _ = do
  -- ALT shadowing rules: x must not be in scope in current site
  checkDecl (C.modl x ds) sc with slookup C.priv (C.qName x) sc
  ... | (site n ∷ _) = fail (shadows (site {sc = sc} (wk1LName n) ))
  ... | _            = modl x <$> checkDecls ds sc

  checkDecl (C.priv ds) sc = A.priv <$> checkDecls ds sc

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
