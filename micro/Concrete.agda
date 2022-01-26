-- Restricted syntax as input for scope checker.

open import Library renaming (_≟_ to _==_); open Dec

module Concrete where

open import HierMod.AST public -- Export AST

-- Access modifiers (private/public).

data Access : Set where
  publ : Access  -- Public access (from everywhere).  Exported.
  priv : Access  -- Private access only from within the module and its parents. Not Exported.

-- Concatenation of qualified names.
-- _◇_ is chosen to represent the Semigroup operation (<>) of Haskell.

_◇_ : QName → QName → QName
qName x   ◇ ys = qual x ys
qual x xs ◇ ys = qual x (xs ◇ ys)

-- Injectivity and decidability.

injName : Injective name
injName refl = refl

_≟_ : (x y : Name) → Dec (x ≡ y)
name x ≟ name y = Dec.cong injName $ x == y



{-
unqual : Name → Exp
unqual x = ident (x ∷ [])

example : Decl
example = mDecl "Top"           -- module Top
    ( axiom "A" univ            --   A : Set
    ∷ axiom "a" (unqual "A")    --   a : A
    ∷ mDecl "M"                 --   module M
      ( axiom "b" (unqual "A")  --     b : A
      ∷ axiom "c" (unqual "A")  --     c : A
      ∷ [])
    ∷ axiom "d" (ident ("M" ∷ "c" ∷ []))    --   d : M.c
    ∷ [])
-}

-- -}
-- -}
-- -}
-- -}
-- -}
