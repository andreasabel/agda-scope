-- Restricted syntax as input for scope checker.

open import Library renaming (_≟_ to _==_); open Dec
-- open import Library using (List; Bool; Dec; yes!; no; _≡_)

module Concrete where

open import HierMod.AST public -- Export AST

-- -- open import Library using (module String) renaming (_≟_ to _==_)

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

module _ {a b} {A : Set a}{B : Set b} where

  module _ {f : A → B} (inj : Injective f) where

    congDec : ∀{x y} → Dec (x ≡ y) → Dec (f x ≡ f y)
    congDec yes!    = yes!
    congDec (no ¬p) = no (¬p ∘ inj)

    injDec : ∀{x y} → Dec (f x ≡ f y) → Dec (x ≡ y)
    injDec (yes p) = yes (inj p)
    injDec (no ¬p) = no (¬p ∘ cong f)

injName : Injective name
injName refl = refl

postulate
  injStringFromList : Injective String.fromList

_≟_ : (x y : Name) → Dec (x ≡ y)
name x ≟ name y = congDec injName $ x == y
  -- congDec injName $
  -- injDec injStringFromList $
  -- String.fromList x == String.fromList y

  -- open import Library using (module String) renaming (primStringEquality to _==_)


{-
_≟_ : Name → Name → Bool
name x ≟ name y = {!String.fromList x == String.fromList y !}
  where
  open import Library using (module String) renaming (primStringEquality to _==_)
  open import Library using (module String) renaming (_≟_ to _==_)

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
