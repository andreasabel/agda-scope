module WellScoped where

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Any using (here; there)

-- We have two kinds of names: module names and ordinary names.

data NameKind : Set where
  symb : NameKind  -- Ordinary symbol name.
  modl : NameKind  -- Module name.

-- Skeleton of a declaration

data Skel : Set where
  symb : Skel              -- function symbol declaration
  modl : List Skel → Skel  -- module declaration with content

-- A "de Bruijn index"

data Name : (k : NameKind) (s : Skel) → Set where
  symb : Name symb symb
  modl : ∀ ss → Name modl (modl ss)
  child : ∀{k s ss} (i : s ∈ ss) (n : Name k s) → Name k (modl ss)
