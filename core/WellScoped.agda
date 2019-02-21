module WellScoped where

open import Data.List.Base using (List; []; _∷_; reverse)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Any using (here; there)

open import Relation.Binary.PropositionalEquality using (refl)

pattern here! = here refl

-- We have two kinds of names: module names and ordinary names.

data NameKind : Set where
  symb : NameKind  -- Ordinary symbol name.
  modl : NameKind  -- Module name.

-- Skeleton of a declaration

mutual
  data Skel : Set where
    symb : Skel              -- function symbol declaration
    modl : Skels → Skel  -- module declaration with content

  Skels = List Skel  -- reversed w.r.t to the ordering in the file (last on top)

Scope = List Skels

-- A "de Bruijn index"

data Name : (k : NameKind) (s : Skel) → Set where
  symb  : Name symb symb
  modl  : ∀{ss} → Name modl (modl ss)
  child : ∀{k s ss} (i : s ∈ ss) (n : Name k s) → Name k (modl ss)

record SName (k : NameKind) (sc : Scope) : Set where
  constructor sname
  field
    {rs} : Skels
    {s}  : Skel
    i : rs ∈ sc
    j : s  ∈ rs
    x : Name k s

data Exp (sc : Scope) : Set where
  def  : SName symb sc → Exp sc
  univ : Exp sc

mutual
  data Decl (z : Scope) : Skel → Set where
    sDecl : (ty : Exp z) → Decl z symb
    mDecl : ∀{rs} (ds : Decls z [] rs) → Decl z (modl rs)  -- OR: reverse rs

  data Decls (z : Scope) (rs : Skels) : (rs' : Skels) → Set where
    []  : Decls z rs rs
    _∷_ : ∀{s rs'} (d : Decl (rs ∷ z) s) (ds : Decls z (s ∷ rs) rs') → Decls z rs rs'

infixr 5 _∷_

example : Decl [] (modl (symb ∷ modl (symb ∷ []) ∷ symb ∷ symb ∷ []))
example = mDecl                                              -- module Top
  ( sDecl univ                                               --   A : Set
  ∷ sDecl (def (sname here! here! symb))                     --   a : A
  ∷ mDecl                                                    --   module M
    ( sDecl (def (sname (there here!) (there here!) symb))   --     b : A
    ∷ [])
  ∷ sDecl (def (sname here! here! (child here! symb))) ∷ []) --   c : b

-- module Top where
--   A : Set
--   a : A
--   module M where

{-
-- A "de Bruijn index"

data Name : (k : NameKind) (s : Skel) → Set where
  symb  : Name symb symb
  modl  : ∀{ss} → Name modl (modl ss)
  child : ∀{k s ss} (i : s ∈ ss) (n : Name k s) → Name k (modl ss)

-- Zipper pointing to the end.

data SkelZip : Set where
  here   : (rs : Skels) → SkelZip    -- reversed lists
  inside : (rs : Skels) (z : SkelZip) → SkelZip

-- addSymb : SkelZip → SkelZip
-- addSymb (here rs) = here (symb ∷ rs)
-- addSymb (inside rs z) = inside rs (addSymb z)

-- addNewModl : SkelZip → SkelZip
-- addNewModl (here rs) = {!!}

add : NameKind → SkelZip → SkelZip
add symb (here rs) = here (symb ∷ rs)
add modl (here rs) = inside rs (here [])
add k (inside rs z) = inside rs (add k z)

stepOutside : SkelZip → SkelZip
stepOutside (here rs) = here rs
stepOutside (inside rs (here rs')) = here (modl rs' ∷ rs)
stepOutside (inside rs z) = inside rs (stepOutside z)

addSkel : Skel → SkelZip → SkelZip
addSkel s (here rs) = here (s ∷ rs)
addSkel s (inside rs z) = inside rs (addSkel s z)

postulate Exp : Set

module FOO where
  mutual
    data Decl (z : Scope) : Skel → Set where
      sDecl : (ty : Exp) → Decl z symb
      mDecl : ∀{rs} (ds : Decls z [] rs) → Decl z (modl (reverse rs))  -- OR: don't reverse


    data Decls (z : Skels) (rs : Skels) : (rs' : Skels) → Set where
      nil  : Decls z rs rs
      cons : ∀{s rs'} (d : Decl (rs ∷ z) s) (ds : Decls z (s ∷ rs) rs') → Decls z rs rs'


module BLA where
  mutual
    data Decl (z : SkelZip) : Skel → Set where
      sDecl : (ty : Exp) → Decl z symb
      mDecl : ∀{rs} (ds : Decls (add modl z) [] rs) → Decl z (modl (reverse rs))


    data Decls (z : SkelZip) (rs : Skels) : (rs' : Skels) → Set where
      nil  : Decls z rs rs
      cons : ∀{s rs'} (d : Decl z s) (ds : Decls (addSkel s z) (s ∷ rs) rs') → Decls z rs rs'


mutual
  data Decl (z : SkelZip) : SkelZip → Set where
    sDecl : (ty : Exp) → Decl z (add symb z)
    mDecl : ∀{z'} (ds : Decls (add modl z) z') → Decl z (stepOutside z')


  data Decls (s : SkelZip) : (s' : SkelZip) → Set where
    nil : Decls s s
    cons : ∀{s' s''} (d : Decl s s') (ds : Decls s' s'') → Decls s s''



{-

data Decl (s : Skel) : (k : NameKind) → Name k s → Set where

addName : ∀ k s → Name k s → Skel

data Decls (s : Skel) : (s' : Skel) → Set where
  nil : Decls s s
  cons : (d : Decl s s') (ds : Decls s' s'') → Decls s s''

-- -}
-- -}
-- -}
-- -}