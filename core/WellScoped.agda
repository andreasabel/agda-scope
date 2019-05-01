-- Abstract syntax, intrinsically well-scoped.

open import Library
import Concrete as C

module WellScoped where

-- We have two kinds of names: module names and ordinary names.

data NameKind : Set where
  symb : NameKind  -- Ordinary symbol name.
  modl : NameKind  -- Module name.

-- Skeleton of a declaration:
-- Contains only the declared names.

mutual
  data Skel : Set where
    symb : (x : C.Name) → Skel               -- Function symbol declaration.
    modl : (x : C.Name) (ss : Skels) → Skel  -- Module declaration with content (names declared there).

  Skels = List Skel  -- reversed w.r.t to the ordering in the file (last on top)

-- A scope is a zipper.

Scope = List Skels

-- A "de Bruijn index"

mutual

  -- "(k,xs) ∈ s"
  data Name : (k : NameKind) (xs : C.QName) (s : Skel) → Set where
    symb  : ∀ x                               → Name symb (x ∷ []) (symb x)
    modl  : ∀ x {ss}                          → Name modl (x ∷ []) (modl x ss)
    child : ∀ x {k xs ss} (n : LName k xs ss) → Name k (x ∷⁺ xs)   (modl x ss)

  -- "(k,xs) ∈ rs"
  record LName (k : NameKind) (xs : C.QName) (rs : Skels) : Set where
    inductive; constructor lname
    field
      {s} : Skel
      j   : s ∈ rs
      x   : Name k xs s

-- "k ∈ sc"
record SName (k : NameKind) (xs : C.QName) (sc : Scope) : Set where
  constructor sname
  field
    {rs} : Skels
    i    : rs ∈ sc
    x    : LName k xs rs

pattern name i j x = sname i (lname j x)

-- Weakening names.

wkLName : ∀{k xs s rs} → LName k xs rs → LName k xs (s ∷ rs)
wkLName (lname i x) = lname (there i) x

wkSName : ∀{k xs rs sc} → SName k xs sc → SName k xs (rs ∷ sc)
wkSName (sname i x) = sname (there i) x

-- Being a Name is decidable (this is the lookup function).

mutual
  name?  : ∀ k xs s → Dec (Name k xs s)
  -- Resolve qualification.
  name? k (x ∷ z ∷ zs) (modl y ss) with x ≟ y
  name? k (x ∷ z ∷ zs) (modl x ss) | yes!  with lname? k (z ∷ zs) ss
  ... | yes n = yes (child x n)
  ... | no ¬n = no (λ{ (child x n) → ¬n n})
  name? k (x ∷ z ∷ zs) (modl y ss) | no ¬p = no λ{ (child x n) → ¬p refl}
  -- Overqualified.
  name? k (x ∷ _ ∷ _ ) (symb y) = no λ()  -- A symb has no children.
  -- Resolve CName.
  name? modl (x ∷ []) (modl y ss) with x ≟ y
  name? modl (x ∷ []) (modl x ss) | yes!  = yes (Name.modl x)
  name? modl (x ∷ []) (modl y ss) | no ¬p = no λ{ (modl x) → ¬p refl }
  name? symb (x ∷ []) (symb y)    with x ≟ y
  name? symb (x ∷ []) (symb x)    | yes!  = yes (symb x)
  name? symb (x ∷ []) (symb y)    | no ¬p = no λ{ (symb x) → ¬p refl }
  -- modl/symb mismatch.
  name? modl (_ ∷ []) (symb _) = no λ()
  name? symb (_ ∷ []) (modl _ _) = no λ()

  lname? : ∀ k xs rs → Dec (LName k xs rs)
  -- List exhausted
  lname? k xs []       = no λ()
  -- In head?
  lname? k xs (s ∷ rs) with name? k xs s
  lname? k xs (s ∷ rs) | yes n = yes (lname here! n)
  -- In tail?
  lname? k xs (s ∷ rs) | no ¬n with lname? k xs rs
  lname? k xs (s ∷ rs) | no _  | yes (lname j n) = yes (lname (there j) n)
  lname? k xs (s ∷ rs) | no ¬n | no ¬m = no λ where
    (lname here!     n) → ¬n n
    (lname (there j) m) → ¬m (lname j m)

sname? : ∀ k xs sc → Dec (SName k xs sc)
-- List exhausted
sname? k xs []        = no λ()
-- In head?
sname? k xs (rs ∷ sc) with lname? k xs rs
... | yes n = yes (sname here! n)
... | no ¬n with sname? k xs sc
-- In tail?
...   | yes (sname i n) = yes (sname (there i) n)
...   | no ¬m = no λ where
          (sname here!     n) → ¬n n
          (sname (there i) m) → ¬m (sname i m)

-- Well-scoped expressions

data Exp (sc : Scope) : Set where
  ident : ∀{xs} → SName symb xs sc → Exp sc
  univ  : Exp sc

mutual

  data Decl (sc : Scope) : Skel → Set where
    sDecl : ∀ x      (ty : Exp sc)         → Decl sc (symb x)
    mDecl : ∀ x {rs} (ds : Decls sc [] rs) → Decl sc (modl x rs)  -- OR: reverse rs

  -- rs  : Skels before the Decls
  -- rs' : Skels after  the Decls
  data Decls (sc : Scope) (rs : Skels) : (rs' : Skels) → Set where
    []  : Decls sc rs rs
    _∷_ : ∀{s rs'}
          (d  : Decl (rs ∷ sc) s)       -- s is the scope declared by d
          (ds : Decls sc (s ∷ rs) rs')  -- we append s to rs to check the remaining ds
              → Decls sc rs       rs'

infixr 5 _∷_

module Example where

  skel : Skel
  skel = modl "Top" (symb "d" ∷ modl "M" (symb "c" ∷ symb "b" ∷ []) ∷ symb "a" ∷ symb "A" ∷ [])
  example : Decl [] skel
  example = mDecl "Top"                                                               -- module Top
    ( sDecl "A" univ                                                                  --   A : Set
    ∷ sDecl "a" (ident (name here! here! (symb "A")))                                 --   a : A
    ∷ mDecl "M"                                                                       --   module M
      ( sDecl "b" (ident (name (there here!) (there here!) (symb "A")))               --     b : A
      ∷ sDecl "c" (ident (name (there here!) (there here!) (symb "A")))               --     c : A
      ∷ [])
    ∷ sDecl "d" (ident (name here! here! (child "M" (lname here! (symb "c"))))) ∷ []) --   d : M.c


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
