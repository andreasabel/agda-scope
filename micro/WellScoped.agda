-- Abstract syntax, intrinsically well-scoped.

open import Library
import Concrete as C

module WellScoped where

-- A scope is a zipper.

Scope = List C.Decls  -- snoc list

-- A "de Bruijn index": path of a name to its declaration.

mutual

  -- "Name xs s" means "xs declared in s"
  data Name : (xs : C.QName) (s : C.Decl) → Set where
    modl  : ∀ x {ss}                      → Name (C.qName x)   (C.modl x ss)
    child : ∀ x {xs ss} (n : LName xs ss) → Name (C.qual x xs) (C.modl x ss)

  -- "xs declared in rs"
  data LName (xs : C.QName) : (ss : C.Decls) → Set where
    here  : ∀{ss s} (n : Name xs s)   → LName xs (C.dSnoc ss s)
    there : ∀{ss s} (n : LName xs ss) → LName xs (C.dSnoc ss s)

-- "xs declared in sc"
record SName (xs : C.QName) (sc : Scope) : Set where
  constructor sname
  field
    {ss} : C.Decls
    i    : ss ∈ sc
    x    : LName xs ss

-- Decide whether xs is declared in s/ss/sc.

mutual
  name?  : ∀ xs s → Dec (Name xs s)
  -- C.ref does not declare a name.
  name? xs (C.ref q) = no λ()
  -- Resolve qualification.
  name? (C.qual x xs) (C.modl y ss) with x C.≟ y
  name? (C.qual x xs) (C.modl x ss) | yes!  with lname? xs ss
  ... | yes n = yes (child x n)
  ... | no ¬n = no (λ{ (child x n) → ¬n n})
  name? (C.qual x xs) (C.modl y ss) | no ¬p = no λ{ (child x n) → ¬p refl}
  -- Resolve CName.
  name? (C.qName x) (C.modl y ss) with x C.≟ y
  name? (C.qName x) (C.modl x ss) | yes!  = yes (Name.modl x)
  name? (C.qName x) (C.modl y ss) | no ¬p = no λ{ (modl x) → ¬p refl }

  lname? : ∀ xs ss → Dec (LName xs ss)
  -- List exhausted
  lname? xs C.dNil       = no λ()
  -- In head?
  lname? xs (C.dSnoc ss s) with name? xs s
  lname? xs (C.dSnoc ss s) | yes n = yes (here n)
  -- In tail?
  lname? xs (C.dSnoc ss s) | no ¬n with lname? xs ss
  lname? xs (C.dSnoc ss s) | no _  | yes n = yes (there n)
  lname? xs (C.dSnoc ss s) | no ¬n | no ¬m = no λ where
    (here n) → ¬n n
    (there m) → ¬m m

sname? : ∀ xs sc → Dec (SName xs sc)
-- List exhausted
sname? xs []        = no λ()
-- In head?
sname? xs (rs ∷ sc) with lname? xs rs
... | yes n = yes (sname here! n)
... | no ¬n with sname? xs sc
-- In tail?
...   | yes (sname i n) = yes (sname (there i) n)
...   | no ¬m = no λ where
          (sname here!     n) → ¬n n
          (sname (there i) m) → ¬m (sname i m)


-- Well-scoped declarations

mutual

  data Decl (sc : Scope) : C.Decl → Set where
    modl : ∀ x {ss} (ds : Decls sc ss) → Decl sc (C.modl x ss)
    ref  : ∀ {xs} (n : SName xs sc) → Decl sc (C.ref xs)

  data Decls (sc : Scope) : (ss : C.Decls) → Set where
    dNil  : Decls sc C.dNil
    dSnoc : ∀{ss s} (ds : Decls sc ss) (d  : Decl (ss ∷ sc) s) → Decls sc (C.dSnoc ss s)

-- Well-formed program

data Program : C.Program → Set where
  prg : ∀ x {ss} (ds : Decls [] ss) → Program (C.prg x ss)

-- Well-formed scope

data WScope : Scope → Set where
  sNil  : WScope []
  sSnoc : ∀{sc ss} → WScope sc → Decls sc ss → WScope (ss ∷ sc)


-- Weakening names.

wkSName : ∀{xs ss sc} → SName xs sc → SName xs (ss ∷ sc)
wkSName (sname i x) = sname (there i) x


-- -}
-- -}
-- -}
-- -}
