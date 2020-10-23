-- Abstract syntax, intrinsically well-scoped.

open import Library; open Dec
import Concrete as C

module WellScoped where

-- A scope is a zipper.

Scope = List C.Decls  -- snoc list

-- A "de Bruijn index": path of a name to its declaration.

mutual

  -- "Name xs s" means "xs declared in s"
  data Name : (xs : C.QName) (s : C.Decl) → Set where
    modl   : ∀ x {ss}                      → Name (C.qName x)   (C.modl x ss)
    inside : ∀ x {xs ss} (n : LName xs ss) → Name (C.qual x xs) (C.modl x ss)

  -- "xs declared in rs"
  data LName (xs : C.QName) : (ss : C.Decls) → Set where
    here  : ∀{ss s} (n : Name xs s)   → LName xs (C.dSnoc ss s)
    there : ∀{ss s} (n : LName xs ss) → LName xs (C.dSnoc ss s)

-- "xs declared in sc"
data SName (xs : C.QName) : (sc : Scope) → Set where
  site   : ∀{sc ss} → LName xs ss → SName xs (ss ∷ sc)
  parent : ∀{sc ss} → SName xs sc → SName xs (ss ∷ sc)

surj-inside : ∀ {x xs ss} → Surjective {A = LName xs ss} (inside x)
surj-inside (inside x n) = n , refl

lname-surjective : ∀{xs ss s}
  → Surjective {B = LName xs (C.dSnoc ss s)} [ here , there ]′
lname-surjective (here  n) = inj₁ n , refl
lname-surjective (there n) = inj₂ n , refl

sname-surjective : ∀{xs ss sc}
  → Surjective {B = SName xs (ss ∷ sc)} [ site , parent ]′
sname-surjective (site   n) = inj₁ n , refl
sname-surjective (parent n) = inj₂ n , refl

-- Decide whether xs is declared in s/ss/sc.

mutual
  name?  : ∀ xs s → Dec (Name xs s)
  -- C.ref does not declare a name.
  name? xs (C.ref q) = no λ()
  -- Resolve qualification.
  name? (C.qual x xs) (C.modl y ss) with x C.≟ y | lname? xs ss
  name? (C.qual x xs) (C.modl x ss) | yes!  | yes n = yes (inside x n)
  name? (C.qual x xs) (C.modl x ss) | yes!  | no ¬n = no λ{ (inside x n) → ¬n n}
  name? (C.qual x xs) (C.modl y ss) | no ¬p | _     = no λ{ (inside x n) → ¬p refl}
  -- Resolve CName.
  name? (C.qName x) (C.modl y ss) with x C.≟ y
  name? (C.qName x) (C.modl x ss) | yes!  = yes (Name.modl x)
  name? (C.qName x) (C.modl y ss) | no ¬p = no λ{ (modl x) → ¬p refl }

  lname? : ∀ xs ss → Dec (LName xs ss)
  -- List exhausted
  lname? xs C.dNil         = no λ()
  -- In head?, in tail?
  lname? xs (C.dSnoc ss s) with name? xs s | lname? xs ss
  lname? xs (C.dSnoc ss s) | yes n | _     = yes (here n)  -- Bias: later decls overwrite earlier ones.
  lname? xs (C.dSnoc ss s) | no _  | yes m = yes (there m)
  lname? xs (C.dSnoc ss s) | no ¬n | no ¬m = no λ where
    (here n) → ¬n n
    (there m) → ¬m m

sname? : ∀ xs sc → Dec (SName xs sc)
-- List exhausted
sname? xs []        = no λ()
-- In head?, in tail?
sname? xs (ss ∷ sc) with lname? xs ss | sname? xs sc
... | yes n | _     = yes (site n)   -- Bias: Inner scopes take precedence!
... | no ¬n | yes m = yes (parent m)
... | no ¬n | no ¬m = no λ where
  (site  n) → ¬n n
  (parent m) → ¬m m

-- Looking up all possible resolutions of a name (not respecting shadowing).

mutual
  lookupAll : ∀ xs s → Enumeration (Name xs s)
  -- C.ref does not declare a name.
  lookupAll xs (C.ref q)    = emptyEnum λ()
  -- Resolve qualification.
  lookupAll (C.qual x xs) (C.modl y ss) with x C.≟ y | llookupAll xs ss
  lookupAll (C.qual x xs) (C.modl x ss) | yes!  | e = mapEnum (inside x) surj-inside e
  lookupAll (C.qual x xs) (C.modl y ss) | no ¬p | _ = emptyEnum λ{ (inside x n) → ¬p refl }
  -- Resolve CName.
  lookupAll (C.qName x) (C.modl y ss) with x C.≟ y
  lookupAll (C.qName x) (C.modl x ss) | yes!  = enum (modl x ∷ []) λ{ (modl x) → here! }
  lookupAll (C.qName x) (C.modl y ss) | no ¬p = emptyEnum λ{ (modl x) → ¬p refl }

  llookupAll : ∀ xs ss → Enumeration (LName xs ss)
  -- List exhausted
  llookupAll xs C.dNil = emptyEnum λ()
  -- In head?, in tail?
  llookupAll xs (C.dSnoc ss s) with lookupAll xs s | llookupAll xs ss
  llookupAll xs (C.dSnoc ss s) | e | e' = appendEnum here there lname-surjective e e'

slookupAll : ∀ xs ss → Enumeration (SName xs ss)
-- List exhausted
slookupAll xs [] = emptyEnum λ()
-- In head?, in tail?
slookupAll xs (ss ∷ sc) with llookupAll xs ss | slookupAll xs sc
slookupAll xs (ss ∷ sc) | e | e' = appendEnum site parent sname-surjective e e'

-- Looking up possible resolutions of a name, discarding shadowed names of parents.

mutual
  lookup : ∀ xs s → List (Name xs s)
  -- C.ref does not declare a name.
  lookup xs (C.ref q)    = []
  -- Resolve qualification.
  lookup (C.qual x xs) (C.modl y ss) with x C.≟ y | llookup xs ss
  lookup (C.qual x xs) (C.modl x ss) | yes!  | ns = map (inside x) ns
  lookup (C.qual x xs) (C.modl y ss) | no ¬p | _  = []
  -- Resolve CName.
  lookup (C.qName x) (C.modl y ss) with x C.≟ y
  lookup (C.qName x) (C.modl x ss) | yes!  = modl x ∷ []
  lookup (C.qName x) (C.modl y ss) | no ¬p = []

  llookup : ∀ xs ss → List (LName xs ss)
  -- List exhausted
  llookup xs C.dNil = []
  -- In head?, in tail?
  llookup xs (C.dSnoc ss s) with lookup xs s | llookup xs ss
  llookup xs (C.dSnoc ss s) | ns | ns' = map here ns ++ map there ns'  -- no shadowing of siblings!

slookup : ∀ xs ss → List (SName xs ss)
-- List exhausted
slookup xs [] = []
-- In head?, in tail?
slookup xs (ss ∷ sc) with llookup xs ss | slookup xs sc
slookup xs (ss ∷ sc) | [] | ns = map parent ns  -- only keep when current site does not resolve the name
slookup xs (ss ∷ sc) | ns | _  = map site   ns  -- discard parent occurrences if current site has one


-- Well-scoped declarations

mutual

  data Decl (sc : Scope) : C.Decl → Set where
    modl : ∀ x {ss} (ds : Decls sc ss) → Decl sc (C.modl x ss)
    ref  : ∀ {xs}   (n  : SName xs sc) → Decl sc (C.ref xs)

  data Decls (sc : Scope) : (ss : C.Decls) → Set where
    dNil  : Decls sc C.dNil
    dSnoc : ∀{ss s} (ds : Decls sc ss) (d : Decl (ss ∷ sc) s) → Decls sc (C.dSnoc ss s)

-- Well-formed program

data Program : C.Program → Set where
  prg : ∀ x {ss} (ds : Decls [] ss) → Program (C.prg x ss)

-- Well-formed scope

data WScope : Scope → Set where
  sNil  : WScope []
  sSnoc : ∀{sc ss} → WScope sc → Decls sc ss → WScope (ss ∷ sc)



-- -}
-- -}
-- -}
-- -}
