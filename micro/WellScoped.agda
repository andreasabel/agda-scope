-- Abstract syntax, intrinsically well-scoped.

open import Library; open Dec
import Concrete as C

module WellScoped where

-- Access modifiers (private/public).

data Access : Set where
  publ : Access  -- Public access (from everywhere).  Exported.
  priv : Access  -- Private access only from within the module and its parents. Not Exported.

variable
  p p' : Access

data FlowTo : Access → Access → Set where
  publFlow : FlowTo publ p      -- Public can flow everywhere.
  privFlow : FlowTo priv priv   -- Private can only flow to private.

-- A scope is a zipper.

Scope = List C.Decls  -- snoc list

variable
  s  : C.Decl
  ss : C.Decls
  sc sc' : Scope
  x x' y : C.Name
  xs xs' : C.QName

-- A "de Bruijn index": path of a name to its declaration.

mutual

  -- "Name p xs s" means "qualified name xs declared p (or more accessible) in declaration s"
  data Name : (p : Access) (xs : C.QName) (s : C.Decl) → Set where
    modl   : ∀ x                        → Name p (C.qName x)   (C.modl x ss)
    inside : ∀ x (n : LName publ xs ss) → Name p (C.qual x xs) (C.modl x ss)
    inpriv :     (n : LName priv xs ss) → Name priv xs (C.priv ss)

  -- "name xs declared p in one of the declarations ss"
  data LName (p : Access) (xs : C.QName) : (ss : C.Decls) → Set where
    here  : ∀{ss s} (n : Name  p xs s)  → LName p xs (C.dSnoc ss s)
    there : ∀{ss s} (n : LName p xs ss) → LName p xs (C.dSnoc ss s)

-- "name xs declared in scope sc"
data SName (p : Access) (xs : C.QName) : (sc : Scope) → Set where
  site   : ∀{sc ss} → LName p xs ss → SName p xs (ss ∷ sc)
  parent : ∀{sc ss} → SName p xs sc → SName p xs (ss ∷ sc)

surj-inside : Surjective {A = LName publ xs ss} (inside {p = p} x)
surj-inside (inside x n) = n , refl

surj-inpriv : Surjective {A = LName priv xs ss} inpriv
surj-inpriv (inpriv n) = n , refl

lname-surjective : Surjective {B = LName p xs (C.dSnoc ss s)} [ here , there ]′
lname-surjective (here  n) = inj₁ n , refl
lname-surjective (there n) = inj₂ n , refl

sname-surjective : Surjective {B = SName p xs (ss ∷ sc)} [ site , parent ]′
sname-surjective (site   n) = inj₁ n , refl
sname-surjective (parent n) = inj₂ n , refl

-- Decide whether xs is declared in s/ss/sc.

mutual
  name?  : ∀ p xs s → Dec (Name p xs s)
  -- C.ref does not declare a name.
  name? p xs (C.ref q) = no λ()
  -- Step inside private blocks.
  name? publ xs (C.priv ss) = no λ()
  name? priv xs (C.priv ss) with lname? priv xs ss
  ... | yes n = yes (inpriv n)
  ... | no ¬n = no λ{ (inpriv n) → ¬n n }
  -- Resolve qualification.
  name? p (C.qual x xs) (C.modl y ss) with x C.≟ y | lname? publ xs ss
  name? p (C.qual x xs) (C.modl x ss) | yes!  | yes n = yes (inside x n)
  name? p (C.qual x xs) (C.modl x ss) | yes!  | no ¬n = no λ{ (inside x n) → ¬n n}
  name? p (C.qual x xs) (C.modl y ss) | no ¬p | _     = no λ{ (inside x n) → ¬p refl}
  -- Resolve CName.
  name? p (C.qName x) (C.modl y ss) with x C.≟ y
  name? p (C.qName x) (C.modl x ss) | yes!  = yes (Name.modl x)
  name? p (C.qName x) (C.modl y ss) | no ¬p = no λ{ (modl x) → ¬p refl }

  lname? : ∀ p xs ss → Dec (LName p xs ss)
  -- List exhausted
  lname? p xs C.dNil         = no λ()
  -- In head?, in tail?
  lname? p xs (C.dSnoc ss s) with name? p xs s | lname? p xs ss
  lname? p xs (C.dSnoc ss s) | yes n | _     = yes (here n)  -- Bias: later decls overwrite earlier ones.
  lname? p xs (C.dSnoc ss s) | no _  | yes m = yes (there m)
  lname? p xs (C.dSnoc ss s) | no ¬n | no ¬m = no λ where
    (here n) → ¬n n
    (there m) → ¬m m

sname? : ∀ p xs sc → Dec (SName p xs sc)
-- List exhausted
sname? p xs []        = no λ()
-- In head?, in tail?
sname? p xs (ss ∷ sc) with lname? p xs ss | sname? p xs sc
... | yes n | _     = yes (site n)   -- Bias: Inner scopes take precedence!
... | no ¬n | yes m = yes (parent m)
... | no ¬n | no ¬m = no λ where
  (site  n) → ¬n n
  (parent m) → ¬m m

-- Looking up all possible resolutions of a name (not respecting shadowing).

mutual
  lookupAll : ∀ p xs s → Enumeration (Name p xs s)
  -- C.ref does not declare a name.
  lookupAll p xs (C.ref q)    = emptyEnum λ()
  -- Step inside private blocks.
  lookupAll publ xs (C.priv ss) = emptyEnum λ()
  lookupAll priv xs (C.priv ss) = mapEnum inpriv surj-inpriv (llookupAll priv xs ss)
  -- Resolve qualification.
  lookupAll p (C.qual x xs) (C.modl y ss) with x C.≟ y | llookupAll publ xs ss
  lookupAll p (C.qual x xs) (C.modl x ss) | yes!  | e = mapEnum (inside x) surj-inside e
  lookupAll p (C.qual x xs) (C.modl y ss) | no ¬p | _ = emptyEnum λ{ (inside x n) → ¬p refl }
  -- Resolve CName.
  lookupAll p (C.qName x) (C.modl y ss) with x C.≟ y
  lookupAll p (C.qName x) (C.modl x ss) | yes!  = enum (modl x ∷ []) λ{ (modl x) → here! }
  lookupAll p (C.qName x) (C.modl y ss) | no ¬p = emptyEnum λ{ (modl x) → ¬p refl }

  llookupAll : ∀ p xs ss → Enumeration (LName p xs ss)
  -- List exhausted
  llookupAll p xs C.dNil = emptyEnum λ()
  -- In head?, in tail?
  llookupAll p xs (C.dSnoc ss s) with lookupAll p xs s | llookupAll p xs ss
  llookupAll p xs (C.dSnoc ss s) | e | e' = appendEnum here there lname-surjective e e'

slookupAll : ∀ p xs ss → Enumeration (SName p xs ss)
-- List exhausted
slookupAll p xs [] = emptyEnum λ()
-- In head?, in tail?
slookupAll p xs (ss ∷ sc) with llookupAll p xs ss | slookupAll p xs sc
slookupAll p xs (ss ∷ sc) | e | e' = appendEnum site parent sname-surjective e e'

-- Looking up possible resolutions of a name, discarding shadowed names of parents
-- ===============================================================================

-- There are two implementations that differ in the resolution of qualified names
-- like M.N
--
-- Alternative 1 (slookup):  Flat scope.
----------------------------------------
--
-- We consider the scope as a map from qualified names to content.
-- Children content shadows parent content, but if parent defines M.N and
-- child M.O, then M.N is still in scope.
--
-- Basically modules with the same name M get merged with child
-- content shadowing parent content.
--
-- Alternative 2 (sclookup):  Nested scope.
-------------------------------------------
--
-- We consider the scope as a map from single names to content.
-- The content may contain scopes again.
--
-- If the parent defines M.N and the child a module M, then the M.N of
-- the parent is no longer in scope even if the child does not define
-- M.N.
--
-- Since Agda does not allow shadowing of parent content by child
-- content, these alternatives coincide.  However, with a proposed
-- revision of Agda (issue #3801), these alternatives differ.  We
-- settle for the stricter alternative 2.  This does not merge modules.

-- Implementation of alternative 1 (slookup).
---------------------------------------------------------------------------
--
-- We lookup up the total qualified name, combining results.

mutual
  lookup : ∀ p xs s → List (Name p xs s)
  -- C.ref does not declare a name.
  lookup p xs (C.ref q)    = []
  -- Step inside private blocks.
  lookup publ xs (C.priv ss) = []
  lookup priv xs (C.priv ss) = map inpriv (llookup priv xs ss)
  -- Resolve qualification.
  lookup p (C.qual x xs) (C.modl y ss) with x C.≟ y | llookup publ xs ss
  lookup p (C.qual x xs) (C.modl x ss) | yes!  | ns = map (inside x) ns
  lookup p (C.qual x xs) (C.modl y ss) | no ¬p | _  = []
  -- Resolve CName.
  lookup p (C.qName x) (C.modl y ss) with x C.≟ y
  lookup p (C.qName x) (C.modl x ss) | yes!  = modl x ∷ []
  lookup p (C.qName x) (C.modl y ss) | no ¬p = []

  llookup : ∀ p xs ss → List (LName p xs ss)
  -- List exhausted
  llookup p xs C.dNil = []
  -- In head?, in tail?
  llookup p xs (C.dSnoc ss s) with lookup p xs s | llookup p xs ss
  llookup p xs (C.dSnoc ss s) | ns | ns' = map here ns ++ map there ns'  -- no shadowing of siblings!

slookup : ∀ p xs sc → List (SName p xs sc)
-- List exhausted
slookup p xs [] = []
-- In head?, in tail?
slookup p xs (ss ∷ sc) with llookup p xs ss | slookup p xs sc
slookup p xs (ss ∷ sc) | [] | ns = map parent ns  -- only keep when current site does not resolve the name
slookup p xs (ss ∷ sc) | ns | _  = map site   ns  -- discard parent occurrences if current site has one

-- Implementation of alternative 2 (sclookup)
---------------------------------------------------------------------------
--
-- Uses a success continuation f and a failure continuation ns.
-- Whenever we step into a module, we commit to this choice,
-- discarding the failure continuation.

mutual

  -- Lookup in a declaration

  clookup : ∀ p xs s
    → (List (Name p xs s) → List (SName p' xs' sc))
    → List (SName p' xs' sc)
    → List (SName p' xs' sc)
  -- C.ref does not declare a name.
  clookup p xs (C.ref q) f ns = ns
  -- Step inside private blocks.
  clookup publ xs (C.priv _ ) f ns = ns
  clookup priv xs (C.priv ps) f ns = lclookup priv xs ps (f ∘ map inpriv) ns
  -- Resolve CName.
  clookup p (C.qName x) (C.modl y ss) f ns with x C.≟ y
  clookup p (C.qName x) (C.modl x ss) f ns | yes!  = f (modl x ∷ [])
  clookup p (C.qName x) (C.modl y ss) f ns | no ¬p = ns
  -- Resolve qualification.
  clookup p (C.qual x xs) (C.modl y ss) f ns with x C.≟ y
  -- When we step into a module, we discard the alternatives!  No backtracking here!
  clookup p (C.qual x xs) (C.modl x ss) f ns | yes!  = lclookup publ xs ss (f ∘ map (inside x)) []
  clookup p (C.qual x xs) (C.modl y ss) f ns | no ¬p = ns

  -- Lookup in a list of declarations

  lclookup : ∀ p xs ss
    → (List (LName p xs ss) → List (SName p' xs' sc))
    → List (SName p' xs' sc)
    → List (SName p' xs' sc)
  -- List exhausted
  lclookup p xs C.dNil         f ns = ns
  -- In head?, in tail?
  lclookup p xs (C.dSnoc ss s) f ns = clookup p xs s (λ ns → f (map here ns) ++ ns') ns'
    where
    -- The fallback ns' is also propagated to the successful case.
    -- No shadowing of siblings!
    ns' = lclookup p xs ss (f ∘ map there) ns

-- Lookup in the scope

sclookup : ∀ p xs sc → List (SName p xs sc)
-- List exhausted
sclookup p xs [] = []
-- In head?, in tail?
sclookup p xs (ss ∷ sc) = lclookup p xs ss (map site) (map parent (sclookup p xs sc))
  -- only keep parent alternatives when current site does not resolve the name
  -- discard parent occurrences if current site has one


-- Well-scoped declarations

mutual

  data Decl (sc : Scope) : C.Decl → Set where
    modl : ∀ x  (ds : Decls sc ss) → Decl sc (C.modl x ss)
    ref  : (n  : SName priv xs sc) → Decl sc (C.ref xs)
    priv : (ds : Decls sc ss)      → Decl sc (C.priv ss)

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
