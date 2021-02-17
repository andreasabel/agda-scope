-- Abstract syntax, intrinsically well-scoped.

{-# OPTIONS --allow-incomplete-matches #-}

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
  s s'   : C.Decl
  ss ss' : C.Decls
  sc sc' : Scope
  x x' y : C.Name
  xs xs' : C.QName

-- A "de Bruijn index": path of a name to its declaration.

mutual

  -- "Name p xs s" means "qualified name xs declared p (or more accessible) in declaration s"
  data Name (sc : Scope) : (p : Access) (xs : C.QName) (s : C.Decl) → Set where
    modl   : ∀ x                           → Name sc p (C.qName x)   (C.modl x ss)
    inside : ∀ x (n : LName publ xs sc ss) → Name sc p (C.qual x xs) (C.modl x ss)
    inpriv :     (n : LName priv xs sc ss) → Name sc priv xs (C.priv ss)

  -- "name xs declared p in one of the declarations ss"
  data LName (p : Access) (xs : C.QName) : (sc : Scope) (ss : C.Decls) → Set where
    here  : ∀{ss s} (n : Name  (ss ∷ sc) p xs s) → LName p xs sc (C.dSnoc ss s)
    there : ∀{ss s} (n : LName       p xs sc ss) → LName p xs sc (C.dSnoc ss s)

-- "name xs declared in scope sc"
data SName (p : Access) (xs : C.QName) : (sc : Scope) → Set where
  site   : ∀{sc ss} → (n : LName p xs sc ss) → SName p xs (ss ∷ sc)
  parent : ∀{sc ss} → (n : SName p xs sc)    → SName p xs (ss ∷ sc)

surj-inside : Surjective {A = LName publ xs sc ss} (inside {p = p} x)
surj-inside (inside x n) = n , refl

surj-inpriv : Surjective {A = LName priv xs sc ss} inpriv
surj-inpriv (inpriv n) = n , refl

lname-surjective : Surjective {B = LName p xs sc (C.dSnoc ss s)} [ here , there ]′
lname-surjective (here  n) = inj₁ n , refl
lname-surjective (there n) = inj₂ n , refl

sname-surjective : Surjective {B = SName p xs (ss ∷ sc)} [ site , parent ]′
sname-surjective (site   n) = inj₁ n , refl
sname-surjective (parent n) = inj₂ n , refl

-- Lifting to a larger scope.

mutual
  wkName  : (τ : sc ⊆ sc') (n : Name sc p xs s)   → Name sc' p xs s
  wkName τ (modl x)     = modl x
  wkName τ (inside x n) = inside x (wkLName τ n)
  wkName τ (inpriv n)   = inpriv   (wkLName τ n)

  wkLName : (τ : sc ⊆ sc') (n : LName p xs sc ss) → LName p xs sc' ss
  wkLName τ (here n)  = here  (wkName (refl ∷ τ) n)
  wkLName τ (there n) = there (wkLName τ n)

  wkSName : (τ : sc ⊆ sc') (n : SName p xs sc)    → SName p xs sc'
  wkSName (ss ∷ʳ τ)  n          = parent (wkSName τ n)
  wkSName (refl ∷ τ) (site n)   = site   (wkLName τ n)
  wkSName (refl ∷ τ) (parent n) = parent (wkSName τ n)

wk1Name : Name sc p xs s → Name (ss ∷ sc) p xs s
wk1Name = wkName (_ ∷ʳ ⊆-refl)

wk1LName : LName p xs sc ss → LName p xs (ss' ∷ sc) ss
wk1LName = wkLName (_ ∷ʳ ⊆-refl)

-- Decide whether xs is declared in s/ss/sc.

mutual
  name? : ∀ sc p xs s → Dec (Name sc p xs s)
  -- C.opn C.importNothingdoes not declare a name.
  name? sc p xs (C.opn q C.importNothing) = no λ()
  -- Step inside private blocks.
  name? sc publ xs (C.priv ss) = no λ()
  name? sc priv xs (C.priv ss) with lname? priv xs sc ss
  ... | yes n = yes (inpriv n)
  ... | no ¬n = no λ{ (inpriv n) → ¬n n }
  -- Resolve qualification.
  name? sc p (C.qual x xs) (C.modl y ss) with x C.≟ y | lname? publ xs sc ss
  name? sc p (C.qual x xs) (C.modl x ss) | yes!  | yes n = yes (inside x n)
  name? sc p (C.qual x xs) (C.modl x ss) | yes!  | no ¬n = no λ{ (inside x n) → ¬n n}
  name? sc p (C.qual x xs) (C.modl y ss) | no ¬p | _     = no λ{ (inside x n) → ¬p refl}
  -- Resolve CName.
  name? sc p (C.qName x) (C.modl y ss) with x C.≟ y
  name? sc p (C.qName x) (C.modl x ss) | yes!  = yes (Name.modl x)
  name? sc p (C.qName x) (C.modl y ss) | no ¬p = no λ{ (modl x) → ¬p refl }

  lname? : ∀ p xs sc ss → Dec (LName p xs sc ss)
  -- List exhausted
  lname? p xs sc C.dNil         = no λ()
  -- In head?, in tail?
  lname? p xs sc (C.dSnoc ss s) with name? (ss ∷ sc) p xs s | lname? p xs sc ss
  lname? p xs sc (C.dSnoc ss s) | yes n | _     = yes (here n)  -- Bias: later decls overwrite earlier ones.
  lname? p xs sc (C.dSnoc ss s) | no _  | yes m = yes (there m)
  lname? p xs sc (C.dSnoc ss s) | no ¬n | no ¬m = no λ where
    (here n) → ¬n n
    (there m) → ¬m m

  sname? : ∀ p xs sc → Dec (SName p xs sc)
  -- List exhausted
  sname? p xs []        = no λ()
  -- In head?, in tail?
  sname? p xs (ss ∷ sc) with lname? p xs sc ss | sname? p xs sc
  ... | yes n | _     = yes (site n)   -- Bias: Inner scopes take precedence!
  ... | no ¬n | yes m = yes (parent m)
  ... | no ¬n | no ¬m = no λ where
    (site  n) → ¬n n
    (parent m) → ¬m m

-- Looking up all possible resolutions of a name (not respecting shadowing).

mutual
  lookupAll : ∀ sc p xs s → Enumeration (Name sc p xs s)
  -- C.ref does not declare a name.
  lookupAll sc p xs (C.opn q C.importNothing)    = emptyEnum λ()
  -- Step inside private blocks.
  lookupAll sc publ xs (C.priv ss) = emptyEnum λ()
  lookupAll sc priv xs (C.priv ss) = mapEnum inpriv surj-inpriv (llookupAll priv xs sc ss)
  -- Resolve qualification.
  lookupAll sc p (C.qual x xs) (C.modl y ss) with x C.≟ y | llookupAll publ xs sc ss
  lookupAll sc p (C.qual x xs) (C.modl x ss) | yes!  | e = mapEnum (inside x) surj-inside e
  lookupAll sc p (C.qual x xs) (C.modl y ss) | no ¬p | _ = emptyEnum λ{ (inside x n) → ¬p refl }
  -- Resolve CName.
  lookupAll sc p (C.qName x) (C.modl y ss) with x C.≟ y
  lookupAll sc p (C.qName x) (C.modl x ss) | yes!  = enum (modl x ∷ []) λ{ (modl x) → here! }
  lookupAll sc p (C.qName x) (C.modl y ss) | no ¬p = emptyEnum λ{ (modl x) → ¬p refl }

  llookupAll : ∀ p xs sc ss → Enumeration (LName p xs sc ss)
  -- List exhausted
  llookupAll p xs sc C.dNil = emptyEnum λ()
  -- In head?, in tail?
  llookupAll p xs sc (C.dSnoc ss s) with lookupAll (ss ∷ sc) p xs s | llookupAll p xs sc ss
  llookupAll p xs sc (C.dSnoc ss s) | e | e' = appendEnum here there lname-surjective e e'

  slookupAll : ∀ p xs sc → Enumeration (SName p xs sc)
  -- List exhausted
  slookupAll p xs [] = emptyEnum λ()
  -- In head?, in tail?
  slookupAll p xs (ss ∷ sc) with llookupAll p xs sc ss | slookupAll p xs sc
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
  lookup : ∀ sc p xs s → List (Name sc p xs s)
  -- C.ref does not declare a name.
  lookup sc p xs (C.opn q C.importNothing)    = []
  -- Step inside private blocks.
  lookup sc publ xs (C.priv ss) = []
  lookup sc priv xs (C.priv ss) = map inpriv (llookup priv xs sc ss)
  -- Resolve qualification.
  lookup sc p (C.qual x xs) (C.modl y ss) with x C.≟ y | llookup publ xs sc ss
  lookup sc p (C.qual x xs) (C.modl x ss) | yes!  | ns = map (inside x) ns
  lookup sc p (C.qual x xs) (C.modl y ss) | no ¬p | _  = []
  -- Resolve CName.
  lookup sc p (C.qName x) (C.modl y ss) with x C.≟ y
  lookup sc p (C.qName x) (C.modl x ss) | yes!  = modl x ∷ []
  lookup sc p (C.qName x) (C.modl y ss) | no ¬p = []

  llookup : ∀ p xs sc ss → List (LName p xs sc ss)
  -- List exhausted
  llookup p xs sc C.dNil = []
  -- In head?, in tail?
  llookup p xs sc (C.dSnoc ss s) with lookup (ss ∷ sc) p xs s | llookup p xs sc ss
  llookup p xs sc (C.dSnoc ss s) | ns | ns' = map here ns ++ map there ns'  -- no shadowing of siblings!

  slookup : ∀ p xs sc → List (SName p xs sc)
  -- List exhausted
  slookup p xs [] = []
  -- In head?, in tail?
  slookup p xs (ss ∷ sc) with llookup p xs sc ss | slookup p xs sc
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

  clookup : ∀ (τ : sc ⊆ sc') p xs s
    → (List (Name sc p xs s) → List (SName p' xs' sc'))
    → List (SName p' xs' sc')
    → List (SName p' xs' sc')
  -- C.ref does not declare a name.
  clookup τ p xs (C.opn q C.importNothing) f ns = ns
  -- Step inside private blocks.
  clookup τ publ xs (C.priv _ ) f ns = ns
  clookup τ priv xs (C.priv ps) f ns = lclookup τ priv xs ps (f ∘ map inpriv) ns
  -- Resolve CName.
  clookup τ p (C.qName x) (C.modl y ss) f ns with x C.≟ y
  clookup τ p (C.qName x) (C.modl x ss) f ns | yes!  = f (modl x ∷ [])
  clookup τ p (C.qName x) (C.modl y ss) f ns | no _  = ns
  -- Resolve qualification.
  clookup τ p (C.qual x xs) (C.modl y ss) f ns with x C.≟ y
  -- When we step into a module, we discard the alternatives!  No backtracking here!
  clookup τ p (C.qual x xs) (C.modl x ss) f ns | yes!  = lclookup τ publ xs ss (f ∘ map (inside x)) []
  clookup τ p (C.qual x xs) (C.modl y ss) f ns | no _  = ns

  -- Lookup in a list of declarations

  lclookup : ∀ (τ : sc ⊆ sc') p xs ss
    → (List (LName p xs sc ss) → List (SName p' xs' sc'))
    → List (SName p' xs' sc')
    → List (SName p' xs' sc')
  -- List exhausted
  lclookup τ p xs C.dNil         f ns = ns
  -- In head?, in tail?
  lclookup τ p xs (C.dSnoc ss s) f ns = clookup τ p xs s (λ ns → f (map (here ∘ wk1Name) ns) ++ ns') ns'
    where
    -- The fallback ns' is also propagated to the successful case.
    -- No shadowing of siblings!
    ns' = lclookup τ p xs ss (f ∘ map there) ns

  -- Lookup in the scope

  sclookup : ∀ p xs sc → List (SName p xs sc)
  -- List exhausted
  sclookup p xs [] = []
  -- In head?, in tail?
  sclookup p xs (ss ∷ sc) = lclookup (_ ∷ʳ ⊆-refl) p xs ss (map site) (map parent (sclookup p xs sc))
    -- only keep parent alternatives when current site does not resolve the name
    -- discard parent occurrences if current site has one

-- Well-scoped declarations

mutual

  data Decl (sc : Scope) : C.Decl → Set where
    modl : ∀ x  (ds : Decls sc ss) → Decl sc (C.modl x ss)
    ref  : (n  : SName priv xs sc) → Decl sc (C.opn xs C.importNothing)
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
  sSnoc : ∀{sc ss} (wsc : WScope sc) (ds : Decls sc ss) → WScope (ss ∷ sc)

-- Well-formed module

data Module : C.Name → Scope → Set where
  modl : (n : SName priv (C.qName x) sc) (ds : Decls sc ss) → Module x sc


-- This needs weakening:

-- mutual

--   llookupModule : (x : C.Name) (ds : Decls sc ss) → List (Module x sc)
--   llookupModule x ds = {!!}

-- slookupModule : (x : C.Name) (wsc : WScope sc) → List (Module x sc)
-- slookupModule x sNil = []
-- slookupModule x (sSnoc wsc ds) = {!llookupModule x ds!}


-- -}
-- -}
-- -}
-- -}
