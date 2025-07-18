-- Imports from the standard library

module Library where

open import Effect.Functor                        public using (RawFunctor)
open import Effect.Applicative                    public using (RawApplicative)
open import Effect.Monad                          public using (RawMonad) -- ; return; _>>=_)

open import Data.Unit.Base                        public using (⊤)
open import Data.Product.Base                     public using (Σ; ∃; _×_; _,_; proj₁; proj₂; map₁; map₂) renaming (map to bimap)

open import Data.Empty                            public using (⊥; ⊥-elim)
open import Data.Sum.Base                         public using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Sum.Effectful.Left               public using (functor; applicative; monad)

open import Data.Bool.Base                        public using (Bool; true; false)
open import Data.String                           public using (String; _≟_)

open import Data.List.Base                        public using (List; []; _∷_; _++_)
open import Data.List.Effectful                   public using (module TraversableM)
open import Data.List.Membership.Propositional    public using (_∈_)
open import Data.List.Membership.Propositional.Properties
                                                  public using (∈-map⁺; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any          public using (Any; here; there)
open import Data.List.Relation.Binary.Sublist.Propositional
                                                  public using (_⊆_; []; _∷_; _∷ʳ_; ⊆-refl; ⊆-trans)
open import Data.List.Relation.Binary.Sublist.Propositional.Properties
                                                  public using ()

open import Data.List.NonEmpty                    public using (List⁺; _∷_; _∷⁺_)
open import Data.Maybe.Base                       public using (Maybe; nothing; just)

open import Function                              public using (id; _∘_; _∘′_; _$_; case_of_)
open import Level                                 public using (_⊔_)

open import Relation.Binary.PropositionalEquality as Eq
                                                  public using (_≡_; refl)
open import Relation.Nullary                      public using (Dec; ¬_) hiding (module Dec)

open import IO.Primitive.Core                     public using (IO)

-- Injective functions

Injective : ∀{a b}{A : Set a}{B : Set b} (f : A → B) → Set _
Injective f = ∀{x y} → f x ≡ f y → x ≡ y

Surjective : ∀{a b}{A : Set a}{B : Set b} (f : A → B) → Set _
Surjective f = ∀ y → ∃ λ x → f x ≡ y

private
  here-there-surjective : ∀{a p}{A : Set a} {P : A → Set p}
    → {x : A} {xs : List A}
    → Surjective {B = Any P (x ∷ xs)} [ here , there ]′
  here-there-surjective (here  px)  = inj₁ px  , refl
  here-there-surjective (there pxs) = inj₂ pxs , refl

-- Utilities

module Dec where
  open        Relation.Nullary           public using (yes; no)
  open import Relation.Nullary.Decidable using (map′)

  module _ {a b} {A : Set a}{B : Set b} {f : A → B} where

    map : Surjective f → Dec A → Dec B
    map surj = map′ f (proj₁ ∘ surj)

    module _ (inj : Injective f) where

      cong : ∀{x y} → Dec (x ≡ y) → Dec (f x ≡ f y)
      cong = map′ (Eq.cong f) inj

      cong⁻¹ : ∀{x y} → Dec (f x ≡ f y) → Dec (x ≡ y)
      cong⁻¹ = map′ inj (Eq.cong f)

pattern here! = here refl
pattern yes!  = Dec.yes refl

module String where
  open import Data.String.Base public
  open import Data.String.Properties public
    using    ()
    renaming (<-strictTotalOrder-≈ to strictTotalOrder)

-- import map after defining Dec.map
open Data.List.Base public using (map)

-- Has A B similar to Dec (Σ A B)

module Has where
  data Has {a} {b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
    yes : {a : A} → B a → Has A B
    no' : ¬ A → Has A B
    no  : ({a : A} → ¬ B a) → Has A B

-- Enumerate a type

Enumerates : ∀{a}{A : Set a} → List A → Set a
Enumerates xs = ∀ x → x ∈ xs

record Enumeration {a} (A : Set a) : Set a where
  constructor enum
  field
    enumeration : List A
    enumerates  : Enumerates enumeration

emptyEnum : ∀{a}{A : Set a} → ¬ A → Enumeration A
emptyEnum ¬a = enum [] (⊥-elim ∘ ¬a)

mapEnum : ∀ {a b} {A : Set a} {B : Set b}
  (f : A → B) (inj : Surjective f)
  → Enumeration A → Enumeration B
mapEnum f surj (enum xs p) = enum (map f xs) enumerates
  where
  enumerates : ∀ y → y ∈ map f xs
  enumerates y with surj y
  enumerates .(f x) | x , refl = ∈-map⁺ f (p x)

appendEnum : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
  → (f : A → C) (g : B → C) (surj : Surjective [ f , g ]′)
  → Enumeration A → Enumeration B → Enumeration C
appendEnum f g surj (enum as p) (enum bs q) =
  enum (map f as ++ map g bs) enumerates
  where
  enumerates : ∀ z → z ∈ map f as ++ map g bs
  enumerates z with surj z
  enumerates .(f x) | (inj₁ x , refl) = ∈-++⁺ˡ (∈-map⁺ f (p x))
  enumerates .(g y) | (inj₂ y , refl) = ∈-++⁺ʳ _ (∈-map⁺ g (q y))

-- H-propositions (uniquely inhabited (if any) sets)

Unique : ∀ {a} (A : Set a) → Set a
Unique A = ∀ (x y : A) → x ≡ y

-- I/O

liftM2 : ∀{a} {M : Set a → Set a} {{app : RawApplicative M}}
         {A B C : Set a} (f : A → B → C) (ma : M A) (mb : M B) → M C
liftM2 {{app}} f ma mb = zipWith f ma mb
  where open RawApplicative app

module IOMonad where
  open import IO.Primitive.Core public using (return; _>>=_)

  infixl 1 _>>_

  _>>_  : ∀ {b} {B : Set b} → IO ⊤ → IO B → IO B
  _>>_ = λ m m' → m >>= λ _ → m'

  infixr 1 _=<<_

  _=<<_  : ∀ {a b} {A : Set a} {B : Set b} → (A → IO B) → IO A → IO B
  k =<< m = m >>= k

{-# FOREIGN GHC import qualified Data.Text #-}
{-# FOREIGN GHC import qualified Data.Text.IO #-}
{-# FOREIGN GHC import qualified System.Exit #-}
{-# FOREIGN GHC import qualified System.Environment #-}
{-# FOREIGN GHC import qualified System.IO #-}

-- Binding more Haskell functions

postulate
  exitFailure    : ∀{a} {A : Set a} → IO A
  getArgs        : IO (List String)
  putStrLn       : String → IO ⊤
  readFiniteFile : String → IO String

{-# COMPILE GHC exitFailure    = \ _ _ -> System.Exit.exitFailure #-}
{-# COMPILE GHC getArgs        = map Data.Text.pack <$> System.Environment.getArgs #-}
{-# COMPILE GHC putStrLn       = System.IO.putStrLn . Data.Text.unpack #-}
{-# COMPILE GHC readFiniteFile = Data.Text.IO.readFile . Data.Text.unpack #-}
