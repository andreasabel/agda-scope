-- Imports from the standard library

module Library where

open import Category.Functor                      public using (RawFunctor)
open import Category.Applicative                  public using (RawApplicative)
open import Category.Monad                        public using (RawMonad) -- ; return; _>>=_)

open import Data.Unit                             public using (⊤)
open import Data.Product                          public using (∃; _,_; proj₁; proj₂)

open import Data.Sum                              public using (_⊎_; inj₁; inj₂)
open import Data.Sum.Categorical.Left             public using (functor; applicative; monad)

open import Data.Bool                             public using (Bool; true; false)
open import Data.String                           public using (String; _≟_)

open import Data.List.Base                        public using (List; []; _∷_; map)
open import Data.List.Membership.Propositional    public using (_∈_)
open import Data.List.Relation.Unary.Any          public using (here; there)
open import Data.List.Categorical                 public using (mapM)

open import Data.List.NonEmpty                    public using (List⁺; _∷_; _∷⁺_)

open import Function                              public using (id; _∘_; _∘′_; _$_; case_of_)

open import Relation.Nullary                      public using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality public using (_≡_; refl; cong)

open import IO.Primitive      public using (IO)

-- Utilities

pattern here! = here refl
pattern yes!  = yes  refl

liftM2 : ∀{a} {M : Set a → Set a} {{app : RawApplicative M}}
         {A B C : Set a} (f : A → B → C) (ma : M A) (mb : M B) → M C
liftM2 {{app}} f ma mb = zipWith f ma mb
  where open RawApplicative app

module String where
  open import Data.String.Base public

module IOMonad where
  open import IO.Primitive public using (return; _>>=_)

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
