-- File generated by the BNF Converter (bnfc 2.9.5).

-- Basic I/O library.

module HierMod.IOLib where

open import Agda.Builtin.IO     public using (IO)
open import Agda.Builtin.List   public using (List; []; _∷_)
open import Agda.Builtin.String public using (String)
  renaming (primStringFromList to stringFromList)
open import Agda.Builtin.Unit   public using (⊤)

-- I/O monad.

postulate
  return : ∀ {a} {A : Set a} → A → IO A
  _>>=_  : ∀ {a b} {A : Set a} {B : Set b} → IO A → (A → IO B) → IO B

{-# COMPILE GHC return = \ _ _ -> return    #-}
{-# COMPILE GHC _>>=_  = \ _ _ _ _ -> (>>=) #-}

infixl 1 _>>=_ _>>_

_>>_  : ∀ {b} {B : Set b} → IO ⊤ → IO B → IO B
_>>_ = λ m m' → m >>= λ _ → m'

-- Co-bind and functoriality.

infixr 1 _=<<_ _<$>_

_=<<_  : ∀ {a b} {A : Set a} {B : Set b} → (A → IO B) → IO A → IO B
k =<< m = m >>= k

_<$>_  : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → IO A → IO B
f <$> m = do
  a ← m
  return (f a)

-- Binding basic I/O functionality.

{-# FOREIGN GHC import qualified Data.Text #-}
{-# FOREIGN GHC import qualified Data.Text.IO #-}
{-# FOREIGN GHC import qualified System.Exit #-}
{-# FOREIGN GHC import qualified System.Environment #-}
{-# FOREIGN GHC import qualified System.IO #-}

postulate
  exitFailure    : ∀{a} {A : Set a} → IO A
  getArgs        : IO (List String)
  putStrLn       : String → IO ⊤
  readFiniteFile : String → IO String

{-# COMPILE GHC exitFailure    = \ _ _ -> System.Exit.exitFailure #-}
{-# COMPILE GHC getArgs        = fmap (map Data.Text.pack) System.Environment.getArgs #-}
{-# COMPILE GHC putStrLn       = System.IO.putStrLn . Data.Text.unpack #-}
{-# COMPILE GHC readFiniteFile = Data.Text.IO.readFile . Data.Text.unpack #-}
