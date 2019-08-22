module AST.GHC.Types where

import Data.String as DS
open import Data.Nat
open import Data.Float as DF
open import Data.Char
open import Data.List


Array = List ℕ

postulate
  Int : Set
  Int32 : Set
  Word : Set
  Word64 : Set
  Maybe : Set -> Set


String = List Char

{-# FOREIGN GHC import Data.Int #-}
{-# FOREIGN GHC import Data.Word #-}
{-# FOREIGN GHC import qualified Data.Maybe as DMM #-}

{-# COMPILE GHC Int = type Int #-}
{-# COMPILE GHC Int32 = type Int32 #-}
{-# COMPILE GHC Word = type Word #-}
{-# COMPILE GHC Word64 = type Word64 #-}
{-# COMPILE GHC Maybe = type DMM.Maybe #-}

Integer = ℕ

Double = DF.Float

Text = DS.String

data _×P_ (A B : Set) : Set where
  _,P_ : A -> B -> A ×P B

msnd : {A B : Set} -> A ×P B -> B
msnd (x ,P x₁) = x₁

postulate
  Sett : Set -> Set

{-# FOREIGN GHC import Data.Set #-}
{-# COMPILE GHC Sett = type Set #-}


{-# COMPILE GHC _×P_ = data (,) ((,)) #-}



