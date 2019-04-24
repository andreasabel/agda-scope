module Parser where

open import Agda.Builtin.Char   using (Char)
open import Agda.Builtin.List   using (List)
open import Agda.Builtin.String using (String)

open import ModuleCalculus.AST using (Program)

{-# FOREIGN GHC import qualified Data.Text  #-}

{-# FOREIGN GHC import ModuleCalculus.Abs  (Program)           #-}
{-# FOREIGN GHC import ModuleCalculus.ErrM (Err (..))          #-}
{-# FOREIGN GHC import ModuleCalculus.Par  (myLexer, pProgram) #-}

-- Error monad of BNFC

data Err (A : Set) : Set where
  ok   : A → Err A
  bad  : List Char → Err A

{-# COMPILE GHC Err = data Err ( Ok | Bad ) #-}

postulate
  parse : String → Err Program

{-# COMPILE GHC parse = pProgram . myLexer . Data.Text.unpack #-}
