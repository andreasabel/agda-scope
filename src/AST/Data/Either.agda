module AST.Data.Either where

mutual
  data Either ( a b : Set ) : Set where
    LeftC : a → Either a b
    RightC : b → Either a b

{-# FOREIGN GHC import Data.Either #-}

{-# COMPILE GHC Either = data Either ( Left | Right ) #-}

 
