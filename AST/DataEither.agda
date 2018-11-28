module AST.DataEither where

mutual
  data Either ( a b : Set ) : Set where
    LeftC : a → Either a b
    RightC : b → Either a b

{-# FOREIGN GHC Either = Either ( LeftC | RightC ) #-}

 
