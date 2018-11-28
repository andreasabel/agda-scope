module AST.DataStrictMaybe where

mutual
  data Maybe ( a : Set ) : Set where
    NothingC : Maybe a
    JustC : a → Maybe a

{-# COMPILE GHC Maybe = data Maybe ( NothingC | JustC ) #-}

 
