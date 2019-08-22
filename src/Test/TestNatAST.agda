module TestNatAST where

data MNat : Set where
  MZ : MNat
  MS : MNat -> MNat



module mod2 where
  data MMay (A : Set) : Set where
    MNot : MMay A
    MJus : A -> MMay A
