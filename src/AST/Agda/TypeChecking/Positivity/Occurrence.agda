module AST.Agda.TypeChecking.Positivity.Occurrence where

mutual
  data Occurrence : Set where
    MixedC : Occurrence 
    JustNegC : Occurrence 
    JustPosC : Occurrence 
    StrictPosC : Occurrence 
    GuardPosC : Occurrence 
    UnusedC : Occurrence 

{-# FOREIGN GHC import Agda.TypeChecking.Positivity.Occurrence #-}

{-# COMPILE GHC Occurrence = data Occurrence ( Mixed | JustNeg | JustPos | StrictPos | GuardPos | Unused ) #-}

 
