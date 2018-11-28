module AST.AgdaTypeCheckingPositivityOccurrence where

mutual
  data Occurrence : Set where
    MixedC : Occurrence 
    JustNegC : Occurrence 
    JustPosC : Occurrence 
    StrictPosC : Occurrence 
    GuardPosC : Occurrence 
    UnusedC : Occurrence 

{-# FOREIGN GHC Occurrence = Occurrence ( MixedC | JustNegC | JustPosC | StrictPosC | GuardPosC | UnusedC ) #-}

 
