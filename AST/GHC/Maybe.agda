module AST.GHC.Maybe where

postulate
  Maybe : Set -> Set

{-# FOREIGN GHC import qualified Data.Maybe as DMM #-}

{-# COMPILE GHC Maybe = type DMM.Maybe #-}



