module AST.Data.Strict.Maybe where

postulate
  Maybe : Set -> Set

{-# FOREIGN GHC import qualified Data.Strict.Maybe as DSM #-}

{-# COMPILE GHC Maybe = type DSM.Maybe #-}

 
