module AST.Data.Sett.Internal where

postulate
  Sett : Set -> Set

{-# FOREIGN GHC import Data.Set #-}
{-# COMPILE GHC Sett = type Set #-}
-- open import AST.GHC.Types
-- mutual
--   data Sett ( a : Set ) : Set where
--     BinC : Size → a → (Sett  a) → (Sett  a) → Sett a
--     TipC : Sett a
  
--   Size :  Set
--   Size  = Int

-- {-# FOREIGN GHC import Data.Set.Internal #-}

-- {-# COMPILE GHC Sett = data Sett ( Bin | Tip ) #-}

 
