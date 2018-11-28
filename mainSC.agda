module mainSC where

open import AST.AgdaSyntaxConcrete
open import AST.AgdaUtilsFileName


open import Data.List
open import Data.String
open import Data.Bool
open import Data.Unit
open import ExtraLibs.Library



postulate
  readFile        : String → IO String
  parseFile       : String → AbsolutePath

{-# FOREIGN GHC import System.IO #-}
{-# FOREIGN GHC import Data.Text #-}
{-# COMPILE GHC readFile = (fmap Data.Text.pack) . System.IO.readFile . Data.Text.unpack #-}


usage : IO ⊤
usage = do
  putStrLn "Usage: lab2 <SourceFile>"
  exitFailure
  where open IOMonad

-- let w = parseFile moduleParser (AbsolutePath $ T.pack path) cont 
-- (Right (modu@(pragmas,decls),_),_) <- flip runStateT [] $ runExceptT $ unPM w
-- putStrLn $ show (decls)

-- postulate
--   moduleParser : (Parser  Module)
--   parseFile : (Parser  a) → AbsolutePath → String → (PM  (a ×  FileType))
--   unPM : (PM  a) → (ExceptT  ParseError (StateT  (List (ParseWarning)) IO) a)
--   flip : a → b → c → b → a → c
--   show : a → String
--   putStrLn : String → (IO  ⊥)
--   readFile : FilePath → (IO  String)
--   pack : String → Text
--   runExceptT : (ExceptT  e m a) → (m  (Either  e a))
--   runStateT : (StateT  s m a) → s → (m  (a ×  s))

-- {-# FOREIGN GHC import Agda.Syntax.Parser #-}
-- {-# FOREIGN GHC import Control.Monad.Trans.Except #-}
-- {-# FOREIGN GHC import Control.Monad.Trans.State.Lazy #-}
-- {-# FOREIGN GHC import Data.Text #-}
-- {-# FOREIGN GHC import GHC.Base #-}
-- {-# FOREIGN GHC import GHC.Show #-}
-- {-# FOREIGN GHC import System.IO #-}

-- {-# COMPILE GHC moduleParser = Agda.Syntax.Parser.moduleParser #-}
-- {-# COMPILE GHC parseFile = Agda.Syntax.Parser.parseFile #-}
-- {-# COMPILE GHC unPM = Agda.Syntax.Parser.unPM #-}
-- {-# COMPILE GHC flip = GHC.Base.flip #-}
-- {-# COMPILE GHC show = GHC.Show.show #-}
-- {-# COMPILE GHC putStrLn = System.IO.putStrLn #-}
-- {-# COMPILE GHC readFile = System.IO.readFile #-}
-- {-# COMPILE GHC pack = Data.Text.pack #-}
-- {-# COMPILE GHC runExceptT = Control.Monad.Trans.Except.runExceptT #-}
-- {-# COMPILE GHC runStateT = Control.Monad.Trans.State.Lazy.runStateT #-}



main : IO ⊤
main = do
  path ∷ [] ← getArgs where _ → usage
  fileContent <- readFile path
  putStrLn fileContent
  where open IOMonad
