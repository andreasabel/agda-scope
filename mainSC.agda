module mainSC where

open import AST.Agda.Syntax.Concrete
open import AST.Agda.Utils.FileName
open import AST.GHC.Types hiding (String)


open import Data.List
open import Data.String as DS
open import Data.Bool
open import Data.Unit
open import ExtraLibs.Library

Module : Set
Module = (List Pragma) ×P (List Declaration)


postulate
  readFile        : String → IO String
  -- parseFile       : String → AbsolutePath
  moduleParserEx  : String → String → IO Module
  mtst1           : List Declaration -> IO String

{-# FOREIGN GHC import System.IO #-}
{-# FOREIGN GHC import Data.Text #-}
{-# COMPILE GHC readFile = (fmap Data.Text.pack) . System.IO.readFile . Data.Text.unpack #-}

{-# FOREIGN GHC import HaskellHelper.ParseAST #-}
{-# COMPILE GHC moduleParserEx =  \ x y -> HaskellHelper.ParseAST.moduleParserEx (Data.Text.unpack x) (Data.Text.unpack y)  #-}
{-# COMPILE GHC mtst1 = HaskellHelper.ParseAST.mtst1  #-}





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
-- {-# FOREIGN GHC import GHC♖GHC♝Types.Int32.Show #-}
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
  modu <- moduleParserEx path fileContent
  ff <- mtst1 (msnd modu)
  putStrLn ff
  putStrLn "loaded"
  where open IOMonad
