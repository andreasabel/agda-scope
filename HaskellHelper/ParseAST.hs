module HaskellHelper.ParseAST where

import Agda.Syntax.Parser
import Agda.Syntax.Concrete

import Agda.Interaction.CommandLine
import Agda.Utils.FileName

import qualified Data.Text as T

import Control.Monad.Trans.Except
import Control.Monad.State

import Data.Data
import qualified Data.Text as DT
import Data.List

import Control.Monad.State

import Language.Haskell.TH

-- import Agda.Syntax.Mtst3

import qualified Data.Set as DS

-- import Agda.Syntax.Mtst5


-- mprintExpr :: Expr -> String
-- mprintExpr t = error $ show t

-- mprintDecl :: Declaration -> String
-- mprintDecl t = showConstr (toConstr t)

-- mprintModule :: Module -> String
-- mprintModule (pragmas,decls) = show (pragmas,map mprintDecl decls)

moduleParserEx :: String -> String -> IO Module
moduleParserEx path cont = do
  let w = parseFile moduleParser (AbsolutePath $ T.pack path) cont
  (Right (modu@(pragmas,decls),_),_) <- flip runStateT [] $ runExceptT $ unPM w
  return modu


mtst1 :: [Declaration] -> IO DT.Text
mtst1 x = do
  return $ DT.pack $ show $ length x









