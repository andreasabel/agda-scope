{-# LANGUAGE TemplateHaskell #-}
module ASTMaker where



import Agda.Syntax.Parser
import Agda.Interaction.CommandLine

import Agda.Benchmarking
import Agda.ImpossibleTest
import Agda.Interaction.CommandLine
import Agda.Interaction.FindFile
import Agda.Interaction.Options
import Agda.Interaction.Options.IORefs
import Agda.Interaction.Options.Lenses
import Agda.Interaction.Options.Warnings
import Agda.Syntax.Abstract
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Abstract.Pattern
import Agda.Syntax.Abstract.PatternSynonyms
import Agda.Syntax.Abstract.Pretty
import Agda.Syntax.Abstract.Views
import Agda.Syntax.Common
import Agda.Syntax.Concrete
import Agda.Syntax.Concrete.Attribute
import Agda.Syntax.Concrete.Definitions
import Agda.Syntax.Concrete.Generic
import Agda.Syntax.Concrete.Name
import Agda.Syntax.Concrete.Operators
import Agda.Syntax.Concrete.Operators.Parser
import Agda.Syntax.Concrete.Operators.Parser.Monad
import Agda.Syntax.Concrete.Pattern
import Agda.Syntax.Concrete.Pretty
import Agda.Syntax.DoNotation
import Agda.Syntax.Fixity
import Agda.Syntax.IdiomBrackets
import Agda.Syntax.Info
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Defs
import Agda.Syntax.Internal.Generic
import Agda.Syntax.Internal.Names
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Internal.SanityCheck
import Agda.Syntax.Literal
import Agda.Syntax.Notation
import Agda.Syntax.Parser
import Agda.Syntax.Parser.Alex
import Agda.Syntax.Parser.Comments
import Agda.Syntax.Parser.Layout
import Agda.Syntax.Parser.LexActions
import Agda.Syntax.Parser.Lexer
import Agda.Syntax.Parser.Literate
import Agda.Syntax.Parser.LookAhead
import Agda.Syntax.Parser.Monad
import Agda.Syntax.Parser.Parser
import Agda.Syntax.Parser.StringLiterals
import Agda.Syntax.Parser.Tokens
import Agda.Syntax.Position
import Agda.Syntax.Reflected
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad
import Agda.Syntax.Translation.AbstractToConcrete
import Agda.Syntax.Translation.ReflectedToAbstract
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.DisplayForm
import Agda.TypeChecking.DropArgs
import Agda.TypeChecking.Free
import Agda.TypeChecking.Level
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Benchmark
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.Env
import Agda.TypeChecking.Monad.MetaVars
import Agda.TypeChecking.Monad.Options
import Agda.TypeChecking.Monad.State
import Agda.TypeChecking.Monad.Trace
import Agda.TypeChecking.Patterns.Abstract
import Agda.TypeChecking.Positivity.Occurrence
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Rules.Builtin
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Warnings
import Agda.Utils.AffineHole
import Agda.Utils.AssocList
import Agda.Utils.Char
import Agda.Utils.Either
import Agda.Utils.Empty
import Agda.Utils.Except
import Agda.Utils.FileName
import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.Geniplate
import Agda.Utils.Hash
import Agda.Utils.Impossible
import Agda.Utils.IO.UTF8
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Map
import Agda.Utils.Maybe
import Agda.Utils.Maybe.Strict
import Agda.Utils.Monad
import Agda.Utils.NonemptyList
import Agda.Utils.Null
import Agda.Utils.Parser.MemoisedCPS
import Agda.Utils.PartialOrd
import Agda.Utils.Permutation
import Agda.Utils.POMonoid
import Agda.Utils.Pretty
import Agda.Utils.Singleton
import Agda.Utils.Size
import Agda.Utils.String
import Agda.Utils.Suffix
import Agda.Utils.Three
import Agda.Utils.Trie
import Agda.Utils.Tuple
import Agda.Utils.Update
import Control.Applicative
import Control.Arrow
import Control.DeepSeq
import Control.Exception
import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Except
import Control.Monad.Writer
import Data.Char
import Data.Data
import Data.Either
import Data.Foldable
import Data.Function
import Data.Functor
import Data.Hashable
import Data.Int
import Data.IntSet
import Data.IORef
import Data.List
import Data.Map
import Data.Maybe
import Data.Monoid
import Data.Semigroup
import Data.Sequence
import Data.Set
import Data.Strict.Maybe
import Data.Text
import Data.Text.Lazy
import Data.Traversable
import Data.Void
import Data.Word
import Debug.Trace
import Language.Haskell.TH
import Numeric.IEEE
import Prelude
import System.FilePath
import System.IO.Unsafe
import Text.PrettyPrint
import Text.PrettyPrint.HughesPJ
import Text.Regex.TDFA

import Agda.Utils.FileName

import qualified Data.Text as T

import Control.Monad.Trans.Except
import Control.Monad.State

import Data.Data
import Data.List

import Control.Monad.State

import Language.Haskell.TH

-- import Agda.Syntax.Mtst3
import ASTMakerTH

import qualified Data.Set as DS

-- mprintExpr :: Expr -> String
-- mprintExpr t = error $ show t

-- mprintDecl :: Declaration -> String
-- mprintDecl t = showConstr (toConstr t)

-- mprintModule :: Module -> String
-- mprintModule (pragmas,decls) = show (pragmas,map mprintDecl decls)

main :: IO ()
main = do
  -- putStrLn  $(findImports "Agda.Syntax.Concrete.Declaration"   )
  putStrLn  $(hask2ag'' "Agda.Syntax.Concrete.Declaration"   )
