
import System.Environment (getArgs)
import System.Exit        (exitFailure)

import HierMod.Abs        (Program)
import HierMod.Par        (pProgram, myLexer)
import HierMod.ErrM
import HierMod.Layout     (resolveLayout)

import ScopeChecker       (checkProgram)

-- | Main: read file passed by only command line argument,
--   parse and scope check.

main :: IO ()
main = do
  args <- getArgs
  case args of
    [file] -> readFile file >>= parse >>= check
    _      -> do
      putStrLn "Usage: Main <SourceFile>"
      exitFailure

-- | Parse, file contents.

parse :: String -> IO Program
parse s = do
  case pProgram (resolveLayout True $ myLexer s) of
    Bad err  -> do
      putStrLn "SYNTAX ERROR"
      putStrLn err
      exitFailure
    Ok  prg -> return prg

-- | Scope check.

check :: Program -> IO ()
check prg = do
  case checkProgram prg of
    Left err -> do
      putStrLn "SCOPE ERROR"
      print err
      exitFailure
    Right sig -> do
      putStrLn "SUCCESS"
      print sig
