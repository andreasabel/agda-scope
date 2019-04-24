
module mocal where

open import Library
open import ModuleCalculus.AST    using (Program; printProgram)
open import ModuleCalculus.Parser using (Err; ok; bad; parseProgram)
-- open import TypeChecker using (printError; module CheckProgram)
-- open import Interpreter using (runProgram)

-- -- Other modules, not used here.
-- import Value
-- import Evaluation
-- import FlowChart

check : String → IO ⊤
check contents = do
  case parseProgram contents of λ where
    (bad cs) → do
      putStrLn "SYNTAX ERROR"
      putStrLn (String.fromList cs)
      exitFailure
    (Err.ok program) → do
          putStrLn (printProgram program)
  --     case checkProgram prg of λ where
  --       (fail err) → do
  --         putStrLn "TYPE ERROR"
  --         putStrLn (printProgram prg)
  --         putStrLn "The type error is:"
  --         putStrLn (printError err)
  --         exitFailure
  --       (ErrorMonad.ok (Σ , prg')) → do
  --         runProgram prg'

  where
  open IOMonad
  -- open CheckProgram using (checkProgram)
  -- open ErrorMonad using (fail; ok)

-- Display usage information and exit

usage : IO ⊤
usage = do
  putStrLn "Usage: mocal <SourceFile>"
  exitFailure
  where open IOMonad

-- Parse command line argument and pass file contents to check.

mocal : IO ⊤
mocal = do
  file ∷ [] ← getArgs where _ → usage
  check =<< readFiniteFile file
  where open IOMonad

main = mocal
