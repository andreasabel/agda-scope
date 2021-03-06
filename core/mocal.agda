
module mocal where

open import Library
open import ModuleCalculus.AST    using (Program; printProgram; printDecl)
open import ModuleCalculus.Parser using (Err; ok; bad; parseProgram)
open import ParsedToConcrete      using (unsupported; p→c; c→p)
open import ScopeChecker          using (checkDecl)
open import AbstractToConcrete    using (a→c-Decl)

-- open import TypeChecker using (printError; module CheckProgram)
-- open import Interpreter using (runProgram)

check : String → IO ⊤
check contents = do
  Err.ok program ← return $ parseProgram contents where
    (bad cs) → do
      putStrLn "SYNTAX ERROR"
      putStrLn (String.fromList cs)
      exitFailure
  inj₂ cdecl ← return $ p→c program where
    (inj₁ unsupported) → do
      putStrLn "ERROR: UNSUPPORTED SYNTAX"
      putStrLn (printProgram program)
      exitFailure
  inj₂ (sk , adecl) ← return $ checkDecl cdecl [] where
    (inj₁ scoperr) → do
      putStrLn "SCOPE ERROR"
      putStrLn (printDecl (c→p cdecl))
      exitFailure
  putStrLn "SUCCESS"
  putStrLn (printDecl (c→p (a→c-Decl adecl)))

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
