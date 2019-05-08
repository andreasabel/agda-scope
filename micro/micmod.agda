
module micmod where

open import Library
open import HierMod.AST    using (Program; printProgram; printDecl)
open import HierMod.Parser using (Err; ok; bad; parseProgram)
open import ScopeChecker   using (checkProgram; printScopeError)

check : String → IO ⊤
check contents = do
  Err.ok cprg ← return $ parseProgram contents where
    (bad cs) → do
      putStrLn "SYNTAX ERROR"
      putStrLn (String.fromList cs)
      exitFailure
  inj₂ aprg ← return $ checkProgram cprg where
    (inj₁ scoperr) → do
      putStrLn ("SCOPE ERROR: " String.++ printScopeError scoperr)
      putStrLn (printProgram cprg)
      exitFailure
  putStrLn "SUCCESS"
  putStrLn (printProgram cprg)

  where
  open IOMonad

-- Display usage information and exit

usage : IO ⊤
usage = do
  putStrLn "Usage: micmod <SourceFile>"
  exitFailure
  where open IOMonad

-- Parse command line argument and pass file contents to check.

main : IO ⊤
main = do
  file ∷ [] ← getArgs where _ → usage
  check =<< readFiniteFile file
  where open IOMonad
