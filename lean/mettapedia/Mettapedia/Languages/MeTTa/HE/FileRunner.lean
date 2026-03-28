import Algorithms.MeTTa.Simple.Session
import Algorithms.MeTTa.Simple.RuntimeProfile

/-!
# LeanHE Real-File Runner

This module gives the mettapedia-side HE stack an honest `.metta` file runner.
It intentionally reuses the current executable HE session backend from
`algorithms` rather than pretending the fully verified evaluator already owns
raw file execution, module loading, and assertion handling end-to-end.

Positive example:
- `he_a1_symbols.metta`, `he_a3_twoside.metta`,
  `he_b0_chaining_prelim.metta`, and `he_b1_equal_chain.metta` can be run from
  the mettapedia executable now.

Negative example:
- direct/backchain-heavy files such as `he_b2_backchain.metta` are still
  expected to fail today; this runner is for real pressure, not for hiding
  current gaps.
-/

namespace Mettapedia.Languages.MeTTa.HE

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Engine
open MeTTailCore.MeTTaIL.Profile
open Algorithms.MeTTa.Simple

private def emptyLanguage : LanguageDef := {
  name := "MettapediaHERunner"
  types := []
  terms := []
  equations := []
  rewrites := []
  congruenceCollections := []
}

private def emptyBundle : SpecBundle := {
  language := emptyLanguage
  relationEnv := RelationEnv.empty
  builtins := coreIntrinsicBuiltins
  policy := {
    maxFuel := 128
    normalizeToFixedPoint := false
  }
}

private def heBaseSession : Session :=
  Session.withAssertionPolicy
    (Session.withSyntax (Session.new emptyBundle) runtimeProfileHE.syntaxSpec)
    runtimeProfileHE.assertionPolicy

private def defaultHELibPath : IO System.FilePath := do
  match (← IO.getEnv "HE_LIB_FILE") with
  | some p => pure (System.FilePath.mk p)
  | none => pure (System.FilePath.mk "/home/zar/claude/hyperon/PeTTa/lib/lib_he.metta")

private def loadDefaultHELibrary (s : Session) : IO Session := do
  let libPath ← defaultHELibPath
  if !(← libPath.pathExists) then
    pure s
  else
    let libText ← IO.FS.readFile libPath
    pure (Session.loadText s libText)

private def renderPattern (p : Pattern) : String :=
  reprStr p

private def renderPatternList (xs : List Pattern) : String :=
  "[" ++ String.intercalate ", " (xs.map renderPattern) ++ "]"

def runHEFile (path : System.FilePath) : IO (Session × List (Nat × List Pattern)) := do
  let text ← IO.FS.readFile path
  let sess0 ← loadDefaultHELibrary heBaseSession
  pure (Session.runText sess0 text)

def runHEFileDiagnostics (path : System.FilePath) : IO Diagnostics := do
  let (sess, _) ← runHEFile path
  pure (Session.diagnostics sess)

def printHEFileReport (path : System.FilePath)
    (queries : List (Nat × List Pattern))
    (diag : Diagnostics) : IO Unit := do
  IO.println s!"file: {path}"
  for q in queries do
    IO.println s!"line {q.1}: {renderPatternList q.2}"
  IO.println s!"diagnostics: parsed={diag.parsedLines} applied={diag.appliedStmts} eval={diag.evalCalls} errors={diag.errors}"
  if !diag.messages.isEmpty then
    IO.println "messages:"
    for m in diag.messages do
      IO.println s!"  - {m}"

def runHEFileCommand (path : System.FilePath) : IO UInt32 := do
  let (sess, queries) ← runHEFile path
  let diag := Session.diagnostics sess
  printHEFileReport path queries diag
  pure (if diag.errors = 0 then 0 else 2)

def defaultCettaTestDir : IO System.FilePath := do
  match (← IO.getEnv "CETTA_TEST_DIR") with
  | some p => pure (System.FilePath.mk p)
  | none => pure (System.FilePath.mk "/home/zar/claude/c-projects/cetta/tests")

def resolveCoreFile (name : String) : IO System.FilePath := do
  pure ((← defaultCettaTestDir) / name)

end Mettapedia.Languages.MeTTa.HE
