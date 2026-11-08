import Mettapedia.GSLT.Parsing.PresentationWire

/-!
# Checked results from the native ParserPack backend

Each finite certificate is replayed against the original expression
presentation and source, so neither its endpoint nor its syntax value is
accepted on the native process's word. A command-stream presentation can
consume an ignored suffix while retaining the command node's exact span.
Native rejection/completeness remains a separate backend boundary.
-/

namespace Mettapedia.GSLT.Parsing.PresentationNative

open _root_.Lean
open LanguageDefSyntaxCompiler PresentationExprSemantics ParserProfileSemantics

structure Config where
  script : System.FilePath
  library : System.FilePath
  tools : System.FilePath
  work : System.FilePath
  backend : String
  workLimit : Nat
  replayDepth : Nat
  resultLimit : Nat

structure Candidate where
  stop : Nat
  output : List CST
  deriving Repr

def run (config : Config) (query : String) (presentation : Presentation) (profile : ParserProfileLayer)
    (root : String) (input : String) : IO (Array Candidate) := do
  let directory := config.work / query
  if ← directory.pathExists then throw (IO.userError "native parser query directory already exists")
  IO.FS.createDirAll directory
  IO.FS.writeFile (directory / "grammar.json") ((PresentationWire.encode presentation profile root).compress ++ "\n")
  IO.FS.writeFile (directory / "input.lean") input
  let process ← IO.Process.output {
    cmd := "python3"
    args := #[config.script.toString, "--library", config.library.toString,
      "--cetta-tools", config.tools.toString, "--grammar", (directory / "grammar.json").toString,
      "--input", (directory / "input.lean").toString, "--work-dir", directory.toString,
      "--backend", config.backend, "--work-limit", toString config.workLimit,
      "--replay-depth", toString config.replayDepth, "--result-limit", toString config.resultLimit] }
  unless process.exitCode == 0 do
    throw (IO.userError ("native parser execution failed: " ++ process.stderr ++ process.stdout))
  let encoded ← IO.FS.readFile (directory / "certificates.json")
  let json ← IO.ofExcept (Json.parse encoded)
  let rows ← IO.ofExcept json.getArr?
  let inputScalars := input.toList.map Char.toNat
  let mut results := #[]
  for raw in rows do
    let certificate ← IO.ofExcept (PresentationWire.certificate (encoded.length + 1) raw)
    let some (stop, output) := PresentationReplay.observe (PresentationWire.classTest profile)
        presentation inputScalars (.ref root) certificate 0
      | throw (IO.userError "native derivation did not replay in the source presentation")
    unless stop == inputScalars.length do throw (IO.userError "native result did not consume the supplied source")
    results := results.push ⟨stop, output⟩
  return results

end Mettapedia.GSLT.Parsing.PresentationNative
