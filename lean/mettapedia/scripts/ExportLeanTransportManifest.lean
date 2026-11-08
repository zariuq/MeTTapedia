import Mettapedia.Languages.Lean.Declarations.Manifest
import Mettapedia.Languages.Lean.Declarations.TargetEnvironment

/-!
Export or check the roots and reconstruction-dependency manifest of the
functional-correspondence development. `LEAN_TRANSPORT_CHECK=1` compares a
fresh inventory without changing artifacts. `LEAN_TRANSPORT_ROOTS` selects
an existing roots file; without it, all non-display declarations of the
source module and the executable machine root plan are roots.
`LEAN_TRANSPORT_OUT` selects the artifact directory. A known-family file may
be supplied to produce a separate list of newly required families.
-/

open Lean
open Mettapedia.Languages.Lean.Declarations.Manifest

def exportTransportManifest : CoreM Unit := do
  let selectedRoots ← IO.getEnv "LEAN_TRANSPORT_ROOTS"
  let directory : System.FilePath := match selectedRoots with
    | some file => (System.FilePath.mk file).parent.getD "."
    | none => "artifacts/lean-declarations/functional-correspondence"
  let modules ← Mettapedia.Languages.Lean.Declarations.TargetEnvironment.load directory
  let env ← getEnv
  let own := (modules.sources.flatMap (ownDeclarations env)).qsort (fun a b => a.toString < b.toString)
  let roots ← match selectedRoots with
    | some file =>
        match resolveRoots env (← IO.FS.readFile file) with
        | .ok roots => pure roots
        | .error reason => throwError reason
    | none =>
        let base := own.filter fun name => (displayReason name).isNone
        let extras ← match resolveRoots env (← IO.FS.readFile
            "artifacts/lean-code-equations/functional-correspondence/roots.txt") with
          | .ok extras => pure extras
          | .error reason => throwError reason
        pure (extras.foldl (fun roots name => if roots.contains name then roots else roots.push name) base)
  let names ← match closure env roots with
    | .ok names => pure names
    | .error reason => throwError reason
  let out : System.FilePath := (← IO.getEnv "LEAN_TRANSPORT_OUT").getD
    "artifacts/lean-declarations/functional-correspondence"
  let mut outputs := #[("roots.txt", rootsText roots),
    ("display-exclusions.tsv", exclusionsText own),
    ("manifest.tsv", manifestText env roots names),
    ("family-roots.txt", rootsText (directFamilies env names)),
    ("profile.json", (Json.mkObj [
      ("schema", toJson (1 : Nat)), ("lean", toJson Lean.versionString),
      ("sourceModule", toJson ((modules.sources[0]?).map Name.toString |>.getD "")),
      ("sourceModules", toJson (modules.sources.map Name.toString)),
      ("theoremProofs", toJson "reconstructed; statement dependencies included"),
      ("recursorRules", toJson "constructor identities and right-hand-side dependencies included"),
      ("roots", toJson roots.size), ("constants", toJson names.size)]).compress ++ "\n")]
  if let some file ← IO.getEnv "LEAN_TRANSPORT_KNOWN_FAMILIES" then
    let known ← match resolveRoots env (← IO.FS.readFile file) with
      | .ok known => pure known
      | .error reason => throwError reason
    outputs := outputs.push ("additional-family-roots.txt",
      rootsText ((directFamilies env names).filter fun name => !known.contains name))
  if (← IO.getEnv "LEAN_TRANSPORT_CHECK") == some "1" then
    for (file, text) in outputs do
      unless (← IO.FS.readFile (out / file)) == text do
        throwError "transport inventory differs: {file}"
  else
    IO.FS.createDirAll out
    for (file, text) in outputs do IO.FS.writeFile (out / file) text
  logInfo m!"Transport inventory: {roots.size} roots, {names.size} constants, {(directFamilies env names).size} families"

#eval exportTransportManifest
