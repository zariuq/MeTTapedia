import MeTTailCore
import Mettapedia.Languages.MinskyLite.LanguageDef

namespace Mettapedia.Languages.MinskyLite.LookupPlan

open MeTTailCore.MeTTaIL.LookupPlan
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MinskyLite.LanguageDef

private def hasLookupPremises : Bool :=
  minskyLite.rewrites.any (fun rw =>
    rw.premises.any (fun
      | .relationQuery _ _ => true
      | _ => false))

def deriveMinskyLiteLookupPlan? : Except String LookupPlanArtifact := do
  if hasLookupPremises then
    throw "MinskyLite lookup-plan derivation failed: expected no relation-query premises"
  let artifact : LookupPlanArtifact :=
    { schemaVersion := 2
      dialect := "minskylite"
      families := [] }
  let lintErrs := artifact.lintErrors
  unless lintErrs.isEmpty do
    throw s!"MinskyLite lookup-plan lint failed:\n{String.intercalate "\n" lintErrs}"
  pure artifact

def derivationIsOk : Bool :=
  match deriveMinskyLiteLookupPlan? with
  | .ok _ => true
  | .error _ => false

#guard derivationIsOk = true

def exportMinskyLiteLookupPlan (outDir : System.FilePath) : IO UInt32 := do
  match deriveMinskyLiteLookupPlan? with
  | .error err =>
      IO.println s!"minskylite lookup-plan derivation failed: {err}"
      pure 2
  | .ok artifact =>
      let jsonPath := outDir / "minskylite.lookup_plan.json"
      let checksumPath := outDir / "minskylite.lookup_plan.checksum"
      IO.FS.createDirAll outDir
      IO.FS.writeFile jsonPath (artifact.renderJson ++ "\n")
      IO.FS.writeFile checksumPath (artifact.checksumString ++ "\n")
      IO.println s!"exported minskylite lookup-plan artifact to {outDir}"
      pure 0

def checkMinskyLiteLookupPlan (outDir : System.FilePath) : IO UInt32 := do
  match deriveMinskyLiteLookupPlan? with
  | .error err =>
      IO.println s!"minskylite lookup-plan derivation failed: {err}"
      pure 2
  | .ok artifact =>
      let jsonPath := outDir / "minskylite.lookup_plan.json"
      let checksumPath := outDir / "minskylite.lookup_plan.checksum"
      try
        let jsonText <- IO.FS.readFile jsonPath
        let checksumText <- IO.FS.readFile checksumPath
        let jsonOk := jsonText.trimAscii.toString == artifact.renderJson.trimAscii.toString
        let checksumOk := checksumText.trimAscii.toString == artifact.checksumString.trimAscii.toString
        if jsonOk && checksumOk then
          IO.println s!"[ok] minskylite lookup-plan artifact matches at {outDir}"
          pure 0
        else
          IO.println s!"[drift] minskylite lookup-plan artifact mismatch at {outDir}"
          if !jsonOk then
            IO.println s!"  json mismatch at {jsonPath}"
          if !checksumOk then
            IO.println s!"  checksum mismatch at {checksumPath}"
          pure 3
      catch e =>
        IO.println s!"minskylite lookup-plan check failed: {e}"
        pure 2

end Mettapedia.Languages.MinskyLite.LookupPlan
