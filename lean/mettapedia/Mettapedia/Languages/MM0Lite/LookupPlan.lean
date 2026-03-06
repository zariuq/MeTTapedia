import MeTTailCore
import Mettapedia.Languages.MM0Lite.LanguageDef

namespace Mettapedia.Languages.MM0Lite.LookupPlan

open MeTTailCore.MeTTaIL.LookupPlan
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MM0Lite.LanguageDef

private def argB (pos : Nat) : SignatureArg :=
  { position := pos, mode := .bound }

private def argF (pos : Nat) : SignatureArg :=
  { position := pos, mode := .free }

private def hasUseRuleWithThmConcl : Bool :=
  mm0Lite.rewrites.any fun rw =>
    rw.name == "R_Use" &&
      rw.premises.any (fun
        | .relationQuery rel args =>
            rel == "thmConcl" && args.length == 2
        | _ => false)

private def mkThmConclFamily : LookupFamilyPlan :=
  { family := "thmConcl"
    logicalRelationId := "mm0lite.thm_concl"
    factRelation := "theoremFact"
    rawRelation := "thmConclRaw"
    hasRelation := "thmConclHas"
    resultRelation := some "thmConclResult"
    queryArity := 1
    payloadArity := 1
    keyPositions := [0]
    demand :=
      [ { relation := "thmConclResult"
          logicalRelationId := "mm0lite.thm_concl.result"
          scopeSignature := "b0+f1"
          arity := 2
          args := [argB 0, argF 1]
          usageKind := .enumerate
          hotPath := true }
      , { relation := "thmConclHas"
          logicalRelationId := "mm0lite.thm_concl.exists"
          scopeSignature := "b0"
          arity := 1
          args := [argB 0]
          usageKind := .exists
          hotPath := true } ]
    contracts :=
      { noFalseNegatives := true
        exactResult := true
        stratifiedNegationSafe := true } }

def deriveMM0LookupPlan? : Except String LookupPlanArtifact := do
  unless hasUseRuleWithThmConcl do
    throw "MM0Lite lookup-plan derivation failed: missing R_Use premise relationQuery(thmConcl, [th, concl])"
  let artifact : LookupPlanArtifact :=
    { schemaVersion := 2
      dialect := "mm0lite"
      families := [mkThmConclFamily] }
  let lintErrs := artifact.lintErrors
  if !lintErrs.isEmpty then
    throw s!"MM0Lite lookup-plan lint failed:\n{String.intercalate "\n" lintErrs}"
  pure artifact

def derivationIsOk : Bool :=
  match deriveMM0LookupPlan? with
  | .ok _ => true
  | .error _ => false

#guard derivationIsOk = true

def exportMM0LookupPlan (outDir : System.FilePath) : IO UInt32 := do
  match deriveMM0LookupPlan? with
  | .error err =>
      IO.println s!"mm0lite lookup-plan derivation failed: {err}"
      pure 2
  | .ok artifact =>
      let jsonPath := outDir / "mm0lite.lookup_plan.json"
      let checksumPath := outDir / "mm0lite.lookup_plan.checksum"
      IO.FS.createDirAll outDir
      IO.FS.writeFile jsonPath (artifact.renderJson ++ "\n")
      IO.FS.writeFile checksumPath (artifact.checksumString ++ "\n")
      IO.println s!"exported mm0lite lookup-plan artifact to {outDir}"
      pure 0

def checkMM0LookupPlan (outDir : System.FilePath) : IO UInt32 := do
  match deriveMM0LookupPlan? with
  | .error err =>
      IO.println s!"mm0lite lookup-plan derivation failed: {err}"
      pure 2
  | .ok artifact =>
      let jsonPath := outDir / "mm0lite.lookup_plan.json"
      let checksumPath := outDir / "mm0lite.lookup_plan.checksum"
      try
        let jsonText ← IO.FS.readFile jsonPath
        let checksumText ← IO.FS.readFile checksumPath
        let jsonOk := jsonText.trimAscii.toString == artifact.renderJson.trimAscii.toString
        let checksumOk := checksumText.trimAscii.toString == artifact.checksumString.trimAscii.toString
        if jsonOk && checksumOk then
          IO.println s!"[ok] mm0lite lookup-plan artifact matches at {outDir}"
          pure 0
        else
          IO.println s!"[drift] mm0lite lookup-plan artifact mismatch at {outDir}"
          if !jsonOk then
            IO.println s!"  json mismatch at {jsonPath}"
          if !checksumOk then
            IO.println s!"  checksum mismatch at {checksumPath}"
          pure 3
      catch e =>
        IO.println s!"mm0lite lookup-plan check failed: {e}"
        pure 2

end Mettapedia.Languages.MM0Lite.LookupPlan

