import MeTTailCore
import Mettapedia.Languages.IMP.LanguageDef

namespace Mettapedia.Languages.IMP.LookupPlan

open MeTTailCore.MeTTaIL.LookupPlan
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.IMP.LanguageDef

private def argB (pos : Nat) : SignatureArg :=
  { position := pos, mode := .bound }

private def argF (pos : Nat) : SignatureArg :=
  { position := pos, mode := .free }

private def hasStoreGetRule : Bool :=
  imp.rewrites.any fun rw =>
    rw.name == "R_AVar" &&
      rw.premises.any (fun
        | .relationQuery rel args =>
            rel == "storeGet" && args.length == 3
        | _ => false)

private def mkStoreGetFamily : LookupFamilyPlan :=
  { family := "storeGet"
    logicalRelationId := "imp.store_get"
    factRelation := "storeCell"
    rawRelation := "storeGetRaw"
    hasRelation := "storeGetHas"
    resultRelation := some "storeGetResult"
    queryArity := 2
    payloadArity := 1
    keyPositions := [0, 1]
    demand :=
      [ { relation := "storeGetResult"
          logicalRelationId := "imp.store_get.result"
          scopeSignature := "b0+b1+f2"
          arity := 3
          args := [argB 0, argB 1, argF 2]
          usageKind := .enumerate
          hotPath := true }
      , { relation := "storeGetHas"
          logicalRelationId := "imp.store_get.exists"
          scopeSignature := "b0+b1"
          arity := 2
          args := [argB 0, argB 1]
          usageKind := .exists
          hotPath := true } ]
    contracts :=
      { noFalseNegatives := true
        exactResult := true
        stratifiedNegationSafe := true } }

def deriveIMPLookupPlan? : Except String LookupPlanArtifact := do
  unless hasStoreGetRule do
    throw "IMP lookup-plan derivation failed: missing R_AVar premise relationQuery(storeGet, [store, x, n])"
  let artifact : LookupPlanArtifact :=
    { schemaVersion := 2
      dialect := "imp"
      families := [mkStoreGetFamily] }
  let lintErrs := artifact.lintErrors
  unless lintErrs.isEmpty do
    throw s!"IMP lookup-plan lint failed:\n{String.intercalate "\n" lintErrs}"
  pure artifact

def derivationIsOk : Bool :=
  match deriveIMPLookupPlan? with
  | .ok _ => true
  | .error _ => false

#guard derivationIsOk = true

def exportIMPLookupPlan (outDir : System.FilePath) : IO UInt32 := do
  match deriveIMPLookupPlan? with
  | .error err =>
      IO.println s!"imp lookup-plan derivation failed: {err}"
      pure 2
  | .ok artifact =>
      let jsonPath := outDir / "imp.lookup_plan.json"
      let checksumPath := outDir / "imp.lookup_plan.checksum"
      IO.FS.createDirAll outDir
      IO.FS.writeFile jsonPath (artifact.renderJson ++ "\n")
      IO.FS.writeFile checksumPath (artifact.checksumString ++ "\n")
      IO.println s!"exported imp lookup-plan artifact to {outDir}"
      pure 0

def checkIMPLookupPlan (outDir : System.FilePath) : IO UInt32 := do
  match deriveIMPLookupPlan? with
  | .error err =>
      IO.println s!"imp lookup-plan derivation failed: {err}"
      pure 2
  | .ok artifact =>
      let jsonPath := outDir / "imp.lookup_plan.json"
      let checksumPath := outDir / "imp.lookup_plan.checksum"
      try
        let jsonText ← IO.FS.readFile jsonPath
        let checksumText ← IO.FS.readFile checksumPath
        let jsonOk := jsonText.trimAscii.toString == artifact.renderJson.trimAscii.toString
        let checksumOk := checksumText.trimAscii.toString == artifact.checksumString.trimAscii.toString
        if jsonOk && checksumOk then
          IO.println s!"[ok] imp lookup-plan artifact matches at {outDir}"
          pure 0
        else
          IO.println s!"[drift] imp lookup-plan artifact mismatch at {outDir}"
          if !jsonOk then
            IO.println s!"  json mismatch at {jsonPath}"
          if !checksumOk then
            IO.println s!"  checksum mismatch at {checksumPath}"
          pure 3
      catch e =>
        IO.println s!"imp lookup-plan check failed: {e}"
        pure 2

end Mettapedia.Languages.IMP.LookupPlan
