import Mettapedia.Languages.MeTTa.ExecutionContract
import Mettapedia.Languages.MeTTa.HE.LookupPlan

/-!
# HE Execution Contract

First HE instance of the shared MeTTa execution-contract surface.

This file starts with the narrowest honest shared lane:
- `eqQuery` as a read-only lookup family over the default atomspace

Positive example:
- `eqQuery` is query-compilable, read-only, and supports scalar/outcome-set
  memo shapes through the shared runtime-kernel query boundary.

Negative example:
- this file does not yet certify HE intrinsic builtins or broader rewrite
  execution fragments.
-/

namespace Mettapedia.Languages.MeTTa.HE.ExecutionContract

open Mettapedia.Languages.MeTTa.ExecutionContract
open Mettapedia.Languages.MeTTa.RuntimeKernel
open MeTTailCore.MeTTaIL.EffectSafety

private def heEqQueryTheoremRefs : List String :=
  [ "Mettapedia.Languages.MeTTa.RuntimeKernel.query_effectClass"
  , "Mettapedia.Languages.MeTTa.RuntimeKernel.query_memo_scalar"
  , "Mettapedia.Languages.MeTTa.RuntimeKernel.query_memo_outcomeSet"
  , "Mettapedia.Languages.MeTTa.HE.LookupPlan.heEqQueryFamily_negatesHas_notResult"
  ]

/-- First HE execution-contract entry: the derived `eqQuery` lookup family. -/
def heEqQueryLookupContract : LookupQueryContract where
  head := "eqQuery"
  surfaceHead := none
  arity := 2
  lookupFamily := Mettapedia.Languages.MeTTa.HE.LookupPlan.heEqQueryFamily
  owner := .artifactBackend
  kernelClass := .query
  effectClass := queryFragment.effectClass
  resourceClass := queryFragment.resourceClass
  backendName := queryFragment.backendName
  supportedMemoShapes := [.scalar, .outcomeSet]
  sourceRuleCompilable := false
  queryCompilable := true
  spaceEffectCompilable := false
  builtinDemand := none
  theoremRefs := heEqQueryTheoremRefs

def heEqQueryEntry : ExecutionContractEntry :=
  .lookupQuery heEqQueryLookupContract

def heExecutionContractArtifact : ExecutionContractArtifact where
  dialect := "he"
  entries := [heEqQueryEntry] ++ coreIntrinsicEntries

theorem heEqQuery_effectClass :
    heEqQueryLookupContract.effectClass = .readOnlyLookup := rfl

theorem heEqQuery_resource :
    heEqQueryLookupContract.resourceClass = .defaultAtomSpace := rfl

theorem heEqQuery_backend :
    heEqQueryLookupContract.backendName = "MORK/MM2" := rfl

theorem heEqQuery_noFalseNegatives :
    heEqQueryLookupContract.noFalseNegatives = true := rfl

theorem heEqQuery_exactResult :
    heEqQueryLookupContract.exactResult = false := rfl

theorem heEqQuery_stratifiedNegationSafe :
    heEqQueryLookupContract.stratifiedNegationSafe = true := rfl

theorem heEqQuery_scalarMemo :
    heEqQueryLookupContract.effectClass.supportsMemoShape .scalar = true := by
  simpa [heEqQueryLookupContract] using query_memo_scalar

theorem heEqQuery_outcomeSetMemo :
    heEqQueryLookupContract.effectClass.supportsMemoShape .outcomeSet = true := by
  simpa [heEqQueryLookupContract] using query_memo_outcomeSet

theorem hePlusIntrinsic_effectClass :
    (mkCoreIntrinsicContract { head := "+", minArity := 2, demand := .numericArgs }).effectClass = .pureStructural := rfl

def exportHeExecutionContract (outDir : System.FilePath) : IO UInt32 := do
  let artifact := heExecutionContractArtifact
  let lintErrs := artifact.lintErrors
  if !lintErrs.isEmpty then
    IO.println s!"he execution contract lint failed:\n{String.intercalate "\n" lintErrs}"
    pure 2
  else
    let jsonPath := outDir / "he.execution_contract.json"
    let checksumPath := outDir / "he.execution_contract.checksum"
    IO.FS.createDirAll outDir
    IO.FS.writeFile jsonPath (artifact.renderJson ++ "\n")
    IO.FS.writeFile checksumPath (artifact.checksumString ++ "\n")
    IO.println s!"exported he execution contract to {outDir}"
    pure 0

def checkHeExecutionContract (outDir : System.FilePath) : IO UInt32 := do
  let artifact := heExecutionContractArtifact
  let lintErrs := artifact.lintErrors
  if !lintErrs.isEmpty then
    IO.println s!"he execution contract lint failed:\n{String.intercalate "\n" lintErrs}"
    pure 2
  else
    let jsonPath := outDir / "he.execution_contract.json"
    let checksumPath := outDir / "he.execution_contract.checksum"
    try
      let jsonText ← IO.FS.readFile jsonPath
      let checksumText ← IO.FS.readFile checksumPath
      let jsonOk := jsonText.trimAscii.toString == artifact.renderJson.trimAscii.toString
      let checksumOk := checksumText.trimAscii.toString == artifact.checksumString.trimAscii.toString
      if jsonOk && checksumOk then
        IO.println s!"[ok] he execution contract matches at {outDir}"
        pure 0
      else
        if !jsonOk then
          IO.println s!"[drift] he execution contract json mismatch at {jsonPath}"
        if !checksumOk then
          IO.println s!"[drift] he execution contract checksum mismatch at {checksumPath}"
        pure 3
    catch e =>
      IO.println s!"he execution contract check failed: {e}"
      pure 2

section Canaries
#check @heEqQueryLookupContract
#check @heExecutionContractArtifact
#check @exportHeExecutionContract
#check @checkHeExecutionContract
end Canaries

end Mettapedia.Languages.MeTTa.HE.ExecutionContract
