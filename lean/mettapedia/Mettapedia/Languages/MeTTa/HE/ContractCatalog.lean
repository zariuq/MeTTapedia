import Mettapedia.Languages.MeTTa.ExecutionContract
import Mettapedia.Languages.MeTTa.HE.LookupPlan

/-!
# HE Contract Catalog

Semantic catalog for the HE execution-contract surface.
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

end Mettapedia.Languages.MeTTa.HE.ExecutionContract
