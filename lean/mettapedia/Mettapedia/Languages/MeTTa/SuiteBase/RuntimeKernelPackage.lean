import Mettapedia.Languages.MeTTa.RuntimeExec
import Mettapedia.Languages.MeTTa.SuiteBase.RuntimeKernelClassified

/-!
# Runtime-Kernel Package

Internal package/theorem layer for the MeTTa runtime-boundary package.
-/

namespace Mettapedia.Languages.MeTTa.RuntimeKernel

open Mettapedia.Languages.MeTTa.ElaboratedCore
open Mettapedia.Languages.MeTTa.RuntimeExec
open MeTTailCore.MeTTaIL.EffectSafety

/-! ## 4. Packaged runtime kernel -/

/-- The runtime kernel package: the triad of proved surfaces together with
their explicit effect and resource classifications.

This is the backend-neutral target object that ElaboratedCore can consume
without importing MORK internals. -/
structure RuntimeKernelPackage where
  triad : MeTTaRuntimeKernelTriad
  oracle : MeTTaRuntimeOracleSurface
  execClass : ClassifiedFragment
  queryClass : ClassifiedFragment
  spaceEffectClass : ClassifiedFragment
  oracleClasses : List ClassifiedFragment

/-- Canonical MORK/MM2 runtime kernel package over the current proved seams. -/
noncomputable def morkRuntimeKernelPackage : RuntimeKernelPackage where
  triad := morkRuntimeKernelTriad
  oracle := morkRuntimeOracleExec0
  execClass := execFragment
  queryClass := queryFragment
  spaceEffectClass := spaceEffectFragment
  oracleClasses := [solverOracleFragment, externalOracleFragment]

/-! ## 5. Classification theorems -/

section EffectClassification

theorem exec_effectClass : execFragment.effectClass = .pureStructural := rfl
theorem query_effectClass : queryFragment.effectClass = .readOnlyLookup := rfl
theorem spaceEffect_effectClass : spaceEffectFragment.effectClass = .writesState := rfl
theorem solverOracle_effectClass : solverOracleFragment.effectClass = .oracleIO := rfl
theorem externalOracle_effectClass : externalOracleFragment.effectClass = .oracleIO := rfl

theorem ruleExec_effectClass_agree :
    RuntimeKernelClass.ruleExec.effectClass = .pureStructural := rfl
theorem query_effectClass_agree :
    RuntimeKernelClass.query.effectClass = .readOnlyLookup := rfl
theorem spaceEffect_effectClass_agree :
    RuntimeKernelClass.spaceEffect.effectClass = .writesState := rfl
theorem oracle_effectClass_agree :
    RuntimeKernelClass.oracle.effectClass = .oracleIO := rfl

end EffectClassification

section ResourceClassification

theorem exec_resource : execFragment.resourceClass = .defaultAtomSpace := rfl
theorem query_resource : queryFragment.resourceClass = .defaultAtomSpace := rfl
theorem spaceEffect_resource : spaceEffectFragment.resourceClass = .defaultAtomSpace := rfl
theorem solverOracle_resource : solverOracleFragment.resourceClass = .solverResource := rfl
theorem externalOracle_resource : externalOracleFragment.resourceClass = .externalResource := rfl

end ResourceClassification

section BackendAgreement

theorem exec_backend : execFragment.backendName = "MORK/MM2" := rfl
theorem query_backend : queryFragment.backendName = "MORK/MM2" := rfl
theorem spaceEffect_backend : spaceEffectFragment.backendName = "MORK/MM2" := rfl
theorem solverOracle_backend : solverOracleFragment.backendName = "MORK/MM2" := rfl
theorem externalOracle_backend : externalOracleFragment.backendName = "MORK/MM2" := rfl

theorem all_backend_mork :
    execFragment.backendName = "MORK/MM2" ∧
    queryFragment.backendName = "MORK/MM2" ∧
    spaceEffectFragment.backendName = "MORK/MM2" ∧
    solverOracleFragment.backendName = "MORK/MM2" ∧
    externalOracleFragment.backendName = "MORK/MM2" :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end BackendAgreement

section MemoizationSafety

/-- Exec (pure structural) supports outcome-set memoization. -/
theorem exec_memo_outcomeSet :
    execFragment.effectClass.supportsMemoShape .outcomeSet = true := by decide

/-- Exec (pure structural) supports scalar memoization. -/
theorem exec_memo_scalar :
    execFragment.effectClass.supportsMemoShape .scalar = true := by decide

/-- Query (read-only lookup) supports scalar memoization. -/
theorem query_memo_scalar :
    queryFragment.effectClass.supportsMemoShape .scalar = true := by decide

/-- Query (read-only lookup) supports outcome-set memoization. -/
theorem query_memo_outcomeSet :
    queryFragment.effectClass.supportsMemoShape .outcomeSet = true := by decide

/-- Space effects (writes state) do NOT support outcome-set memoization. -/
theorem spaceEffect_not_memo_outcomeSet :
    spaceEffectFragment.effectClass.supportsMemoShape .outcomeSet = false := by decide

/-- Space effects (writes state) do NOT support scalar memoization. -/
theorem spaceEffect_not_memo_scalar :
    spaceEffectFragment.effectClass.supportsMemoShape .scalar = false := by decide

end MemoizationSafety

/-! ## Canaries -/

section Canaries
#check @RuntimeKernelClass.effectClass
#check @RuntimeKernelTarget.effectClass
#check @ClassifiedFragment
#check @execFragment
#check @queryFragment
#check @spaceEffectFragment
#check @solverOracleFragment
#check @externalOracleFragment
#check @RuntimeKernelPackage
#check @morkRuntimeKernelPackage
#check @exec_effectClass
#check @query_effectClass
#check @spaceEffect_effectClass
#check @solverOracle_effectClass
#check @exec_memo_outcomeSet
#check @query_memo_scalar
#check @spaceEffect_not_memo_outcomeSet
#check @all_backend_mork
end Canaries

/-! ## Axiom audit -/

section AxiomAudit
#print axioms exec_effectClass
#print axioms query_effectClass
#print axioms spaceEffect_effectClass
#print axioms exec_memo_outcomeSet
#print axioms spaceEffect_not_memo_outcomeSet
#print axioms all_backend_mork
end AxiomAudit

end Mettapedia.Languages.MeTTa.RuntimeKernel
