import Mettapedia.Languages.MeTTa.ElaboratedCoreBase
import MeTTailCore

/-!
# Runtime-Kernel Package: Effect-Class Bridge

Connects the backend-neutral `RuntimeKernelClass` (from `ElaboratedCoreBase`)
to `EffectClass` (from `MeTTailCore.MeTTaIL.EffectSafety`) and packages the
current MORK/MM2-backed runtime kernel seams with explicit effect and resource
classifications.

This file is the single runtime-kernel packaging layer. It does not touch
PureKernel, ElaboratedCore proof certificates, WM, or mettail-rust.

Positive example:
- Packages the already-proved `MeTTaRuntimeKernelTriad` plus the first oracle
  request/response seam with honest effect-class assignments derived from the
  current proved MORK/MM2 seams.

Negative example:
- Does not add a large abstract resource calculus or pretend to support
  full runtime semantics beyond the current three operational classes.
-/

namespace Mettapedia.Languages.MeTTa.ElaboratedCore

open MeTTailCore.MeTTaIL.EffectSafety

/-! ## 1. Effect-class bridge

Assigns a conservative `EffectClass` to each `RuntimeKernelClass` based on
the current proved MORK/MM2 seams:

- `ruleExec`: eval/evalc are pure structural rewrites
- `query`: match &self, get-atoms are read-only lookups
- `spaceEffect`: add-atom, remove-atom mutate workspace state
- `oracle`: grounded/FFI calls are side-effecting I/O
- `metaPhase`: meta-reflection is structural
-/
def RuntimeKernelClass.effectClass : RuntimeKernelClass → EffectClass
  | .ruleExec    => .pureStructural
  | .query       => .readOnlyLookup
  | .spaceEffect => .writesState
  | .oracle      => .oracleIO
  | .metaPhase   => .pureStructural

def RuntimeKernelTarget.effectClass (t : RuntimeKernelTarget) : EffectClass :=
  t.kernelClass.effectClass

end Mettapedia.Languages.MeTTa.ElaboratedCore

namespace Mettapedia.Languages.MeTTa.RuntimeKernel

open Mettapedia.Languages.MeTTa.ElaboratedCore
open Mettapedia.Languages.MeTTa.RuntimeExec
open MeTTailCore.MeTTaIL.EffectSafety

/-! ## 2. Classified fragment

Pairs a kernel class with its proved effect class, resource class, and backend
name. This is the object that ElaboratedCore can target through backend-neutral
classes without importing scheduler internals.
-/
structure ClassifiedFragment where
  kernelClass : RuntimeKernelClass
  effectClass : EffectClass
  resourceClass : RuntimeResourceClass
  backendName : String
deriving Repr, DecidableEq

/-! ## 3. Current MORK/MM2-backed classified fragments -/

/-- PeTTa eval/evalc rewrite steps over the default atomspace. -/
def execFragment : ClassifiedFragment where
  kernelClass := .ruleExec
  effectClass := .pureStructural
  resourceClass := .defaultAtomSpace
  backendName := "MORK/MM2"

/-- match &self, get-atoms &self queries over the default atomspace. -/
def queryFragment : ClassifiedFragment where
  kernelClass := .query
  effectClass := .readOnlyLookup
  resourceClass := .defaultAtomSpace
  backendName := "MORK/MM2"

/-- add-atom, remove-atom mutations over the default atomspace. -/
def spaceEffectFragment : ClassifiedFragment where
  kernelClass := .spaceEffect
  effectClass := .writesState
  resourceClass := .defaultAtomSpace
  backendName := "MORK/MM2"

/-- Z3-backed oracle interactions over the solver resource. -/
def solverOracleFragment : ClassifiedFragment where
  kernelClass := .oracle
  effectClass := .oracleIO
  resourceClass := .solverResource
  backendName := "MORK/MM2"

/-- ACT-backed external lookups over the external resource. -/
def externalOracleFragment : ClassifiedFragment where
  kernelClass := .oracle
  effectClass := .oracleIO
  resourceClass := .externalResource
  backendName := "MORK/MM2"

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
