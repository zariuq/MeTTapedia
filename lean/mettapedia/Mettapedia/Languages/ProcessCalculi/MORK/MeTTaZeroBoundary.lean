import Mettapedia.Languages.MeTTa.MeTTaZeroWorkClosure
import Mettapedia.Languages.ProcessCalculi.MORK.GSLTSemantics

/-!
# The generated-work boundary between MM2 and bare MeTTa Zero

The canonical Zero evaluation GSLT is intentionally one-step: every answer is
terminal.  MM2 spaces instead contain pending `exec` atoms, and a selected
directive may emit another directive that the same scheduler subsequently
selects.

This module gives an executable two-step MM2 witness and turns that difference
into a structural non-embedding theorem.  The result concerns internal work
closure, not Turing computability: a global translation may add explicit
runner configurations, while a direct structural embedding into bare Zero
cannot.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.GSLT
open Mettapedia.Languages.MeTTa.MeTTaZero
open Mettapedia.Languages.MeTTa.OSLFCore
open WQComputable
open Conformance.Computable (cmatchPattern)

/-! ## The executable MM2 work-queue GSLT -/

/-- The duplicate-free list realization used by the executable MM2
conformance model.  Its correspondence with support-level `validExecGSLT` is
stated below under the exact scheduler invariant already identified by the
MORK formalization. -/
def nativeListExecGSLT : GSLT where
  Term := List Atom
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target => cWorkQueueStep source = some target
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

@[simp] theorem nativeListExecGSLT_step_iff (source target : List Atom) :
    nativeListExecGSLT.Step source target ↔
      cWorkQueueStep source = some target :=
  Iff.rfl

/-- Every native list step satisfying the established realization invariant
is a step of the authored support-level MM2 GSLT. -/
theorem nativeListExec_step_refines_validExec
    {source target : List Atom} (invariant : WorkQueueInvariant source)
    (step : nativeListExecGSLT.Step source target) :
    validExecGSLT.Step source.toFinset target.toFinset := by
  apply (validExecGSLT_step_iff _ _).2
  have agreement := cWorkQueueStep_toFinset source invariant.nodup
    invariant.keyInj invariant.fire
  have nativeStep := (nativeListExecGSLT_step_iff source target).mp step
  rw [nativeStep] at agreement
  exact agreement.symm

/-! ## A directive that emits later work -/

def generatedWorkExec : Atom :=
  .expression [.symbol "exec",
    .expression [.symbol "0", .symbol "persist"],
    .expression [.symbol ","],
    .expression [.symbol "O"]]

def generatedWorkRespawner : Atom :=
  .expression [.symbol "exec",
    .expression [.symbol "0", .symbol "persist"],
    .expression [.symbol ","],
    .expression [.symbol "O",
      .expression [.symbol "+", generatedWorkExec]]]

def generatedWorkInitial : List Atom :=
  [generatedWorkRespawner]

def generatedWorkMiddle : List Atom :=
  [generatedWorkExec]

def generatedWorkFinal : List Atom :=
  []

/-- The first directive consumes itself and emits a second executable
directive.  Its empty conjunction contributes exactly one substitution row. -/
@[simp] theorem generatedWork_first_step :
    cWorkQueueStep generatedWorkInitial = some generatedWorkMiddle :=
  rfl

/-- The emitted directive is selected on the next scheduler step and consumed
without replacement. -/
@[simp] theorem generatedWork_second_step :
    cWorkQueueStep generatedWorkMiddle = some generatedWorkFinal :=
  rfl

/-- The concrete starting state satisfies the exact list-to-support
correspondence obligations. -/
theorem generatedWorkInitial_invariant :
    WorkQueueInvariant generatedWorkInitial := by
  constructor
  · simp [generatedWorkInitial]
  · simp [KeyInjective, generatedWorkInitial, cExecFacts,
      generatedWorkRespawner, extractExecFact]
  · intro fact selected
    simp [generatedWorkInitial, cExecFacts, generatedWorkRespawner,
      extractExecFact, selectNextExec, selectNextScheduled] at selected
    subst fact
    constructor
    · simp [generatedWorkInitial, generatedWorkRespawner]
    · simp [cReadCopy, cConsumeExec, cmatchPattern, matchPattern, mkExecRule,
        mkPattern, cmatchPattern.go, matchPattern.go]

/-- The residual state containing the emitted directive also satisfies the
list-to-support correspondence obligations. -/
theorem generatedWorkMiddle_invariant :
    WorkQueueInvariant generatedWorkMiddle := by
  constructor
  · simp [generatedWorkMiddle]
  · simp [KeyInjective, generatedWorkMiddle, cExecFacts,
      generatedWorkExec, extractExecFact]
  · intro fact selected
    simp [generatedWorkMiddle, cExecFacts, generatedWorkExec,
      extractExecFact, selectNextExec, selectNextScheduled] at selected
    subst fact
    constructor
    · simp [generatedWorkMiddle, generatedWorkExec]
    · simp [cReadCopy, cConsumeExec, cmatchPattern, matchPattern, mkExecRule,
        mkPattern, cmatchPattern.go, matchPattern.go]

/-- MM2's executable work queue has genuine internal re-entry. -/
theorem nativeMM2_has_composable_steps :
    HasComposableSteps nativeListExecGSLT := by
  exact ⟨generatedWorkInitial, generatedWorkMiddle, generatedWorkFinal,
    generatedWork_first_step, generatedWork_second_step⟩

/-- The first executable canary edge is also an authored support-level MM2
edge. -/
theorem generatedWork_first_validExec_step :
    validExecGSLT.Step generatedWorkInitial.toFinset
      generatedWorkMiddle.toFinset :=
  nativeListExec_step_refines_validExec generatedWorkInitial_invariant
    generatedWork_first_step

/-- The second executable canary edge is also an authored support-level MM2
edge. -/
theorem generatedWork_second_validExec_step :
    validExecGSLT.Step generatedWorkMiddle.toFinset
      generatedWorkFinal.toFinset :=
  nativeListExec_step_refines_validExec generatedWorkMiddle_invariant
    generatedWork_second_step

/-- The authored support-level MM2 GSLT itself has internal work closure. -/
theorem authoredMM2_has_composable_steps :
    HasComposableSteps validExecGSLT := by
  exact ⟨generatedWorkInitial.toFinset, generatedWorkMiddle.toFinset,
    generatedWorkFinal.toFinset, generatedWork_first_validExec_step,
    generatedWork_second_validExec_step⟩

/-! ## The structural separation -/

/-- A structural GSLT embedding preserves internal re-entry. -/
theorem hasComposableSteps_of_embedding {source target : GSLT}
    (embedding : GSLT.Embedding source target)
    (sourceReentry : HasComposableSteps source) :
    HasComposableSteps target := by
  obtain ⟨first, middle, last, firstStep, secondStep⟩ := sourceReentry
  exact ⟨embedding.toFun first, embedding.toFun middle, embedding.toFun last,
    (embedding.step_iff first middle).2 firstStep,
    (embedding.step_iff middle last).2 secondStep⟩

/-- **Zero/MM2 work-closure separation.**  There is no faithful structural
embedding of MM2's executable work-queue GSLT into the bare one-step Zero
evaluation GSLT.  Such a translation must add a runner/control carrier or
compile generated work globally; it cannot merely rename terms and steps. -/
theorem no_nativeMM2_embedding_into_bareZero (model : Model) :
    ¬ Nonempty (GSLT.Embedding nativeListExecGSLT (evaluationGSLT model)) := by
  rintro ⟨embedding⟩
  exact bareZero_has_no_composable_steps model
    (hasComposableSteps_of_embedding embedding nativeMM2_has_composable_steps)

/-- The same separation at the authored MM2 semantic level. -/
theorem no_authoredMM2_embedding_into_bareZero (model : Model) :
    ¬ Nonempty (GSLT.Embedding validExecGSLT (evaluationGSLT model)) := by
  rintro ⟨embedding⟩
  exact bareZero_has_no_composable_steps model
    (hasComposableSteps_of_embedding embedding authoredMM2_has_composable_steps)

/-- The negative and positive sides in one theorem: base Zero lacks internal
re-entry, whereas the status-aware Zero runner restores it without importing
MM2's support quotient or priority policy. -/
theorem bareZero_and_iterativeZero_are_separated :
    (¬ HasComposableSteps (evaluationGSLT chainModel)) ∧
      HasComposableSteps (iterativeGSLT chainModel) :=
  ⟨bareZero_has_no_composable_steps chainModel,
    iterativeZero_has_composable_steps⟩

end Mettapedia.Languages.ProcessCalculi.MORK
