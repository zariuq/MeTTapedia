import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceScopedExecutionControls

/-!
# A real caller-frame binding accompanies protected inference publication

The extra caller equation is solved by the actual worklist. Its variable
also occurs in a retained continuation root and a stored-template capture.
The inference projection forgets that external equation, while the receipt
retains its native result, concrete answer and complete scope inventory.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceScopedFrameControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenApplicationControls (a b definition)
open ContextualFrameUpdate
open InferenceRequestExecution (Occurrence label location)
open ScopedInferenceValues (Ready base encode)
open InferenceJudgmentBoards
open InferenceTraceClassifying
open InferenceScopedExecutionControls
  (locals captures active readyRequest readyA readyB readyRule actual_source_activates
    requestOccurrence premiseOccurrence outputOccurrence readyLabel state selection scopes retained templates
    nativeRule nativeRows nativeOutputs canonical_readback pending)

local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq (ScopedInferenceValues.Head × List Nat))

def extra : EquationStore (Term (signature base captures) [] ()) :=
  [(generator captures (), ContextualRigidActivation.into encode captures readyB)]

def occupied : Finset Nat :=
  InferenceScopedInventory.reserve locals captures scopes ∅ readyLabel state retained templates extra

def nativeBefore := ContextualRigidActivation.withFrame captures encode extra state
def problem := ContextualActivatedStep.problem locals captures occupied selection nativeRule nativeRows nativeBefore

theorem off_query_scope_is_reserved : occupied = {37} := by decide +kernel

theorem actual_ports_and_helper_namespace_are_reserved :
    ContextualActivationScopes.after occupied selection = {37, 38, 39, 40} ∧
      ContextualFreshFrameScopeLedger.helperLedger
        (ContextualActivationScopes.after occupied selection) = {37, 38, 39, 40, 41} := by
  rw [off_query_scope_is_reserved]
  decide +kernel

theorem full_problem_keeps_the_caller_equation : problem = [
    (generator active (.inr ()), ContextualRigidActivation.into encode active readyB),
    (ContextualRigidActivation.into encode active readyRequest, ContextualRigidActivation.into encode active readyRequest),
    (ContextualRigidActivation.into encode active readyA, ContextualRigidActivation.into encode active readyA)] := by
  unfold problem nativeBefore nativeRule nativeRows
  rw [ContextualRigidActivation.problem_withFrame, ContextualRigidActivation.problem]
  simp only [extra, ContextualFrameUnifier.mapProblem, List.map_cons, List.map_nil,
    ContextualRigidActivation.into, Rigid.instantiate_include]
  rfl

def independentAnswer : Assignment active active
  | .inl localName => nomatch localName.name
  | .inr () => ContextualRigidActivation.into encode active readyB

theorem independent_model : ContextualResidual.Models independentAnswer
    (ContextualResidual.observeProblem problem) := by
  apply (ContextualResidual.models_observeProblem independentAnswer problem).mpr
  intro equation member
  rw [full_problem_keeps_the_caller_equation] at member
  rcases List.mem_cons.mp member with same | rest
  · subst equation
    change instantiate independentAnswer (generator active (.inr ())) =
      instantiate independentAnswer (Rigid.includeTerm active (encode readyB))
    rw [instantiate_generator, Rigid.instantiate_include]
    rfl
  · rcases List.mem_cons.mp rest with same | last
    · subst equation
      rfl
    · have same := List.mem_singleton.mp last
      subst equation
      rfl

theorem actual_worklist_solves_frame_and_inference :
    pending (ContextualFrameWorklist.run 3 active (ContextualResidual.observeProblem problem)) = some 0 := by
  rw [ContextualFrameWorklist.run_eq_local_on_model 3 (ContextualResidual.observeProblem problem)
    active independentAnswer independent_model]
  decide +kernel

theorem physical_admission : ContextualGuardedStep.Requirements locals captures
    occupied selection nativeRule nativeRows nativeBefore nativeOutputs := by
  refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_⟩
  · unfold nativeRule nativeRows
    rw [ContextualRigidActivation.prepared_rule]
    rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [nativeBefore, ContextualRigidActivation.withFrame, state, selection, Selection.commit]
    · simp [nativeBefore, ContextualRigidActivation.withFrame, state, selection, Selection.commit]
    · simp [selection, Selection.commit, requestOccurrence, premiseOccurrence]
    · simp [nativeBefore, ContextualRigidActivation.withFrame, state, selection, Selection.commit,
        requestOccurrence, premiseOccurrence, outputOccurrence]
    · intro query member
      cases member
  · intro check member
    unfold nativeRule nativeRows at member
    rw [ContextualRigidActivation.prepared_rule] at member
    cases member

def prior : Board (InferenceScopedReturned.legacyBefore state) where
  entries := [(premiseOccurrence, a)]
  distinct := by simp
  occupied := by
    intro occurrence
    simp only [List.map_cons, List.map_nil, List.mem_singleton,
      InferenceScopedReturned.legacyBefore, OccurrenceRelabeling.configuration, state,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨Or.inr rfl, rfl⟩
    · rintro ⟨rfl | rfl, protectedHere⟩
      · cases protectedHere
      · rfl
  readback := by intro entry member; obtain rfl := List.mem_singleton.mp member; rfl
  supported := by intro entry member; obtain rfl := List.mem_singleton.mp member; rfl

/-- This actual receipt performs a genuine caller binding, retains the
off-query root inventories, and derives the protected conclusion from the
original selected source premise. -/
theorem actual_framed_execution :
    ∃ receipt : InferenceScopedExecution.Receipt definition locals captures,
      receipt.extraFrame = extra ∧ receipt.retained = retained ∧ receipt.templates = templates ∧
      receipt.capturedAnswer () =
        ContextualRigidActivation.into encode
          (ContextualComputedFreshFrame.active active receipt.update.declaration) readyB ∧
      receipt.capturedAnswer () ≠ generator
        (ContextualComputedFreshFrame.active active receipt.update.declaration) (.inl (.inr ())) ∧
      Nonempty (OpenDerivation definition [a] b) := by
  have closed := actual_worklist_solves_frame_and_inference
  cases computed : ContextualFrameWorklist.run 3 active (ContextualResidual.observeProblem problem) with
  | refuted impossible => simp only [computed, pending, reduceCtorEq] at closed
  | residual update =>
      have empty : update.remaining = [] := by
        simpa only [computed, pending, Option.some.injEq, List.length_eq_zero_iff] using closed
      let receipt : InferenceScopedExecution.Receipt definition locals captures := {
        id := ⟨"ab"⟩
        arguments := []
        readyRule := readyRule
        activated := actual_source_activates
        readyLabel := readyLabel
        state := state
        extraFrame := extra
        scopes := scopes
        oldLedger := ∅
        retained := retained
        templates := templates
        selection := selection
        fuel := 3
        update := update
        returned := ContextualTransportedActivation.from_run locals captures physical_admission update computed empty
        readback := canonical_readback }
      have solved := receipt.captured_answer_solves_external_frame
        (generator captures (), ContextualRigidActivation.into encode captures readyB)
        (List.mem_singleton_self _)
      have binding : receipt.capturedAnswer () =
          ContextualRigidActivation.into encode
            (ContextualComputedFreshFrame.active active receipt.update.declaration) readyB := by
        change instantiate receipt.capturedAnswer (generator captures ()) =
          instantiate receipt.capturedAnswer (Rigid.includeTerm captures (encode readyB)) at solved
        rw [instantiate_generator, Rigid.instantiate_include] at solved
        exact solved
      have nonidentity : receipt.capturedAnswer () ≠ generator
          (ContextualComputedFreshFrame.active active receipt.update.declaration) (.inl (.inr ())) := by
        rw [binding]
        intro same
        have operators := (Term.op.inj same).1
        cases operators
      let trace : SelectedRun definition (InferenceScopedReturned.legacyBefore state) [true]
          (InferenceScopedReturned.legacyAfter state readyRule selection) :=
        .cons receipt.firing (.nil _)
      have outputPresent : outputOccurrence ∈ (InferenceScopedReturned.legacyAfter state readyRule selection).present := by
        change outputOccurrence ∈ Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.fire
          _ (selection.commit (T := InferenceSchemaKernel.Value))
        apply Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.mem_fire.mpr
        right
        simp [selection, Selection.commit]
      exact ⟨receipt, rfl, rfl, rfl, binding, nonidentity,
        ⟨trace.derive prior outputOccurrence outputPresent rfl b rfl⟩⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceScopedFrameControls
