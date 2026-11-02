import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopedInferencePathProjection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceScopedRefusalControls

/-!
# A real framed solver return reaches the path functor and its source node

The worklist solves a nonidentity caller binding, preserves the whole
native result and reserved helper inventory, and publishes through the
actual source rule with the selected protected premise position. Refusals
cover source origin, inputs and a public row proposed as a protected premise.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopedInferencePathControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenApplicationControls (a b definition)
open ContextualFrameUpdate
open ScopedInferenceValues (base encode)
open InferenceRequestExecution (label)
open InferenceJudgmentBoards InferenceTraceClassifying
open InferenceExecutionPaths InferencePathFunctor InferenceTracePaths
open ScopedInferencePathProjection
open InferenceScopedExecutionControls
  (locals captures active readyB readyRule actual_source_activates readyLabel state selection scopes retained templates
    nativeRule nativeRows nativeOutputs canonical_readback pending premiseOccurrence)
open InferenceScopedFrameControls
  (extra problem occupied prior physical_admission actual_worklist_solves_frame_and_inference
    off_query_scope_is_reserved actual_ports_and_helper_namespace_are_reserved)
open _root_.CategoryTheory

local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq (ScopedInferenceValues.Head × List Nat))

theorem actual_framed_path :
    ∃ situated : Situated definition locals captures,
      situated.native.id = ⟨"ab"⟩ ∧ situated.native.arguments = [] ∧
      situated.native.selection = selection ∧ situated.native.fuel = 3 ∧
      situated.native.extraFrame = extra ∧ situated.native.retained = retained ∧
      situated.native.templates = templates ∧ situated.native.occupied = {37} ∧
      ContextualFreshFrameScopeLedger.helperLedger
        (ContextualActivationScopes.after situated.native.occupied situated.native.selection) =
          {37, 38, 39, 40, 41} ∧
      situated.native.capturedAnswer () = ContextualRigidActivation.into encode
        (ContextualComputedFreshFrame.active active situated.native.update.declaration) readyB ∧
      situated.native.capturedAnswer () ≠ generator
        (ContextualComputedFreshFrame.active active situated.native.update.declaration) (.inl (.inr ())) ∧
      ContextualFrameUnifier.Models (ContextualComputedFreshFrame.answer situated.native.update)
        situated.native.nativeAfter.equations ∧
      (InferencePathFunctor.projection definition).map situated.path =
        (situated.native.projection situated.prior).2 ∧
      situated.origin.instance_.ruleId = ⟨"ab"⟩ ∧ situated.origin.instance_.arguments = [] ∧
      (∃ port : Fin situated.origin.premises.length,
        port.val = 0 ∧ (situated.origin.readPosition situated.prior port).val = 0 ∧
          situated.origin.readOccurrence port = premiseOccurrence) ∧
      (InferencePathFunctor.projection definition).map situated.path ≫
          eqToHom (situated.origin.board_context situated.prior) ≫
          ClassifyingContext.sndProjection (situated.prior.context definition)
            ⟨[situated.origin.conclusion]⟩ =
        OpenDerivationList.cons (.byRule situated.origin.instance_ situated.origin.application
          (situated.origin.picked situated.prior)) .nil := by
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
      let situated : Situated definition locals captures := ⟨receipt, prior⟩
      have solved := receipt.captured_answer_solves_external_frame
        (generator captures (), ContextualRigidActivation.into encode captures readyB) (List.mem_singleton_self _)
      have binding : receipt.capturedAnswer () = ContextualRigidActivation.into encode
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
      have onePort : situated.origin.premises.length = 1 := situated.origin.read_length
      let port : Fin situated.origin.premises.length := ⟨0, by rw [onePort]; decide⟩
      have positionZero : (situated.origin.readPosition situated.prior port).val = 0 := by
        have bound := (situated.origin.readPosition situated.prior port).isLt
        change (situated.origin.readPosition situated.prior port).val < 1 at bound
        omega
      refine ⟨situated, rfl, rfl, rfl, rfl, rfl, rfl, rfl, off_query_scope_is_reserved,
        actual_ports_and_helper_namespace_are_reserved.2, binding, nonidentity,
        receipt.returned_answer_models_native_result, situated.functor_is_actual_projection,
        situated.source_instance.1, situated.source_instance.2,
        ⟨port, rfl, positionZero, ?_⟩, situated.publishes_source_node⟩
      rfl

theorem no_path_receipt_with_unknown_origin (situated : Situated definition locals captures)
    (source : situated.native.id = ⟨"uninstalled"⟩) (inputs : situated.native.arguments = []) : False := by
  have activated := situated.native.activated
  rw [source, inputs] at activated
  have refused := InferenceScopedRefusalControls.unknown_source_refuses
  rw [activated] at refused
  cases refused

theorem no_path_receipt_with_wrong_inputs (situated : Situated definition locals captures)
    (source : situated.native.id = ⟨"ab"⟩) (inputs : situated.native.arguments = [a]) : False := by
  have activated := situated.native.activated
  rw [source, inputs] at activated
  have refused := InferenceScopedRefusalControls.wrong_input_vector_refuses
  rw [activated] at refused
  cases refused

theorem public_row_cannot_be_a_protected_premise
    (board : Board (InferenceScopedReturned.legacyBefore InferenceScopedRefusalControls.wrongState)) :
    (InferenceScopedRefusalControls.publicOccurrence, a) ∉ board.entries := by
  intro member
  have wrong := congrArg Prod.fst (board.readback _ member)
  cases wrong

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopedInferencePathControls
