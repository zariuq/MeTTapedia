import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceScopedNativePaths
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopedInferencePathControls

/-!
# A nonidentity caller refinement survives the entire native path

The existing executable receipt solves a caller equation outside the rigid
protected judgment. Its family-changing path retains that frame, the actual
selected premise and the complete helper ledger. Logical projection is a
separate observation of this full native result.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceScopedNativePathControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenApplicationControls (definition)
open ScopedInferenceValues (base encode)
open InferenceRequestExecution (Occurrence)
open InferenceScopedExecutionControls
  (locals captures active selection retained templates premiseOccurrence)
open InferenceScopedFrameControls (extra)
open ScopedInferencePathProjection

local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq (ScopedInferenceValues.Head × List Nat))

theorem an_actual_native_path_retains_the_nonidentity_frame :
    ∃ situated : Situated definition locals captures,
      ∃ path : Quiver.Path situated.native.endpoint situated.native.targetEndpoint,
        ContextualExecution.selections path = [selection] ∧
        ContextualExecution.fuels path = [3] ∧
        situated.native.targetEndpoint.inventory.configuration = situated.native.nativeAfter ∧
        situated.native.endpoint.inventory.configuration =
          ContextualRigidActivation.withFrame captures encode extra situated.native.state ∧
        situated.native.endpoint.inventory.retained = retained ∧
        situated.native.endpoint.inventory.templates = templates ∧
        situated.native.targetEndpoint.occupied = {37, 38, 39, 40, 41} ∧
        situated.native.capturedAnswer () ≠ generator
          (ContextualComputedFreshFrame.active active situated.native.update.declaration) (.inl (.inr ())) ∧
        ContextualFrameUnifier.Models (ContextualComputedFreshFrame.answer situated.native.update)
          situated.native.targetEndpoint.inventory.configuration.equations ∧
        situated.origin.instance_.ruleId = ⟨"ab"⟩ ∧ situated.origin.instance_.arguments = [] ∧
        ∃ port : Fin situated.origin.premises.length,
          port.val = 0 ∧ (situated.origin.readPosition situated.prior port).val = 0 ∧
            situated.origin.readOccurrence port = premiseOccurrence := by
  obtain ⟨situated, _source, _inputs, selected, fuel, frame, roots, stored, _occupied,
    ledger, _binding, nonidentity, _models, _projection, sourceId, sourceArgs, port, _node⟩ :=
      ScopedInferencePathControls.actual_framed_path
  refine ⟨situated, situated.native.nativePath, ?_, ?_, situated.native.native_target_is_full_result,
    ?_, roots, stored, ledger, nonidentity, situated.native.returned_answer_models_native_endpoint,
    sourceId, sourceArgs, port⟩
  · exact situated.native.native_path_selection_and_fuel.1.trans (congrArg List.singleton selected)
  · exact situated.native.native_path_selection_and_fuel.2.trans (congrArg List.singleton fuel)
  · exact situated.native.original_frame_equations_are_present.trans
      (congrArg (fun equations => ContextualRigidActivation.withFrame captures encode equations situated.native.state) frame)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceScopedNativePathControls
