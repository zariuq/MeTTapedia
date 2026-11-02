import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPathModelRestriction
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceScopedNativePaths
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopedInferencePathControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPathSnapshotControls

/-!
# Actual final answers restrict to nonempty prefixes, without temporal reflection

The positive control uses the actual nonidentity framed inference answer and
its nonempty caller equation prefix. The negative control keeps the old
snapshot's rows and physical world fixed: a later tell still forbids blanket
reflection of asks justified by the actual final equations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPathModelControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualExecution

namespace Framed

open Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenApplicationControls (definition)
open ScopedInferenceValues (base)
open InferenceScopedExecutionControls (locals captures active)
open InferenceScopedFrameControls (extra)

local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq (ScopedInferenceValues.Head × List Nat))

theorem the_actual_answer_restricts_to_the_nonempty_caller_prefix :
    ∃ receipt : InferenceScopedExecution.Receipt definition locals captures,
      receipt.fuel = 3 ∧ receipt.extraFrame = extra ∧
      receipt.endpoint.inventory.configuration.equations ≠ [] ∧
      ContextualFrameUnifier.Models (ContextualComputedFreshFrame.answer receipt.update)
        receipt.targetEndpoint.inventory.configuration.equations ∧
      ContextualFrameUnifier.Models
        (Assignment.compose (ContextualComputedFreshFrame.answer receipt.update) (pathAssignment receipt.nativePath))
        receipt.endpoint.inventory.configuration.equations ∧
      ContextualFrameUnifier.Models (ContextualComputedFreshFrame.answer receipt.update)
        (prefixSnapshot receipt.nativePath).configuration.equations ∧
      receipt.capturedAnswer () ≠ generator
        (ContextualComputedFreshFrame.active active receipt.update.declaration) (.inl (.inr ())) := by
  obtain ⟨situated, _source, _inputs, _selected, fuel, frame, _roots, _templates, _occupied,
    _ledger, _binding, nonidentity, _models, _projection, _sourceId, _sourceArgs, _port, _node⟩ :=
      ScopedInferencePathControls.actual_framed_path
  let receipt := situated.native
  have finalModel := receipt.returned_answer_models_native_endpoint
  refine ⟨receipt, fuel, frame, ?_, finalModel,
    models_restrict_to_prefix receipt.nativePath _ finalModel,
    final_model_satisfies_prefixSnapshot receipt.nativePath _ finalModel, nonidentity⟩
  intro empty
  change receipt.extraFrame ++ _ = [] at empty
  have frameEmpty := (List.append_eq_nil_iff.mp empty).1
  rw [frame] at frameEmpty
  cases frameEmpty

end Framed

namespace FutureTell

open ContextualSelectionViews.Controls (base locals captures)
open ContextualGuardedExecutionControls (initial)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)
local instance : Quiver (Endpoint locals Nat [] ()) := ContextualExecution.graph locals Nat

theorem actual_final_equations_cannot_reflect_all_prefix_asks :
    ¬ ∀ (target : Endpoint locals Nat [] ()) (path : Quiver.Path initial target)
      (check : Check (Term (signature base captures) [] ())),
      ContextualGuardSemantics.Ask locals target.inventory.configuration.equations
        (prefixSnapshot path).rows (prefixSnapshot path).configuration.present
        (check.map (instantiate (pathAssignment path))) →
      ContextualGuardSemantics.Ask locals (prefixSnapshot path).configuration.equations
        (prefixSnapshot path).rows (prefixSnapshot path).configuration.present
        (check.map (instantiate (pathAssignment path))) := by
  intro reflects
  obtain ⟨target, _firing, _rule, _selection, path, _actualPath, _selected, earlierRefused, laterEntailed⟩ :=
    ContextualPathSnapshotControls.actual_later_tell_does_not_discharge_the_retained_prefix_question
  apply earlierRefused
  apply reflects target path _
  intro Future future candidate model
  exact laterEntailed Future future candidate model

end FutureTell

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPathModelControls
