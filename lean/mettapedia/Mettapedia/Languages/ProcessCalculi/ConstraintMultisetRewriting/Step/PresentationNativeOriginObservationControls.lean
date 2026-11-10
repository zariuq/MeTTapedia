import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationNativeOriginObservation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationNativeOriginControls

/-! # A native template event with two observable authorized origins -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.NativeOriginControls

open Interface NativeOrigins ContextualConditionalTemplateControls

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq Operation)

def permitsAliases (firing : NativeFiring originState) :
    (state : NativeState base Nat [] ()) → Nat → NativeFiring state → Prop :=
  fun _ key candidate => key < 2 ∧ HEq candidate firing

theorem actual_origin_record_separation (fuel : Nat) :
    ∃ (firing : NativeFiring originState) (admitted : firing.Realized),
      ¬ ∃ update : nativeStep.effectCore.Event nativeStep.eventAdmission originState
          (nativeStep.result firing admitted) → List Nat,
        ∀ edge : SourceEvent (catalogueAt firing.rule) (permitsAliases firing) originState
            (nativeStep.result firing admitted),
          update (edge.erase _ _) =
            (referenceObserver (catalogueAt firing.rule) (permitsAliases firing)).update
              (s := ⟨originState⟩) (t := ⟨nativeStep.result firing admitted⟩) edge [] := by
  obtain ⟨firing, _, admitted, _, _, _, _, _, _, _, _⟩ :=
    PublicationControls.native_result_depends_on_recipes fuel
  refine ⟨firing, admitted, ?_⟩
  exact origin_observer_cannot_descend (catalogueAt firing.rule) (permitsAliases firing) (first := 0) (second := 1)
    (by decide) (nativeStep.event firing admitted)
    (lookup_alias firing.rule 0 (by decide)) (lookup_alias firing.rule 1 (by decide))
    ⟨by decide, HEq.rfl⟩ ⟨by decide, HEq.rfl⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.NativeOriginControls
