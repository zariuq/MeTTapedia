import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopedInferenceValues

/-! # Scope, routing and binder preservation of physical inference encoding -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopedInferenceValueControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.GSLT.LanguageDef
open InferenceSchemaActivation (Tm)
open InferenceSchemaKernel (Value)
open ScopedInferenceValues

def boundPayload : Tm := .node (.inr "binder") (.cons 1 (.idx 0) .nil)
def loosePayload : Tm := .node (.inr "binder") (.cons 0 (.idx 0) .nil)
def boundValue : Value := (.judgments, boundPayload)
def boundReady : Ready := ⟨boundValue, rfl⟩
def publicReady : Ready := ⟨(.requests, boundPayload), rfl⟩

theorem scoped_binder_is_admitted : checkScope? boundValue = some boundReady := rfl
theorem loose_index_is_refused : checkScope? (.judgments, loosePayload) = none := rfl
theorem bare_loose_index_is_refused : checkScope? (.requests, .idx 0) = none := rfl

/-- The intrinsic presentation preserves the actual binding field and
index; it does not replace them with opaque data constants. -/
theorem binder_readback_is_exact : CommonABT.Presentation.erase (encode boundReady) =
    .node (.inl .judgments) (.cons 0
      (.node (.inr (.inr "binder")) (.cons 1 (.idx 0) .nil)) .nil) :=
  CommonABT.Presentation.erase_read _ _ _

theorem equal_payload_does_not_erase_physical_space : encode boundReady ≠ encode publicReady := by
  intro same
  have locations := congrArg (fun value : Ready => value.val.1) (encode_injective same)
  cases locations

theorem contextual_assignment_cannot_capture_its_bound_index
    {V W : Type} {source : V → MetaArity base} {target : W → MetaArity base}
    (assignment : Assignment source target) :
    instantiate assignment (into source boundReady) = into target boundReady :=
  instantiate_into assignment boundReady

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopedInferenceValueControls
