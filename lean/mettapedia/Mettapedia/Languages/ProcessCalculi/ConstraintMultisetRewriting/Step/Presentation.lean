import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationCore
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EffectStore

/-! # Store effects interpreted by the authored event interface -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

namespace StoreExample

open Interface
open AdmissionObservationCover.Controls (frame)
open EffectStoreControls (extra tell_prepared)

abbrev effect := EffectCore.tell frame () extra

def permission (permit : Bool) : effect.Admission := fun _ _ => permit = true

/-- This source fixture represents a real effect which adds a nontrivial constraint. -/
theorem event_iff (permit : Bool) :
    Nonempty (effect.Event (permission permit) [] extra) ↔ permit = true := by
  constructor
  · rintro ⟨e⟩
    exact e.permitted
  · intro allowed
    exact ⟨⟨(), tell_prepared, allowed, rfl⟩⟩

/-- Preservation and reflection for the independently defined store-effect example. -/
theorem execution_iff_event (permit : Bool) :
    atState (.apply "Finish" []) ∈ rewriteStepWithPremisesUsing (fixture permit) language
      (request (.apply "Start" []) (.apply "Move" [])) ↔
      Nonempty (effect.Event (permission permit) [] extra) := by
  rw [event_iff]
  cases permit
  · rw [prepared_without_permission]
    simp
  · rw [admitted_fixture]
    simp

/-- The generated modal observation agrees with that same semantic event. -/
theorem diamond_iff_event (permit : Bool) :
    langDiamondUsing (fixture permit) language
      (observation (fixture permit) (· = atState (.apply "Finish" [])))
      (request (.apply "Start" []) (.apply "Move" [])) ↔
      Nonempty (effect.Event (permission permit) [] extra) := by
  rw [diamond_reads]
  simpa using execution_iff_event permit

end StoreExample

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation
