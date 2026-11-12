import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RepresentedEffects
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PreparedPublicationsControls

/-!
# A record consulted by execution is operational state

Both first labels perform the existing genuine store update and produce
their corresponding records. The next firing consults that record. At the
same underlying store one history permits a false label and the other refuses
it. Consequently no permission predicate on the underlying store alone can
describe this controller. Preparation remains available after refusal.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.EventFeedbackControls

open Presentation.Controls
open PublicationTransportControls

abbrev P := program permissive

structure RecordedState where
  world : Store
  past : List Bool

def represented : P.effectCore.Representation RecordedState (fun _ => Bool) where
  state s := s.world
  firing label := label
  preparedResult {s} label prepared :=
    ⟨P.effectCore.preparedResult label prepared, s.past ++ [label]⟩
  result_eq _ _ := rfl

def allowed {s : RecordedState} (label : Bool) : Prop :=
  s.past = [] ∨ label = s.past.getLastD false

def controller : Step frame Nat RecordedState (fun _ => Bool) :=
  Spaces.restrict (P.represent represented) (fun {s} label => allowed (s := s) label)

def start : RecordedState := ⟨[], []⟩
def after (label : Bool) : RecordedState := ⟨[(true, false)], [label]⟩

theorem first_admitted (label : Bool) : controller.Admits (s := start) label :=
  ⟨⟨prepares [] (), trivial⟩, Or.inl rfl⟩

theorem first_result (label : Bool) : controller.result label (first_admitted label) = after label := rfl

def first_event (label : Bool) : controller.effectCore.Event controller.eventAdmission start (after label) :=
  controller.event label (first_admitted label)

theorem same_world : (after false).world = (after true).world := rfl

theorem false_allowed_after_false : controller.Admits (s := after false) false :=
  ⟨⟨prepares _ (), trivial⟩, Or.inr rfl⟩

theorem false_refused_after_true : ¬ controller.Admits (s := after true) false := by
  rintro ⟨_, permitted⟩
  rcases permitted with empty | last
  · cases empty
  · exact Bool.false_ne_true last

theorem refusal_retains_preparation : controller.Prepares (s := after true) false :=
  prepares _ ()

theorem record_is_execution_state :
    ¬ ∃ permission : Store → Bool → Prop,
      ∀ (s : RecordedState) (label : Bool), controller.Admits (s := s) label ↔ permission s.world label := by
  rintro ⟨permission, agrees⟩
  have permitted := (agrees (after false) false).mp false_allowed_after_false
  exact false_refused_after_true ((agrees (after true) false).mpr permitted)

/-- The records in the separating states are exactly the passive records of
the corresponding first base events, before execution reads them. -/
def observer : EventObserver (EffectCore.EventObject P.effectCore P.eventAdmission) where
  Data _ := List Bool
  update event record := record ++ [event.firing]

def base_event (label : Bool) : P.effectCore.Event P.eventAdmission [] [(true, false)] :=
  P.event label ⟨prepares [] (), trivial⟩

theorem recorded_from_actual_event (label : Bool) :
    observer.evaluate ((Quiver.Path.nil).cons (base_event label)) [] = (after label).past := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.EventFeedbackControls
