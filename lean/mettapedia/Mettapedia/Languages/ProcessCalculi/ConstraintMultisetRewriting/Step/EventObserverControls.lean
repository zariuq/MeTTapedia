import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventObserverLifting

/-! # Order and feedback boundaries for event observations

The one-state graph has two distinct generating events. It is a counterexample
to identifying events by endpoints, or commuting them for an order-sensitive
observer. The feedback graph deliberately reads its record to enable an edge;
it therefore fails the unique-lifting property of a passive observer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.EventObserver.Controls

inductive State where | ready

instance : Quiver State where
  Hom _ _ := Bool

def log : EventObserver State where
  Data _ := List Bool
  update event past := past ++ [event]

def first : @Quiver.Path State _ .ready .ready := .cons .nil true
def second : @Quiver.Path State _ .ready .ready := .cons .nil false

theorem equal_endpoints_distinct_events : first ≠ second := by
  intro same
  have outputs := congrArg (fun path => log.evaluate path []) same
  change [true] = [false] at outputs
  cases outputs

theorem event_order_observable :
    log.evaluate (first.comp second) [] ≠ log.evaluate (second.comp first) [] := by
  change ([true, false] : List Bool) ≠ [false, true]
  decide +kernel

theorem decorated_order_erases_exactly :
    log.forget.mapPath (log.decorate (first.comp second) []) = first.comp second :=
  log.forget_decorate _ _

theorem unique_ordered_record :
    ∃! lifted : Quiver.PathStar (⟨State.ready, []⟩ : log.Observed),
      log.forget.pathStar _ lifted = ⟨State.ready, first.comp second⟩ :=
  log.unique_lift _ _

/-- This graph reads the Boolean state: the first event disables itself. -/
structure FeedbackEdge (before after : Bool) where
  event : Bool
  allowed : event = true → before = false
  updated : after = (before || event)

instance : Quiver Bool where
  Hom := FeedbackEdge

def forgetFeedback : Bool ⥤q State where
  obj _ := .ready
  map edge := edge.event

theorem feedback_first_exists :
    ∃ edge : FeedbackEdge false true, edge.event = true :=
  ⟨⟨true, fun _ => rfl, rfl⟩, rfl⟩

theorem feedback_blocks_second :
    ¬∃ (after : Bool) (edge : FeedbackEdge true after), edge.event = true := by
  rintro ⟨_, edge, same⟩
  cases edge.allowed same

/-- Reading a record changes available events and invalidates passive erasure. -/
theorem feedback_is_not_surjective : ¬Function.Surjective (forgetFeedback.star true) := by
  intro onto
  obtain ⟨⟨after, edge⟩, mapped⟩ := onto ⟨State.ready, true⟩
  have event_eq := eq_of_heq (Sigma.mk.inj mapped).2
  exact feedback_blocks_second ⟨after, edge, event_eq⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.EventObserver.Controls
