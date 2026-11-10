import Mettapedia.Languages.MeTTa.PeTTa.LibTransform
import Mettapedia.Machines.StoreAndDemand.FirstAnswer

/-!
# The search-model consumer is an instance of first-answer demand

This adapter exposes an answer-delimited `LibTransform.Search` through the existing
cursor protocol. The successor stores its continuation without invoking it. The
first consumer agrees with `Search.once`, including the world left by an answerless
producer. One counted request here may encompass many internal search steps; it
does not assert constant matching work or a native fuel correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.StoreAndDemand.SearchCursor

open Mettapedia.Languages.MeTTa.PeTTa.LibTransform
open Mettapedia.Machines.Cursor
open Mettapedia.Machines.StoreAndDemand

variable {World Answer : Type}

structure State (World Answer : Type) where
  world : World
  continuation : Search World Answer

def next (state : State World Answer) : FirstAnswer.Reply Answer Empty × State World Answer :=
  match state.continuation state.world with
  | .done after => (.exhausted, ⟨after, .done⟩)
  | .answer value after continuation => (.answer value, ⟨after, continuation⟩)

def observe : FirstAnswer.Result Answer Empty → State World Answer → Option (List Answer × World)
  | .answer value, state => some ([value], state.world)
  | .exhausted, state => some ([], state.world)
  | .raised impossible, _ => nomatch impossible
  | .interrupted, _ => none

/-- The generic first consumer and the independent search consumer have the same observation. -/
theorem first_refines_once (producer : Search World Answer) (world : World) :
    ∃ result residual,
      advance (FirstAnswer.provider next) (FirstAnswer.client Answer Empty) (fun _ _ => 1) 2
        (FirstAnswer.start next ⟨world, producer⟩) = (1, .done ⟨(), result, residual⟩) ∧
      observe result residual = some ((Search.once producer world).drain) := by
  cases produced : producer world with
  | done after =>
      refine ⟨.exhausted, ⟨after, .done⟩, ?_, ?_⟩
      · exact FirstAnswer.exhaustion_stops next _ _ (by simp [next, produced])
      · simp [observe, Search.once, produced]
  | answer value after continuation =>
      refine ⟨.answer value, ⟨after, continuation⟩, ?_, ?_⟩
      · exact FirstAnswer.answer_stops next _ _ value (by simp [next, produced]) 0
      · simp [observe, Search.once, produced]

end Mettapedia.Languages.MeTTa.StoreAndDemand.SearchCursor
