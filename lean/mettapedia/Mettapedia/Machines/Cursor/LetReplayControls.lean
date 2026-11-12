import Mettapedia.Machines.Cursor.LetPlacement

/-!
# A minimal model of a guide which forgets its let result

There is one fixed atom match. Entry makes one guide for each produced let
result but stores only the common atom footprint, represented here by Unit.
Each such guide then runs the producer again and selects its first result.
The independently constructed retained-packet route uses the source producer
and its actual continuation. This isolates the lost-choice/replayed-effect
defect from any decision about transactional effect publication.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.LetReplayControls

open Mettapedia.Languages.MeTTa.PeTTa.LibTransform (Trace Search)
open LetPlacement (yieldOne)

variable {World Value : Type}

def forgottenGuides (code : Search World Value) : Search World Value := fun world =>
  let entry := (code world).drain
  let guides := entry.1.map (fun _ => ())
  ((Search.superpose guides).bind (fun _ => Search.once code)) entry.2

def retainedPackets (code : Search World Value) : Search World Value := fun world =>
  LetChoicePackets.fire (LetChoicePackets.capture id 0 (code world)) yieldOne

theorem bind_yield (trace : Trace World Value) : trace.bind yieldOne = trace := by
  induction trace with
  | done world => rfl
  | answer value world later ih =>
      simp only [Trace.bind, yieldOne, Trace.append]
      congr 1
      funext next
      exact ih next

/-- This is a proof about the actual packet constructor and firing route,
not a target defined to be the source computation. -/
theorem retained_is_ordinary_binding (code : Search World Value) :
    retainedPackets code = code := by
  funext world
  rw [retainedPackets, LetChoicePackets.fire_capture, bind_yield]

def touchThenChoose : Search Nat Nat := fun world =>
  .answer 10 (world + 1) (fun next => .answer 20 next .done)

theorem full_replay_witness :
    (forgottenGuides touchThenChoose 0).drain = ([10, 10], 3) ∧
      (retainedPackets touchThenChoose 0).drain = ([10, 20], 1) := by decide

theorem first_replay_witness :
    (Search.once (forgottenGuides touchThenChoose) 0).drain = ([10], 2) ∧
      (Search.once (retainedPackets touchThenChoose) 0).drain = ([10], 1) := by decide

theorem no_effect_is_needed_to_expose_lost_choice :
    (forgottenGuides (Search.superpose [10, 20]) (0 : Nat)).drain = ([10, 10], 0) ∧
      (retainedPackets (Search.superpose [10, 20]) 0).drain = ([10, 20], 0) := by decide

end Mettapedia.Machines.Cursor.LetReplayControls
