import Mettapedia.Machines.Supercompilation.Driving

/-!
# Controls for guarded driving

The example has an authored order, a repeated successor, a loop, a late
input, an absent lookup, and a change of program authority.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Supercompilation.Controls

open ReadOnlyQuery

private abbrev StoreValue := Option (List Nat)

private def describe (revised : Bool) : Description Nat Nat StoreValue (List Nat)
  | 0 => if revised then .pure ⟨false, [6], []⟩ else
      .read 0 (fun choices => .pure ⟨false, choices.getD [4], []⟩)
  | 1 => .pure ⟨false, [1, 3], []⟩
  | 2 => .read 0 fun choices => .read 1 fun inputs =>
      .pure ⟨true, [], (choices.getD []).take 1 ++ inputs.getD []⟩
  | answer + 3 => .pure ⟨true, [], [answer + 3]⟩

private def original : Nat → StoreValue
  | 0 => some [1, 2, 1]
  | 1 => some [5]
  | _ => none

private def lateInput : Nat → StoreValue
  | 1 => some [11, 11]
  | key => original key

private def reordered : Nat → StoreValue
  | 0 => some [2, 1, 1]
  | key => original key

private def missing : Nat → StoreValue := fun _ => none

private def static (key : Nat) : Bool := key == 0

private def compiled := Graph.compile (describe false) static original 2 12 [0]

theorem loop_folds_and_repeats_survive :
    compiled.map Block.config = [2, 3, 1, 0] ∧
      (dispatch describe false compiled false original 0).answer.successors = [1, 2, 1] ∧
      (dispatch describe false compiled false original 1).answer.successors = [1, 3] := by
  decide +kernel

/-- Runtime input can change without rerunning the discharged lookup. The
result carries the semantic footprint in the source read order. -/
theorem live_suffix_is_executed :
    (compiled.lookup 2).map (fun residual => residual.reads) = some [(0, some [1, 2, 1])] ∧
      enter? describe false compiled false lateInput 2 =
        some ⟨⟨true, [], [1, 11, 11]⟩, [(0, some [1, 2, 1]), (1, some [11, 11])]⟩ := by
  exact ⟨rfl, rfl⟩

theorem same_bag_different_order_is_stale :
    ([1, 2, 1] : Multiset Nat) = ([2, 1, 1] : Multiset Nat) ∧
      enter? describe false compiled false reordered 0 = none ∧
      (dispatch describe false compiled false reordered 0).answer.successors = [2, 1, 1] := by
  decide +kernel

theorem equal_memory_cannot_authorize_other_program :
    enter? describe false compiled true original 0 = none ∧
      (dispatch describe false compiled true original 0).answer.successors = [6] := by
  decide +kernel

theorem filling_an_absence_invalidates :
    let absent := Graph.compile (describe false) static missing 2 1 [0]
    enter? describe false absent false missing 0 =
        some ⟨⟨false, [4], []⟩, [(0, none)]⟩ ∧
      enter? describe false absent false original 0 = none := by
  exact ⟨rfl, rfl⟩

/-- After a budget cut, fallback enters the source at the reached configuration. -/
theorem budget_cut_resumes_current_configuration :
    let onlyRoot := Graph.compile (describe false) static original 2 1 [0]
    let noReads := Graph.compile (describe false) static original 0 1 [0]
    enter? describe false onlyRoot false original 1 = none ∧
      (dispatch describe false onlyRoot false original 1).answer.successors = [1, 3] ∧
      (noReads.lookup 0).map (fun residual => residual.reads) = some [] ∧
      (dispatch describe false noReads false reordered 0).answer.successors = [2, 1, 1] := by
  decide +kernel

open ReadOnlySpecialization

/-- Each captured key must match the next source read. -/
theorem capture_rejects_wrong_key :
    restore [(1, some [5])] (describe false 2) = none := rfl

/-- A reconstructed read still needs a live value check. -/
theorem capture_still_checks_values :
    (restore [(0, some [2, 1, 1])] (describe false 0)).map
      (fun plan => plan.tryRun original) = some none := rfl

private def record : ScopedCommit.Body Nat (List Nat) :=
  .effect (fun state history => (state, history ++ [state])) .done

private def hostGuard (memory : Nat → StoreValue) : ScopedCommit.Body Nat (List Nat) :=
  OrderedGuardPipeline.guard
    (fun site => (dispatch describe false compiled false memory site).answer.successors) record

/-- A repeated occurrence consumes the existing continuation twice, and
rejection of a stale prefix starts from the incoming world. -/
theorem duplicate_effects_and_stale_order :
    ScopedCommit.run (hostGuard original) 0 [99] = ([1, 2, 1], [99, 1, 2, 1]) ∧
      ScopedCommit.run (hostGuard reordered) 0 [99] = ([2, 1, 1], [99, 2, 1, 1]) := by
  decide +kernel

theorem once_uses_the_live_order :
    ScopedCommit.run (ScopedCommit.once (hostGuard reordered)) 0 [99] = ([2], [99, 2]) := by
  decide +kernel

end Mettapedia.Machines.Supercompilation.Controls
