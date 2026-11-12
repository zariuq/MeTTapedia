import Mettapedia.Machines.QueryState
import Mettapedia.Machines.Cursor.StatefulQueryRun

/-!
# Ordered partial row selection with retained effects

The reference visits a snapshot's rows in order and threads the actual world
through each partial test. An error retains the reached world and ends the
scan. The target uses the existing adaptive-query syntax and cursor, with
reversed accumulators and one request per visited row. Neither publishes a
removal. A caller may publish a completed selection under its own dependency
contract; a scheduler pause or test error is not a completed negative match.

This is a generic selection protocol. A test is one total protocol transition;
its internal suspension, error and fuel observations must be explicit replies.
It does not assign a unit runtime cost to arbitrary unification or callbacks.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.EffectfulRowSelection

open ReadOnlyQuery (Program)

variable {Row Error World : Type}

abbrev Decision (Error : Type) := Except Error Bool
abbrev Result (Row Error : Type) := Except (Nat × Error) (List Row × List Row)
abbrev Service (Row Error World : Type) := World → Nat × Row → Decision Error × World

def prepend (kept taken : List Row) : Result Row Error → Result Row Error :=
  Except.map fun selected => (kept ++ selected.1, taken ++ selected.2)

def reference (test : Service Row Error World) : Nat → List Row → World →
    QueryState.Observation (Nat × Row) (Decision Error) (Result Row Error) World
  | _, [], world => ⟨.ok ([], []), world, []⟩
  | use, row :: rest, world =>
      let tested := test world (use, row)
      match tested.1 with
      | .error reason => ⟨.error (use, reason), tested.2, [((use, row), tested.1)]⟩
      | .ok selected =>
          let later := reference test (use + 1) rest tested.2
          let result := if selected then prepend [] [row] later.answer else prepend [row] [] later.answer
          ⟨result, later.state, ((use, row), tested.1) :: later.reads⟩

def loop (use : Nat) (rows keptRev takenRev : List Row) :
    Program (Nat × Row) (Decision Error) (Result Row Error) :=
  match rows with
  | [] => .pure (.ok (keptRev.reverse, takenRev.reverse))
  | row :: rest => .read (use, row) fun tested =>
      match tested with
      | .error reason => .pure (.error (use, reason))
      | .ok selected =>
          if selected then loop (use + 1) rest keptRev (row :: takenRev)
          else loop (use + 1) rest (row :: keptRev) takenRev

def program (use : Nat) (rows : List Row) : Program (Nat × Row) (Decision Error) (Result Row Error) :=
  loop use rows [] []

theorem loop_refines (test : Service Row Error World) (use : Nat) (rows : List Row)
    (keptRev takenRev : List Row) (world : World) :
    QueryState.run test (loop use rows keptRev takenRev) world =
      let observed := reference test use rows world
      ⟨prepend keptRev.reverse takenRev.reverse observed.answer, observed.state, observed.reads⟩ := by
  induction rows generalizing use keptRev takenRev world with
  | nil => simp [loop, QueryState.run, reference, prepend, Except.map]
  | cons row rest ih =>
      cases tested : test world (use, row) with
      | mk decision reached =>
          cases decision with
          | error reason => simp [loop, QueryState.run, reference, tested, prepend, Except.map]
          | ok selected =>
              cases answer : (reference test (use + 1) rest reached).answer <;> cases selected <;>
                simp [loop, QueryState.run, reference, tested, ih, prepend, List.reverse_cons,
                  List.append_assoc, Except.map, answer]

theorem program_refines (test : Service Row Error World) (use : Nat) (rows : List Row) (world : World) :
    QueryState.run test (program use rows) world = reference test use rows world := by
  rw [program, loop_refines]
  generalize reference test use rows world = observed
  rcases observed with ⟨answer, reached, reads⟩
  cases answer <;> simp [prepend, Except.map]

theorem reference_visits_at_most (test : Service Row Error World) (use : Nat)
    (rows : List Row) (world : World) :
    (reference test use rows world).reads.length ≤ rows.length := by
  induction rows generalizing use world with
  | nil => simp [reference]
  | cons row rest ih =>
      cases tested : test world (use, row) with
      | mk decision reached =>
          cases decision with
          | error reason => simp [reference, tested]
          | ok selected => simpa [reference, tested] using Nat.succ_le_succ (ih (use + 1) reached)

theorem error_retains_test_world (test : Service Row Error World) (use : Nat)
    (row : Row) (rest : List Row) (world reached : World) (reason : Error)
    (failed : test world (use, row) = (.error reason, reached)) :
    reference test use (row :: rest) world =
      ⟨.error (use, reason), reached, [((use, row), .error reason)]⟩ := by
  simp [reference, failed]

theorem reference_state_invariant (test : Service Row Error World) (invariant : World → Prop)
    (closed : ∀ world, invariant world → ∀ key, invariant (test world key).2)
    (use : Nat) (rows : List Row) (world : World) (initial : invariant world) :
    invariant (reference test use rows world).state := by
  rw [← program_refines test use rows world]
  exact QueryState.state_invariant test invariant closed _ world initial

open Cursor.ReadOnlyQuery

theorem cursor_reference (test : Service Row Error World) (price : Nat × Row → Nat)
    (use : Nat) (rows : List Row) (world : World) :
    let observed := reference test use rows world
    let executed := Sampled.advance test price (observed.reads.length + 1)
      (program use rows) world []
    Sampled.completed? test executed.2 = some ⟨observed.answer, observed.reads⟩ ∧
      (Sampled.savedState test executed.2).1 = observed.state ∧
      executed.1 = Cursor.StatefulQueryRun.invoice price observed.reads := by
  have same := Cursor.StatefulQueryRun.completed_answer test price (program use rows) world
  simpa only [program_refines] using same

theorem cursor_row_budget (test : Service Row Error World) (price : Nat × Row → Nat)
    (use : Nat) (rows : List Row) (world : World) :
    let observed := reference test use rows world
    Sampled.advance test price (rows.length + 1) (program use rows) world [] =
      (Cursor.StatefulQueryRun.invoice price observed.reads,
        .done ⟨PUnit.unit, observed.answer, observed.state, observed.reads.reverse⟩) := by
  have bounded : (QueryState.run test (program use rows) world).reads.length + 1 ≤ rows.length + 1 := by
    rw [program_refines]
    exact Nat.succ_le_succ (reference_visits_at_most test use rows world)
  have same := Cursor.StatefulQueryRun.completed_above test price (program use rows) world []
    (rows.length + 1) bounded
  simpa only [program_refines, List.append_nil] using same

/-- The common cursor owns the pending row request and accumulated decisions.
Resumption does not re-enter the program at its original list head. -/
theorem split_without_replay (test : Service Row Error World) (price : Nat × Row → Nat)
    (first second use : Nat) (rows : List Row) (world : World) :
    Sampled.advance test price (first + second) (program use rows) world [] =
      Sampled.resume test price second
        (Sampled.advance test price first (program use rows) world []) :=
  Cursor.advance_add (Sampled.provider test) client (Sampled.charge test price) first second _

namespace Controls

def record (world : List Nat) (key : Nat × Nat) : Decision String × List Nat :=
  (if key.2 = 3 then .error "interrupted-test" else .ok (key.2 % 2 == 0), world ++ [key.2])

theorem effects_before_error_are_retained :
    (reference record 10 [1, 2, 3, 4] []).answer = .error (12, "interrupted-test") ∧
      (reference record 10 [1, 2, 3, 4] []).state = [1, 2, 3] ∧
      (reference record 10 [1, 2, 3, 4] []).reads.length = 3 := by decide

def paused := Sampled.advance record (fun _ => 1) 2 (program 10 [1, 2, 3, 4]) [] []
def finished := Sampled.resume record (fun _ => 1) 2 paused

theorem pause_is_not_a_completed_negative :
    Sampled.completed? record paused.2 = none ∧
      (Sampled.savedState record paused.2).1 = [1, 2] := by decide

theorem resume_keeps_prior_effects_once :
    (Sampled.completed? record finished.2).map (fun value => value.answer) =
      some (.error (12, "interrupted-test")) ∧
      (Sampled.savedState record finished.2).1 = [1, 2, 3] ∧ finished.1 = 3 := by decide

theorem restarting_repeats_effects :
    (reference record 10 [1, 2, 3, 4] (Sampled.savedState record paused.2).1).state =
      [1, 2, 1, 2, 3] := by decide

def changesDecision (world : Nat) (_ : Nat × Nat) : Decision String × Nat :=
  (.ok (world == 0), world + 1)

theorem rechecking_can_change_selection_and_repeat_effects :
    (reference changesDecision 0 [7] 0).answer = .ok ([], [7]) ∧
      (reference changesDecision 0 [7] (reference changesDecision 0 [7] 0).state).answer =
        .ok ([7], []) ∧
      (reference changesDecision 0 [7] (reference changesDecision 0 [7] 0).state).state = 2 := by decide

end Controls

end Mettapedia.Machines.EffectfulRowSelection
