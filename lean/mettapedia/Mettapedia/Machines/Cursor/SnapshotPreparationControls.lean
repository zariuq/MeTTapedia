import Mettapedia.Machines.Cursor.SnapshotPreparation

/-!
# Controls for demand-driven snapshot preparation

Positive cases cover duplicate occurrences, stopped and resumed consumers,
empty demand, decoder accounting and retained entry snapshots. Negative cases
distinguish startup from delivery, answers from inspected rows, and the captured
array from a later store version. The large-size controls use general proved
laws rather than trusting an external evaluator for the result.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.SnapshotPreparationControls

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open SnapshotPreparation

abbrev Answers := fun (_ : Unit) (_ : Unit) => List (Option Nat)

def observer : Client (P := Sequence.protocol Nat) (Return := Answers) :=
  CoalgebraicPlans.retainedPlanRealizer

def onePull : (Sequence.protocol Nat).Free Answers () () :=
  Free.node (Sequence.protocol Nat) () fun first =>
    Free.pure (Sequence.protocol Nat) [first]

def twoPulls : (Sequence.protocol Nat).Free Answers () () :=
  Free.node (Sequence.protocol Nat) () fun first =>
    Free.node (Sequence.protocol Nat) () fun second =>
      Free.pure (Sequence.protocol Nat) [first, second]

def noPulls : (Sequence.protocol Nat).Free Answers () () :=
  Free.pure (Sequence.protocol Nat) []

def even (row : Nat) : Bool := row % 2 == 0

def observed (M : Provider (Sequence.protocol Nat)) :
    Outcome M observer () → Option (List (Option Nat))
  | .paused _ => none
  | .done result => some result.2.1

def nextOffset : Outcome (FilteredSnapshot.provider even id) observer () → Nat
  | .paused packet => packet.2.2.offset
  | .done result => result.2.2.offset

example : (retainedRun even id observer 2 onePull #[1, 4, 4, 9, 6]).1 = 2 := by decide

example : observed _ (retainedRun even id observer 2 onePull #[1, 4, 4, 9, 6]).2 =
    some [some 4] := by decide

example : nextOffset (retainedRun even id observer 2 onePull #[1, 4, 4, 9, 6]).2 =
    2 := by decide

example : (preparedRun even id observer 2 onePull #[1, 4, 4, 9, 6]).1 = 5 := by decide

example : observed _ (preparedRun even id observer 2 onePull #[1, 4, 4, 9, 6]).2 =
    some [some 4] := by decide

example : (retainedRun even id observer 1 noPulls #[1, 4, 4, 9, 6]).1 = 0 ∧
    observed _ (retainedRun even id observer 1 noPulls #[1, 4, 4, 9, 6]).2 = some [] := by decide

example : (preparedRun even id observer 1 noPulls #[1, 4, 4, 9, 6]).1 = 5 ∧
    observed _ (preparedRun even id observer 1 noPulls #[1, 4, 4, 9, 6]).2 = some [] := by decide

example : observed _ (retainedRun even id observer 1 onePull #[1, 4, 4, 9, 6]).2 =
    none := by decide

/-- The interrupted client resumes with the next duplicate occurrence. Its
three inspected rows include the rejected first row, without scanning it twice. -/
def resumed := resume (FilteredSnapshot.provider even id) observer
  (FilteredSnapshot.inspections even id) 2
  (retainedRun even id observer 1 twoPulls #[1, 4, 4, 9, 6])

example : resumed.1 = 3 ∧ observed _ resumed.2 = some [some 4, some 4] ∧
    nextOffset resumed.2 = 3 := by decide

example :
    (advance (FilteredSnapshot.provider even id) observer
      (FilteredSnapshot.decodings even id) 3
      ⟨(), twoPulls, FilteredSnapshot.start #[1, 4, 4, 9, 6]⟩).1 = 2 := by decide

/-- One returned answer may follow several rejected rows. -/
example : (retainedRun even id observer 2 onePull #[1, 3, 5, 8, 10]).1 = 4 ∧
    observed _ (retainedRun even id observer 2 onePull #[1, 3, 5, 8, 10]).2 =
      some [some 8] := by decide

/-- Exhaustion is a completed `none` reply, unlike scheduler suspension. -/
example : (retainedRun even id observer 2 onePull #[1, 3, 5]).1 = 3 ∧
    observed _ (retainedRun even id observer 2 onePull #[1, 3, 5]).2 =
      some [none] := by decide

example : (advance (FilteredSnapshot.provider even id) observer
    (FilteredSnapshot.decodings even id) 2
    ⟨(), onePull, FilteredSnapshot.start #[1, 3, 5]⟩).1 = 0 := by decide

example : observed _ (retainedRun even id observer 2 onePull #[]).2 =
    some [none] := by decide

/-- A later appended row does not enter the already captured snapshot. A new
reader does see it; replacing the old snapshot would change the second reply. -/
example : observed _ (retainedRun even id observer 3 twoPulls #[2]).2 =
    some [some 2, none] ∧
    observed _ (retainedRun even id observer 3 twoPulls (#[2].push 4)).2 =
      some [some 2, some 4] := by decide

example : (gather (fun _ : Nat => true) id (List.replicate 4096 7)).inspected =
    4096 := by rw [gather_inspections, List.length_replicate]

example :
    (FilteredSnapshot.search (fun _ : Nat => true) id
      (7 :: List.replicate 4095 7).toArray 0 (4095 + 1)).inspected = 1 := by
  have result := (first_match_work (fun _ : Nat => true) id 7
    (List.replicate 4095 7) rfl).2.1
  simpa only [List.length_replicate] using result

/-- No fixed startup allowance covers all eagerly prepared arrays, even for
this consumer which returns without asking the provider for an answer. -/
example (bound : Nat) : ∃ storage : Array Nat,
    bound < (preparedRun even id observer 1 noPulls storage).1 :=
  preparation_exceeds_any_bound even id observer 1 noPulls 7 bound

example : repeatPrepared even id #[2, 4, 6] 3 =
    (9, [some 2, some 2, some 2]) := by decide

example : repeatRetained even id #[2, 4, 6] 3 =
    (3, [some 2, some 2, some 2]) := by decide

/-- Reopening is different from continuing one reader. The repeated query
must return the first occurrence again; it may avoid gathering the tail. -/
example : (repeatRetained even id #[2, 4, 6] 2).2 ≠ [some 2, some 4] := by decide

#print axioms FilteredSnapshot.refinement
#print axioms FilteredSnapshot.advance_observation
#print axioms FilteredSnapshot.advance_conservation
#print axioms FilteredSnapshot.advance_decodings_exact
#print axioms FilteredSnapshot.resumed_inspections_le
#print axioms representation_observation
#print axioms retained_inspections_le_prepared
#print axioms preparation_exceeds_any_bound
#print axioms repeat_answers_agree
#print axioms repeated_first_match

end Mettapedia.Machines.Cursor.SnapshotPreparationControls
