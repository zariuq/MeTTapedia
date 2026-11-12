import Mettapedia.Machines.Cursor.StampedSnapshotsControls

/-!
# Reader schedules with exportable observations

The observations are computed by the stamped store and reader machine. A
renderer can consume them without obtaining expected answers from a runtime.
For unordered spaces, the relevant observer compares each reader's complete
entry bag rather than imposing an unpromised first-answer order.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ReaderScheduleFixtures

open StampedSnapshots

def values (events : List (Event Nat)) : List Nat :=
  (StampedSnapshots.Controls.outputs events).map Prod.snd

def liveValues (events : List (Event Nat)) : List Nat :=
  let store := (run (initial empty) events).1.store
  (snapshot store (start store)).filterMap (fun slot => slot.map Prod.snd)

def setup : List (Event Nat) := [.add 10, .add 20, .add 30]

def retained : List (Event Nat) := setup ++
  [.openReader 0, .read 0, .remove 1, .add 40, .read 0, .read 0, .read 0]

def churn : List (Event Nat) := setup ++
  [.openReader 0, .read 0, .remove 1, .add 40, .remove 2, .add 50,
    .read 0, .read 0, .read 0]

def duplicate (he : Bool) : List (Event Nat) :=
  [.add 7, .add 7, .add 9, .openReader 0, .read 0, .remove 0] ++
    (if he then [] else [.remove 1]) ++ [.add 11, .read 0, .read 0, .read 0]

def many (count : Nat) : List (Event Nat) := setup ++
  (List.range count).flatMap (fun id => [.openReader id, .read id]) ++
  [.remove 1, .add 40] ++
  (List.range count).flatMap (fun id => [.read id, .read id, .read id])

def nested : List (Event Nat) := setup ++
  [.openReader 0, .read 0, .remove 1, .add 40,
    .openReader 1, .read 1, .read 1, .read 1, .read 1, .close 1,
    .read 0, .read 0, .read 0]

def cancelled : List (Event Nat) := setup ++
  [.openReader 0, .read 0, .openReader 1, .read 1,
    .remove 1, .add 40, .close 0, .read 1, .read 1, .read 1]

structure Observation where
  first : List Nat
  later : List Nat
  live : List Nat
  deriving Repr, DecidableEq

def observation (firstCount : Nat) (events : List (Event Nat)) : Observation :=
  ⟨(values events).take firstCount, (values events).drop firstCount, liveValues events⟩

theorem retained_expected : observation 1 retained = ⟨[10], [20, 30], [10, 30, 40]⟩ := by decide
theorem churn_expected : observation 1 churn = ⟨[10], [20, 30], [10, 40, 50]⟩ := by decide
theorem duplicate_he_expected : observation 1 (duplicate true) = ⟨[7], [7, 9], [7, 9, 11]⟩ := by decide
theorem duplicate_petta_expected : observation 1 (duplicate false) = ⟨[7], [7, 9], [9, 11]⟩ := by decide
theorem many_eight_expected : observation 8 (many 8) =
    ⟨List.replicate 8 10, List.flatten (List.replicate 8 [20, 30]), [10, 30, 40]⟩ := by decide

def nestedObservation : Observation :=
  ⟨(values nested).take 1, (values nested).drop 4, ((values nested).drop 1).take 3⟩

theorem nested_expected : nestedObservation = ⟨[10], [20, 30], [10, 30, 40]⟩ := by decide
theorem cancelled_expected : observation 2 cancelled =
    ⟨[10, 10], [20, 30], [10, 30, 40]⟩ := by decide

def natList (xs : List Nat) : String :=
  "(" ++ String.intercalate " " (xs.map toString) ++ ")"

def render (tag : String) (value : Observation) : String :=
  "(" ++ tag ++ " " ++ natList value.first ++ " " ++ natList value.later ++ " " ++
    natList value.live ++ ")"

def exports : List (String × String) :=
  [("retained", render "rr-retained" (observation 1 retained)),
   ("churn", render "rr-churn" (observation 1 churn)),
   ("duplicate-he", render "rr-duplicate" (observation 1 (duplicate true))),
   ("duplicate-petta", render "rr-duplicate" (observation 1 (duplicate false))),
   ("many-eight", render "rr-many" (observation 8 (many 8))),
   ("nested", render "rr-nested" nestedObservation),
   ("cancel", render "rr-cancel" (observation 2 cancelled))]

def exportLines : List String := exports.map fun (name, expected) => name ++ "\t" ++ expected

def prefixStore (count retired : Nat) : Store Nat :=
  ⟨retired, count, fun id => if id < count then
    some ⟨id + 1, 0, if id < retired then some (id + 1) else none⟩ else none⟩

def livePayloads (store : Store Nat) : List Nat :=
  (snapshot store (start store)).filterMap (fun slot => slot.map Prod.snd)

theorem initial_payloads (count : Nat) :
    livePayloads (prefixStore count 0) = (List.range count).map (· + 1) := by
  have cells : snapshot (prefixStore count 0) (start (prefixStore count 0)) =
      (List.range count).map (fun id => some (id, id + 1)) := by
    apply List.map_congr_left
    intro id member
    have within : id < count := by simpa [start, prefixStore] using List.mem_range.mp member
    simp [start, prefixStore, atTime, visible, within]
  simp only [livePayloads, cells, List.filterMap_map, Function.comp_def, Option.map_some]
  simp

theorem first_cardinality (count : Nat) (nonempty : 0 < count) :
    ((livePayloads (prefixStore count 0)).take 1).length = 1 := by
  rw [initial_payloads]
  simp only [List.length_take, List.length_map, List.length_range]
  omega

theorem first_marker (count : Nat) (nonempty : 0 < count) :
    ((livePayloads (prefixStore count 0)).take 1).map (fun _ => "x") = ["x"] := by
  rw [List.map_const', first_cardinality count nonempty]
  rfl

theorem retire_next (count retired : Nat) (available : retired < count) :
    remove (prefixStore count retired) retired = prefixStore count (retired + 1) := by
  simp only [remove, prefixStore, if_pos available, Nat.lt_irrefl, if_false]
  congr 1
  funext id
  by_cases same : id = retired
  · subst id
    simp [Function.update, available]
  · have before : id < retired + 1 ↔ id < retired := by omega
    simp [Function.update_of_ne same, before]

def retirePrefix (count : Nat) : Nat → Store Nat
  | 0 => prefixStore count 0
  | retired + 1 => remove (retirePrefix count retired) retired

theorem retirePrefix_eq (count retired : Nat) (within : retired ≤ count) :
    retirePrefix count retired = prefixStore count retired := by
  induction retired with
  | zero => rfl
  | succ retired ih =>
      rw [retirePrefix, ih (by omega), retire_next count retired (by omega)]

theorem all_retired_payloads (count : Nat) :
    livePayloads (retirePrefix count count) = [] := by
  rw [retirePrefix_eq count count le_rfl]
  have cells : snapshot (prefixStore count count) (start (prefixStore count count)) =
      (List.range count).map (fun _ => (none : Option (Nat × Nat))) := by
    apply List.map_congr_left
    intro id member
    have within : id < count := by simpa [start, prefixStore] using List.mem_range.mp member
    simp [start, prefixStore, atTime, visible, within, show ¬ count < id + 1 by omega]
  simp [livePayloads, cells]

theorem drain_cardinalities (count : Nat) :
    (livePayloads (prefixStore count 0)).length = count ∧
      (retirePrefix count count).clock = count ∧
      (livePayloads (retirePrefix count count)).length = 0 := by
  rw [initial_payloads, retirePrefix_eq count count le_rfl]
  have empty := all_retired_payloads count
  rw [retirePrefix_eq count count le_rfl] at empty
  simp only [List.length_map, List.length_range]
  exact ⟨trivial, rfl, by rw [empty]; rfl⟩

def boundaryWrittenStore (count : Nat) : Store Nat :=
  add (remove (prefixStore count 0) 1) (count + 1)

theorem boundary_old_view (count : Nat) :
    snapshot (boundaryWrittenStore count) (start (prefixStore count 0)) =
      snapshot (prefixStore count 0) (start (prefixStore count 0)) := by
  have admissible : Admissible (prefixStore count 0) (start (prefixStore count 0)) :=
    ⟨le_rfl, le_rfl⟩
  rw [boundaryWrittenStore,
    snapshot_add _ _ _ (admissible_remove _ 1 _ admissible), snapshot_remove _ 1 _ admissible]

def boundaryRetainedObservation (count : Nat) : Observation :=
  let before := prefixStore count 0
  let after := boundaryWrittenStore count
  let held := (snapshot after (start before)).filterMap (fun slot => slot.map Prod.snd)
  ⟨held.take 1, held.drop 1, livePayloads after⟩

theorem boundary_retained_bag (count : Nat) :
    (boundaryRetainedObservation count).first ++ (boundaryRetainedObservation count).later =
      (List.range count).map (· + 1) := by
  simp only [boundaryRetainedObservation, List.take_append_drop]
  rw [boundary_old_view]
  exact initial_payloads count

theorem boundary_written_payloads (count : Nat) (large : 1 < count) :
    livePayloads (boundaryWrittenStore count) =
      (List.range count).filterMap (fun id => if id = 1 then none else some (id + 1)) ++
        [count + 1] := by
  have after : boundaryWrittenStore count =
      ⟨2, count + 1, Function.update
        (Function.update (prefixStore count 0).row 1 (some ⟨2, 0, some 1⟩))
        count (some ⟨count + 1, 2, none⟩)⟩ := by
    simp [boundaryWrittenStore, add, remove, prefixStore, large]
  have lookup (id : Nat) :
      (atTime (boundaryWrittenStore count) (boundaryWrittenStore count).clock id).map Prod.snd =
        if id = count then some (count + 1) else if id = 1 then none else
          if id < count then some (id + 1) else none := by
    by_cases newest : id = count
    · subst id
      simp [after, atTime, Function.update, visible]
    · by_cases removed : id = 1
      · subst id
        simp [after, atTime, Function.update, visible, newest]
      · by_cases within : id < count <;>
          simp [after, atTime, Function.update, visible, prefixStore, newest, removed, within]
  simp only [livePayloads, snapshot, start, List.filterMap_map, Function.comp_def, lookup]
  have ceiling : (boundaryWrittenStore count).next = count + 1 := by rw [after]
  rw [ceiling, List.range_succ, List.filterMap_append]
  simp only [List.filterMap_cons, List.filterMap_nil, ↓reduceIte]
  congr 1
  apply List.filterMap_congr
  intro id member
  have within := List.mem_range.mp member
  simp [show id ≠ count by omega, within]

def boundaryLines : List String := [4095, 4096, 4097].flatMap fun count =>
  ["first-" ++ toString count ++ "\t(rr-first " ++ toString count ++ " (x) " ++
      toString count ++ ")",
   "drain-" ++ toString count ++ "\t(rr-drain " ++ toString count ++ " 0)"]

def retainedBoundaryLines : List String := [4095, 4096, 4097].map fun count =>
  "retained-large-" ++ toString count ++ "\t" ++
    render "rr-retained-large" (boundaryRetainedObservation count)

#eval for line in exportLines ++ boundaryLines ++ retainedBoundaryLines do IO.println line
#print axioms retained_expected
#print axioms churn_expected
#print axioms duplicate_he_expected
#print axioms duplicate_petta_expected
#print axioms many_eight_expected
#print axioms first_cardinality
#print axioms first_marker
#print axioms drain_cardinalities
#print axioms boundary_written_payloads

end Mettapedia.Machines.Cursor.ReaderScheduleFixtures
