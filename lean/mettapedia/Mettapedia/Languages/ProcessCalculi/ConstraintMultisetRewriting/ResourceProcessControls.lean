import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResourceProcess

/-!
# Source-execution controls for the resource factorization

These controls exercise the original selected firing relation, including
aliased reads, distinct produced occurrences, double consumption and a causal
cycle that cannot bootstrap itself. Separate controls show why equality of
partial resource operators is weaker than history or process equivalence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResourceProcessControls

open ConditionalSchedule ResourceProcess
open ResourceOccupation

def action : SubstitutionAction Unit Unit where
  E := Eq
  equivalence := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩
  apply _ term := term
  identity := ()
  compose _ _ := ()
  apply_identity _ := rfl
  apply_compose _ _ _ := rfl
  preserves _ _ _ same := same

def label (_ : Nat) : Unit := ()

def event (taken read made : List Nat) : Firing Unit Nat :=
  (⟨taken.map label, read.map label, [], [], made.map label⟩, ⟨taken, read, made⟩)

def state (world : Finset Nat) : Configuration Unit Nat := ⟨[], world⟩

theorem every_unit_store_has_a_model (equations : EquationStore Unit) : action.Consistent equations := by
  refine ⟨(), ?_⟩
  rintro ⟨⟨⟩, ⟨⟩⟩ _member
  rfl

theorem two_read_ports_really_execute_on_one_row :
    Executable action label (state {7}) [event [] [7, 7] []] := by
  apply (executable_iff_operator action label _ _ (by simp [CheckFree, event])).mpr
  refine ⟨by simp [Shapes, PortShape, event], by simp [LocallyFresh, event], ?_,
    every_unit_store_has_a_model _⟩
  decide

theorem two_take_ports_cannot_execute_on_one_row :
    ¬ Executable action label (state {7}) [event [7, 7] [] []] := by
  intro executes
  have resource := (executable_iff_operator action label _ _
    (by simp [CheckFree, event])).mp executes |>.2.2.1
  contradiction

theorem the_same_row_cannot_be_taken_and_read :
    ¬ Executable action label (state {7}) [event [7] [7] []] := by
  intro executes
  have resource := (executable_iff_operator action label _ _
    (by simp [CheckFree, event])).mp executes |>.2.2.1
  contradiction

theorem production_then_aliased_read_then_consumption_executes :
    Executable action label (state ∅)
      [event [] [] [7], event [] [7, 7] [], event [7] [] []] := by
  apply (executable_iff_operator action label _ _ (by simp [CheckFree, event])).mpr
  refine ⟨by simp [Shapes, PortShape, event], by simp [LocallyFresh, event], ?_,
    every_unit_store_has_a_model _⟩
  decide

theorem read_before_take_executes :
    Executable action label (state {7}) [event [] [7] [], event [7] [] []] := by
  apply (executable_iff_operator action label _ _ (by simp [CheckFree, event])).mpr
  refine ⟨by simp [Shapes, PortShape, event], by simp [LocallyFresh, event], ?_,
    every_unit_store_has_a_model _⟩
  decide

theorem take_before_read_refuses :
    ¬ Executable action label (state {7}) [event [7] [] [], event [] [7] []] := by
  intro executes
  have resource := (executable_iff_operator action label _ _
    (by simp [CheckFree, event])).mp executes |>.2.2.1
  contradiction

theorem cyclic_producers_have_shapes_and_consistent_equations :
    Shapes label [event [1] [] [2], event [2] [] [1]] ∧
      LocallyFresh [event [1] [] [2], event [2] [] [1]] ∧
      action.Consistent (follow label (state ∅)
        [event [1] [] [2], event [2] [] [1]]).equations := by
  exact ⟨by simp [Shapes, PortShape, event], by simp [LocallyFresh, event],
    every_unit_store_has_a_model _⟩

theorem cyclic_producers_have_neither_execution_order :
    ¬ Executable action label (state ∅) [event [1] [] [2], event [2] [] [1]] ∧
      ¬ Executable action label (state ∅) [event [2] [] [1], event [1] [] [2]] := by
  constructor <;> intro executes
  · have resource := (executable_iff_operator action label _ _
      (by simp [CheckFree, event])).mp executes |>.2.2.1
    contradiction
  · have resource := (executable_iff_operator action label _ _
      (by simp [CheckFree, event])).mp executes |>.2.2.1
    contradiction

theorem two_readers_publish_distinct_equal_labels :
    Executable action label (state {7}) [event [] [7] [8], event [] [7] [9]] ∧
      Executable action label (state {7}) [event [] [7] [9], event [] [7] [8]] ∧
      (follow label (state {7}) [event [] [7] [8], event [] [7] [9]]).present = {7, 8, 9} := by
  have first : Executable action label (state {7}) [event [] [7] [8], event [] [7] [9]] := by
    apply (executable_iff_operator action label _ _ (by simp [CheckFree, event])).mpr
    refine ⟨by simp [Shapes, PortShape, event], by simp [LocallyFresh, event], ?_,
      every_unit_store_has_a_model _⟩
    decide
  have independent : SharedReadsOnly (event [] [7] [8]).2 (event [] [7] [9]).2 := by
    intro occurrence
    by_cases seven : occurrence = 7
    · subst occurrence
      simp [event]
    · by_cases eight : occurrence = 8
      · subst occurrence
        simp [event]
      · left
        simp [event, Ne.symm seven, Ne.symm eight]
  exact ⟨first, (shared_reads_swap action label _ _ _ (by simp [CheckFree, event]) independent first).1,
    by decide⟩

theorem fewer_world_observations_do_not_erase_read_history :
    runs [(([] : List Nat), [7], [])] = runs [(([] : List Nat), [7], []), ([], [7], [])] ∧
      (([([], [7], [])] : List (List Nat × List Nat × List Nat)).length ≠
        ([([], [7], []), ([], [7], [])] : List (List Nat × List Nat × List Nat)).length) := by
  constructor
  · funext world
    by_cases present : (7 : Nat) ∈ world <;>
      simp [runs, commit, andThen, runList, one, point, present]
  · decide

theorem partial_publication_can_have_another_completed_commit_description :
    commit ([0] : List Nat) [] [1] {0} = some {1} ∧
      commit ([0] : List Nat) [] [1, 2] {0} = some {1, 2} ∧
      commit ([1] : List Nat) [] [0] {1} = some {0} ∧
      ({1} : Finset Nat) ≠ {1, 2} := by decide

/-- Commutation as partial maps includes both orders refusing. The sufficient
shared-read criterion cannot be read as a converse. -/
theorem distinct_overlapping_consumers_commute_as_partial_maps :
    runs [(([0] : List Nat), [], []), ([0, 1], [], [])] =
      runs [(([0, 1] : List Nat), [], []), ([0], [], [])] := by
  apply runs_eq_of_modes
  intro occurrence
  funext bit
  by_cases zero : occurrence = 0
  · subst occurrence
    cases bit <;> simp [modeRun, modeAction, modeBits, bitTake]
  · by_cases one : occurrence = 1
    · subst occurrence
      cases bit <;> simp [modeRun, modeAction, modeBits, bitTake]
    · cases bit <;> simp [modeRun, modeAction, modeBits, Ne.symm zero, Ne.symm one]

theorem the_overlapping_consumers_are_individually_available :
    commit ([0] : List Nat) [] [] {0, 1} = some {1} ∧
      commit ([0, 1] : List Nat) [] [] {0, 1} = some ∅ ∧
      ¬ SharedReadsOnly ((⟨[0], [], []⟩ : Selection Nat)) ⟨[0, 1], [], []⟩ := by
  refine ⟨by decide, by decide, ?_⟩
  intro shared
  have impossible := shared 0
  simp at impossible

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResourceProcessControls
