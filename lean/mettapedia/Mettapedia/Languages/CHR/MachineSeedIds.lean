import Mettapedia.Languages.CHR.MachinePublication

/-! Posted seed identifiers are distinct. A tick either keeps the posted
identifiers or posts the current counter in front of them, and every posted
identifier is below the counter. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Machine

theorem tick_seeds (table : Table) (state : State) :
    (tick table state).seeds = state.seeds ∨ (tick table state).seeds = state.next :: state.seeds := by
  cases running : state.status with
  | failed =>
    left
    have same : tick table state = state := by unfold tick; rw [running]
    rw [same]
  | faulted reason =>
    left
    have same : tick table state = state := by unfold tick; rw [running]
    rw [same]
  | running =>
    cases tasks : state.tasks with
    | nil =>
      left
      have same : tick table state = state := by unfold tick; rw [running, tasks]
      rw [same]
    | cons task rest =>
      cases seedsTask : task.isSeeds with
      | false => exact .inl (tick_shape table state task rest running tasks seedsTask).1
      | true =>
        cases task with
        | goals => simp [Task.isSeeds] at seedsTask
        | scan => simp [Task.isSeeds] at seedsTask
        | search => simp [Task.isSeeds] at seedsTask
        | seeds heads =>
          cases heads with
          | nil =>
            left
            have same : tick table state = { state with tasks := rest } := by unfold tick; rw [running, tasks]
            rw [same]
          | cons head heads =>
            right
            have ticked : tick table state =
                introduce table head [] (.seeds heads) state.tasks rest state (state.next :: state.seeds) := by
              unfold tick; rw [running, tasks]
            rw [ticked]
            unfold introduce
            split <;> rfl

theorem tick_seeds_nodup (table : Table) (state : State) (below : ∀ id ∈ state.seeds, id < state.next)
    (distinct : state.seeds.Nodup) : (tick table state).seeds.Nodup := by
  rcases tick_seeds table state with same | pushed
  · rw [same]
    exact distinct
  · rw [pushed]
    exact List.nodup_cons.mpr ⟨fun inside => Nat.lt_irrefl _ (below _ inside), distinct⟩

theorem advance_seeds_nodup (program : Program) (constraints : List Constraint) :
    ∀ (budget : Nat) (state : State) (abstract : CHR.State), Simulates program state abstract →
      Posting constraints state → state.seeds.Nodup → (advance (table program) budget state).seeds.Nodup
  | 0, _, _, _, _, distinct => distinct
  | budget + 1, state, abstract, simulates, posting, distinct => by
    unfold advance
    split
    · obtain ⟨middle, _, related⟩ := tick_simulates program state abstract simulates
      exact advance_seeds_nodup program constraints budget _ middle related
        (tick_posting program constraints state abstract simulates posting)
        (tick_seeds_nodup (table program) state posting.below distinct)
    · exact distinct

/-- **Posted identifiers are distinct.** -/
theorem run_seeds_nodup (program : Program) (constraints : List Constraint) (budget : Nat) :
    (advance (table program) budget (start (constraints.map Constraint.asHead))).seeds.Nodup :=
  advance_seeds_nodup program constraints budget _ _ (start_simulates program constraints)
    (start_posting constraints) (by simp [start])

#print axioms run_seeds_nodup

end Mettapedia.Languages.CHR.Machine
