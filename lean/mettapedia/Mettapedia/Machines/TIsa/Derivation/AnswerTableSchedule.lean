import Mettapedia.Machines.TIsa.Derivation.AnswerTableLimits
import Mettapedia.Machines.TIsa.Derivation.SnapshotMachine

/-!
# Fixed-point evaluation on the shared snapshot machine

The table proposes its next snapshot and refuses publication if
it would not change. Fuel pays for publications, not for detecting
the fixed point. A quiescent count table gives complete multiplicities;
an exhausted count table is only a finite-depth approximation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation

namespace FixedPointSchedule

open SnapshotMachine (Phases Schedule Outcome)

universe u
variable {State : Type u} [DecidableEq State]

def phases (State : Type u) : Phases State where
  Candidate _ := PUnit.{u+1}
  Pending _ := State
  Accepted _ := State

def schedule (update : State → State) : Schedule (phases State) where
  options _ := [PUnit.unit]
  prepare {before} _ := some (update before)
  verify {before} candidate :=
    let next : State := candidate
    if next = before then none else some next
  publish candidate := candidate

def iterate (update : State → State) : ℕ → State → State
  | 0, state => state
  | fuel + 1, state => iterate update fuel (update state)

omit [DecidableEq State] in
theorem iterate_succ (update : State → State) (fuel : ℕ) (state : State) :
    iterate update (fuel + 1) state = update (iterate update fuel state) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih => exact ih (update state)

omit [DecidableEq State] in
theorem iterate_fixed (update : State → State) (fuel : ℕ) (state : State) (fixed : update state = state) :
    iterate update fuel state = state := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => rw [iterate, fixed, ih]

theorem search_eq (update : State → State) (state : State) :
    SnapshotMachine.search (schedule update) state =
      if update state = state then none else some (update state) := by
  change ([PUnit.unit].findSome? (fun (_ : PUnit.{u+1}) =>
    (some (update state)).bind fun next => if next = state then none else some next)) = _
  by_cases h : update state = state <;> simp [h]

theorem run_eq (update : State → State) (fuel : ℕ) (state : State) :
    SnapshotMachine.run (schedule update) fuel state =
      let result := iterate update fuel state
      if update result = result then .quiescent result else .exhausted result := by
  induction fuel generalizing state with
  | zero =>
    by_cases fixed : update state = state <;>
      simp [SnapshotMachine.run, search_eq, iterate, fixed]
  | succ fuel ih =>
    by_cases fixed : update state = state
    · rw [SnapshotMachine.run, search_eq, if_pos fixed, iterate_fixed _ _ _ fixed, if_pos fixed]
    · rw [SnapshotMachine.run, search_eq, if_neg fixed, iterate]
      exact ih (update state)

theorem exists_complete_run (update : State → State) (fuel : ℕ) (state : State) :
    ∃ result, SnapshotMachine.Runs (schedule update) (.entry fuel state) (.halt result) ∧
      (result = if update (iterate update fuel state) = iterate update fuel state
        then .quiescent (iterate update fuel state) else .exhausted (iterate update fuel state)) :=
  ⟨_, SnapshotMachine.complete_run (schedule update) fuel state, run_eq update fuel state⟩

end FixedPointSchedule

namespace AnswerTable

open FixedPointSchedule (iterate schedule)

variable {n : ℕ}

def countStep (program : List (Clause n)) (previous : Vector ℕ n) : Vector ℕ n :=
  Vector.ofFn fun key => countRound program (fun q => previous[q.val]'q.isLt) key

def presenceStep (program : List (Clause n)) (previous : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun q => (eligible program q).any
    (fun i => (program.get i).premises.all (fun p => decide (p ∈ previous)))

theorem count_layers (program : List (Clause n)) (depth : ℕ) :
    iterate (countStep program) depth (Vector.replicate n 0) = counts program depth := by
  induction depth with
  | zero => rfl
  | succ depth ih => rw [FixedPointSchedule.iterate_succ, ih]; rfl

theorem presence_layers (program : List (Clause n)) (depth : ℕ) :
    iterate (presenceStep program) depth ∅ = presence program depth := by
  induction depth with
  | zero => rfl
  | succ depth ih => rw [FixedPointSchedule.iterate_succ, ih]; rfl

def countMachine (program : List (Clause n)) (fuel : ℕ) : SnapshotMachine.Outcome (Vector ℕ n) :=
  SnapshotMachine.run (schedule (countStep program)) fuel (Vector.replicate n 0)

def presenceMachine (program : List (Clause n)) (fuel : ℕ) : SnapshotMachine.Outcome (Finset (Fin n)) :=
  SnapshotMachine.run (schedule (presenceStep program)) fuel ∅

theorem count_machine_exact (program : List (Clause n)) (fuel : ℕ) :
    countMachine program fuel =
      if counts program (fuel + 1) = counts program fuel then .quiescent (counts program fuel)
      else .exhausted (counts program fuel) := by
  rw [countMachine, FixedPointSchedule.run_eq, count_layers]
  rfl

theorem presence_machine_completes (program : List (Clause n)) :
    presenceMachine program n = .quiescent (presence program n) := by
  rw [presenceMachine, FixedPointSchedule.run_eq, presence_layers]
  change (if presence program (n + 1) = presence program n then SnapshotMachine.Outcome.quiescent (presence program n)
    else SnapshotMachine.Outcome.exhausted (presence program n)) = _
  rw [if_pos (presence_saturates program).symm]

theorem counts_stay (program : List (Clause n)) {first : ℕ} (fixed : counts program (first + 1) = counts program first)
    {later : ℕ} (bound : first ≤ later) : counts program later = counts program first := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le bound
  clear bound
  induction extra with
  | zero => rfl
  | succ extra ih =>
    change countStep program (counts program (first + extra)) = _
    rw [ih]
    exact fixed

/-- Quiescence is evidence of completed counts, including the
absence of an infinite proof multiplicity at each query. -/
theorem quiescent_counts (program : List (Clause n)) {fuel : ℕ} {table : Vector ℕ n}
    (done : countMachine program fuel = .quiescent table) (key : Fin n) :
    Finite (AnswerWitness program key) ∧ table[key.val]'key.isLt = Nat.card (AnswerWitness program key) := by
  rw [count_machine_exact] at done
  split at done
  · rename_i stationary
    obtain rfl := (SnapshotMachine.Outcome.quiescent.inj done).symm
    have finite : Finite (AnswerWitness program key) := by
      by_contra missing
      have infinite := not_finite_iff_infinite.mp missing
      obtain ⟨depth, larger⟩ := (infinite_iff_unbounded program key).mp infinite
        ((counts program fuel)[key.val]'key.isLt)
      have grows := counts_mono program (Nat.le_max_left depth fuel) key
      rw [counts_stay program stationary (Nat.le_max_right depth fuel)] at grows
      omega
    let _ := finite
    obtain ⟨limit, exactCount⟩ := finite_derivations_eventual_count program key
    have computed := exactCount (max limit fuel) (Nat.le_max_left limit fuel)
    rw [counts_stay program stationary (Nat.le_max_right limit fuel)] at computed
    exact ⟨finite, computed⟩
  · cases done

theorem finite_counts_reach_quiescence (program : List (Clause n))
    (finite : ∀ key, Finite (AnswerWitness program key)) :
    ∃ fuel, countMachine program fuel = .quiescent (counts program fuel) := by
  classical
  choose limit exactCount using fun key =>
    @finite_derivations_eventual_count n program key (finite key)
  let depth := Finset.univ.sup limit
  have fixed : counts program (depth + 1) = counts program depth := by
    apply Vector.ext
    intro key within
    let q : Fin n := ⟨key, within⟩
    have covers : limit q ≤ depth := Finset.le_sup (f := limit) (Finset.mem_univ q)
    exact (exactCount q (depth + 1) (by omega)).trans (exactCount q depth covers).symm
  exact ⟨depth, by rw [count_machine_exact, if_pos fixed]⟩

theorem infinite_counts_exhaust (program : List (Clause n)) (key : Fin n)
    (infinite : Infinite (AnswerWitness program key)) (fuel : ℕ) :
    countMachine program fuel = .exhausted (counts program fuel) := by
  rw [count_machine_exact]
  split
  · rename_i stable
    have done : countMachine program fuel = .quiescent (counts program fuel) := by
      rw [count_machine_exact, if_pos stable]
    exact ((not_finite_iff_infinite.mpr infinite) (quiescent_counts program done key).1).elim
  · rfl

theorem count_trace_exact (program : List (Clause n)) (fuel : ℕ) :
    let driver := schedule (countStep program)
    let initial := Vector.replicate n 0
    (∃ result, SnapshotMachine.Runs driver (.entry fuel initial) (.halt result)) ∧
      ∀ result, SnapshotMachine.Runs driver (.entry fuel initial) (.halt result) ↔ result = countMachine program fuel := by
  exact ⟨⟨_, SnapshotMachine.complete_run (schedule (countStep program)) fuel (Vector.replicate n 0)⟩,
    SnapshotMachine.machine_run_iff (schedule (countStep program)) fuel (Vector.replicate n 0)⟩

theorem presence_trace_reaches_complete_table (program : List (Clause n)) :
    SnapshotMachine.Runs (schedule (presenceStep program)) (.entry n ∅) (.halt (.quiescent (presence program n))) ∧
      ∀ key ∈ presence program n, ∃ proof, Derives program key proof := by
  refine ⟨?_, fun key member => (presence_complete program key).mp member⟩
  rw [← presence_machine_completes program]
  exact SnapshotMachine.complete_run (schedule (presenceStep program)) n ∅

namespace ScheduleExamples

private def duplicateChoices : List (Clause 2) := [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0]⟩]

theorem four_answers_reach_quiescence : countMachine duplicateChoices 2 = .quiescent #v[2, 4] := by
  have stable : counts duplicateChoices 3 = counts duplicateChoices 2 := by decide +kernel
  have multiplicity : counts duplicateChoices 2 = #v[2, 4] := by decide +kernel
  rw [count_machine_exact, if_pos stable, multiplicity]

private def productive : List (Clause 1) := [⟨0, []⟩, ⟨0, [0]⟩]

theorem productive_cycle_never_reports_finished_counts (fuel : ℕ) :
    countMachine productive fuel = .exhausted (counts productive fuel) :=
  infinite_counts_exhaust productive 0 productive_cycle_has_infinite_derivations fuel

theorem productive_cycle_does_report_finished_presence : presenceMachine productive 1 = .quiescent {0} := by
  rw [presence_machine_completes]
  exact congrArg SnapshotMachine.Outcome.quiescent (by decide +kernel : presence productive 1 = {0})

end ScheduleExamples

end AnswerTable

end Mettapedia.Machines.TIsa.Derivation
