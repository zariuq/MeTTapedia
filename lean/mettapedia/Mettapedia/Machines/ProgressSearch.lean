import Mettapedia.Machines.ProgressCompression

/-!
# Resumable search for retained events

The cursor examines a supplied execution in order. A finite budget returns a
retained event or the exact position from which to resume. Suspension makes no
claim that an event is absent. Combining budgets resumes at that position and
does not inspect the earlier erased prefix again.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ProgressObservation

universe u v w

variable {V : Type u} [Quiver.{v} V] {Label : Type w}
variable (read : Observation V Label) (execution : Execution V)

def Execution.labelAt (n : ℕ) : Option Label := read (execution.event n)

inductive SearchResult (Label : Type w) where
  | found (position : ℕ) (value : Label)
  | suspended (nextPosition : ℕ)
  deriving DecidableEq

def seek : ℕ → ℕ → SearchResult Label
  | 0, start => .suspended start
  | budget + 1, start =>
      match execution.labelAt read start with
      | some value => .found start value
      | none => seek budget (start + 1)

def resume (result : SearchResult Label) (budget : ℕ) : SearchResult Label :=
  match result with
  | .found position value => .found position value
  | .suspended start => seek read execution budget start

theorem seek_resume (earlier later start : ℕ) :
    seek read execution (earlier + later) start =
      resume read execution (seek read execution earlier start) later := by
  induction earlier generalizing start with
  | zero => simp only [Nat.zero_add, seek, resume]
  | succ earlier ih =>
      cases found : execution.labelAt read start <;>
        simp [seek, Nat.succ_add, found, resume, ih]

def SearchResult.Correct (start budget : ℕ) : SearchResult Label → Prop
  | .found position value => start ≤ position ∧ position < start + budget ∧
      execution.labelAt read position = some value ∧
      ∀ n, start ≤ n → n < position → execution.labelAt read n = none
  | .suspended nextPosition => nextPosition = start + budget ∧
      ∀ n, start ≤ n → n < nextPosition → execution.labelAt read n = none

theorem seek_correct (budget start : ℕ) :
    SearchResult.Correct read execution start budget (seek read execution budget start) := by
  induction budget generalizing start with
  | zero =>
      refine ⟨by omega, ?_⟩
      intro n lower upper
      omega
  | succ budget ih =>
      cases found : execution.labelAt read start with
      | some value =>
          simp only [seek, found]
          refine ⟨Nat.le_refl _, by omega, found, ?_⟩
          intro n lower upper
          omega
      | none =>
          simp only [seek, found]
          have earlier := ih (start + 1)
          cases result : seek read execution budget (start + 1) with
          | found position value =>
              rw [result] at earlier
              obtain ⟨lower, upper, observed, skipped⟩ := earlier
              refine ⟨by omega, by omega, observed, ?_⟩
              intro n after before
              by_cases first : n = start
              · subst n
                exact found
              · exact skipped n (by omega) before
          | suspended nextPosition =>
              rw [result] at earlier
              obtain ⟨position, skipped⟩ := earlier
              refine ⟨by omega, ?_⟩
              intro n after before
              by_cases first : n = start
              · subst n
                exact found
              · exact skipped n (by omega) before

theorem suspension_position {budget start nextPosition : ℕ}
    (suspended : seek read execution budget start = .suspended nextPosition) :
    nextPosition = start + budget := by
  have correct := seek_correct read execution budget start
  rw [suspended] at correct
  exact correct.1

theorem found_stable {budget start position : ℕ} {value : Label}
    (found : seek read execution budget start = .found position value) (later : ℕ) :
    seek read execution (budget + later) start = .found position value := by
  rw [seek_resume, found]
  rfl

/-- A declarative erased prefix followed by an event is found at its exact position. -/
theorem seek_finds (gap start : ℕ) (value : Label)
    (erased : ∀ n, n < gap → execution.labelAt read (start + n) = none)
    (present : execution.labelAt read (start + gap) = some value) :
    seek read execution (gap + 1) start = .found (start + gap) value := by
  induction gap generalizing start with
  | zero =>
      simp only [Nat.add_zero] at present
      simp [seek, present]
  | succ gap ih =>
      have first : execution.labelAt read start = none := by simpa using erased 0 (by omega)
      rw [seek, first]
      have tailErased : ∀ n, n < gap → execution.labelAt read (start + 1 + n) = none := by
        intro n before
        rw [show start + 1 + n = start + (n + 1) by omega]
        exact erased (n + 1) (by omega)
      have tailPresent : execution.labelAt read (start + 1 + gap) = some value := by
        rw [show start + 1 + gap = start + (gap + 1) by omega]
        exact present
      have found := ih (start + 1) tailErased tailPresent
      rw [show start + 1 + gap = start + (gap + 1) by omega] at found
      exact found

/-- Well-founded erased work supplies an explicit sufficient budget for each execution suffix. -/
theorem seek_eventually_finds
    (termination : WellFounded (fun b a => Administrative read a b)) (start : ℕ) :
    ∃ budget position value, seek read execution budget start = .found position value := by
  let next := nextObserved read termination execution start
  let value := (read (execution.event next.index)).get next.observed
  have present : execution.labelAt read next.index = some value :=
    (Option.some_get next.observed).symm
  have startGap : start + (next.index - start) = next.index := Nat.add_sub_of_le next.lowerBound
  refine ⟨next.index - start + 1, next.index, value, ?_⟩
  have found := seek_finds read execution (next.index - start) start value
    (fun n before => next.skipped (start + n) (by omega) (by omega))
    (by rw [startGap]; exact present)
  simpa only [startGap] using found

theorem resumed_found_after_suspension {budget start nextPosition later position : ℕ} {value : Label}
    (suspended : seek read execution budget start = .suspended nextPosition)
    (found : resume read execution (.suspended nextPosition) later = .found position value) :
    start + budget ≤ position := by
  have next := suspension_position read execution suspended
  have correct := seek_correct read execution later nextPosition
  change seek read execution later nextPosition = .found position value at found
  rw [found] at correct
  exact next ▸ correct.1

/-- The exact finite budget condition is the distance to the first retained event. -/
theorem seek_found_iff {start : ℕ} (next : NextObserved read execution start) (budget : ℕ) :
    (∃ position value, seek read execution budget start = .found position value) ↔
      next.index - start < budget := by
  constructor
  · rintro ⟨position, value, found⟩
    have correct := seek_correct read execution budget start
    rw [found] at correct
    obtain ⟨lower, upper, present, skipped⟩ := correct
    let actual : NextObserved read execution start :=
      ⟨position, lower, congrArg Option.isSome present, skipped⟩
    have same := next.index_unique actual
    change next.index = position at same
    omega
  · intro enough
    let value := (read (execution.event next.index)).get next.observed
    have present : execution.labelAt read next.index = some value :=
      (Option.some_get next.observed).symm
    have offset : start + (next.index - start) = next.index := Nat.add_sub_of_le next.lowerBound
    have found := seek_finds read execution (next.index - start) start value
      (fun n before => next.skipped (start + n) (by omega) (by omega))
      (by rw [offset]; exact present)
    have stable := found_stable read execution found (budget - (next.index - start + 1))
    rw [show next.index - start + 1 + (budget - (next.index - start + 1)) = budget by omega,
      offset] at stable
    exact ⟨next.index, value, stable⟩

def allocatedBudget (allocation : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => allocatedBudget allocation n + allocation n

def searchChunks (allocation : ℕ → ℕ) (start : ℕ) : ℕ → SearchResult Label
  | 0 => .suspended start
  | n + 1 => resume read execution (searchChunks allocation start n) (allocation n)

theorem searchChunks_eq (allocation : ℕ → ℕ) (start n : ℕ) :
    searchChunks read execution allocation start n = seek read execution (allocatedBudget allocation n) start := by
  induction n with
  | zero => rfl
  | succ n ih => rw [searchChunks, allocatedBudget, ih, seek_resume]

theorem unbounded_allocation_eventually_finds
    (termination : WellFounded (fun b a => Administrative read a b))
    (allocation : ℕ → ℕ)
    (unbounded : ∀ budget : ℕ, ∃ n, budget ≤ allocatedBudget allocation n) (start : ℕ) :
    ∃ n position value, searchChunks read execution allocation start n = .found position value := by
  obtain ⟨budget, position, value, found⟩ := seek_eventually_finds read execution termination start
  obtain ⟨n, enough⟩ := unbounded budget
  have stable := found_stable read execution found (allocatedBudget allocation n - budget)
  rw [Nat.add_sub_of_le enough] at stable
  exact ⟨n, position, value, (searchChunks_eq read execution allocation start n).trans stable⟩

end Mettapedia.Machines.ProgressObservation
