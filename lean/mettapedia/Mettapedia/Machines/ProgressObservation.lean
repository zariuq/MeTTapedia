import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Order.WellFounded
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
# Productive observations of infinite event executions

The observer acts on generating events, including distinct events with identical
endpoints. An erased event is administrative for this declared observation.
Well-foundedness of erased steps is equivalent to every infinite execution having
observed events arbitrarily far along it. This concerns existing executions;
existence, source adequacy, scheduling fairness and terminal outcomes are separate.
`NonZeno` here is observation productivity; no physical clock is specified.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ProgressObservation

universe u v w

variable {V : Type u} [Quiver.{v} V] {Label : Type w}

/-- An execution already supplies its chosen event at every position. -/
structure Execution (V : Type u) [Quiver.{v} V] where
  state : ℕ → V
  event : (n : ℕ) → state n ⟶ state (n + 1)

abbrev Observation (V : Type u) [Quiver.{v} V] (Label : Type w) :=
  ∀ {a b : V}, (a ⟶ b) → Option Label

variable (read : Observation V Label)

/-- The state relation induced by events erased by the observer. -/
def Administrative (a b : V) : Prop := ∃ event : a ⟶ b, read event = none

/-- Every suffix of every existing infinite execution contains an observed event. -/
def NonZeno : Prop :=
  ∀ execution : Execution V, ∀ start : ℕ,
    ∃ n, start ≤ n ∧ (read (execution.event n)).isSome = true

theorem nonZeno_of_wellFounded
    (termination : WellFounded (fun b a => Administrative read a b)) : NonZeno read := by
  intro execution start
  by_contra absent
  have erased (n : ℕ) : read (execution.event (start + n)) = none := by
    cases found : read (execution.event (start + n)) with
    | none => rfl
    | some value => exact False.elim (absent ⟨start + n, by omega, by simp [found]⟩)
  apply (wellFounded_iff_isEmpty_descending_chain.mp termination).false
  refine ⟨(fun n => execution.state (start + n)), ?_⟩
  intro n
  simpa only [Nat.add_assoc] using
    (show Administrative read (execution.state (start + n))
        (execution.state (start + n + 1)) from ⟨execution.event (start + n), erased n⟩)

theorem wellFounded_of_nonZeno (progress : NonZeno read) :
    WellFounded (fun b a => Administrative read a b) := by
  classical
  apply wellFounded_iff_isEmpty_descending_chain.mpr
  refine ⟨?_⟩
  rintro ⟨states, moves⟩
  let execution : Execution V := ⟨states, fun n => (moves n).choose⟩
  obtain ⟨n, _, observed⟩ := progress execution 0
  have erased : read (execution.event n) = none := (moves n).choose_spec
  simp [erased] at observed

/-- This characterization does not require finite branching or inhabited event fibres. -/
theorem nonZeno_iff_wellFounded :
    NonZeno read ↔ WellFounded (fun b a => Administrative read a b) :=
  ⟨wellFounded_of_nonZeno read, nonZeno_of_wellFounded read⟩

/-- A natural potential is a sufficient, quantitative certificate. -/
theorem wellFounded_of_rank (rank : V → ℕ)
    (decreases : ∀ {a b : V} (event : a ⟶ b), read event = none → rank b < rank a) :
    WellFounded (fun b a => Administrative read a b) :=
  Subrelation.wf (fun {_ _} ⟨event, erased⟩ => decreases event erased)
    (InvImage.wf rank Nat.lt_wfRel.wf)

theorem nonZeno_of_rank (rank : V → ℕ)
    (decreases : ∀ {a b : V} (event : a ⟶ b), read event = none → rank b < rank a) :
    NonZeno read :=
  nonZeno_of_wellFounded read (wellFounded_of_rank read rank decreases)

/-- Finite observations use Mathlib's paths in the generating quiver. -/
def observePath {a : V} : {b : V} → Quiver.Path a b → List Label
  | _, .nil => []
  | _, .cons path event => observePath path ++ (read event).toList

@[simp] theorem observePath_nil (a : V) : observePath read (Quiver.Path.nil : Quiver.Path a a) = [] := rfl

@[simp] theorem observePath_cons {a b c : V} (path : Quiver.Path a b) (event : b ⟶ c) :
    observePath read (path.cons event) = observePath read path ++ (read event).toList := rfl

theorem observePath_comp {a b c : V} (first : Quiver.Path a b) (second : Quiver.Path b c) :
    observePath read (first.comp second) = observePath read first ++ observePath read second := by
  induction second with
  | nil => simp
  | cons path event ih => simp [ih, List.append_assoc]

/-- Erased finite work has a bound that includes its entire administrative prefix. -/
theorem erased_path_bound (rank : V → ℕ)
    (decreases : ∀ {a b : V} (event : a ⟶ b), read event = none → rank b < rank a)
    {a b : V} (path : Quiver.Path a b) (erased : observePath read path = []) :
    path.length + rank b ≤ rank a := by
  induction path with
  | nil => simp
  | @cons b c path event ih =>
      cases found : read event with
      | none =>
          have earlier : observePath read path = [] := by simpa [found] using erased
          have previousBound := ih earlier
          have drop := decreases event found
          simp only [Quiver.Path.length_cons]
          omega
      | some value => simp [found] at erased

namespace Execution

def initialPath (execution : Execution V) : (n : ℕ) → Quiver.Path (execution.state 0) (execution.state n)
  | 0 => .nil
  | n + 1 => (initialPath execution n).cons (execution.event n)

@[simp] theorem initialPath_length (execution : Execution V) (n : ℕ) :
    (execution.initialPath n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [initialPath, ih]

def observedCount (execution : Execution V) (n : ℕ) : ℕ :=
  (observePath read (execution.initialPath n)).length

@[simp] theorem observedCount_zero (execution : Execution V) : execution.observedCount read 0 = 0 := rfl

theorem observedCount_succ (execution : Execution V) (n : ℕ) :
    execution.observedCount read (n + 1) =
      execution.observedCount read n + (read (execution.event n)).toList.length := by
  simp [observedCount, initialPath]

theorem observedCount_monotone (execution : Execution V) : Monotone (execution.observedCount read) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [observedCount_succ]
  omega

theorem observedCount_le (execution : Execution V) (n : ℕ) :
    execution.observedCount read n ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [observedCount_succ]
      cases read (execution.event n) <;> simp_all
      omega

end Execution

theorem unbounded_observations (progress : NonZeno read) (execution : Execution V) :
    ∀ count : ℕ, ∃ cutoff, count ≤ execution.observedCount read cutoff := by
  intro count
  induction count with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ count ih =>
      obtain ⟨start, enough⟩ := ih
      obtain ⟨n, after, present⟩ := progress execution start
      have monotone := execution.observedCount_monotone read after
      refine ⟨n + 1, ?_⟩
      rw [Execution.observedCount_succ]
      cases found : read (execution.event n) with
      | none => simp [found] at present
      | some value => simp only [Option.toList_some, List.length_singleton]; omega

theorem nonZeno_of_unbounded_observations
    (unbounded : ∀ execution : Execution V, ∀ count : ℕ,
      ∃ cutoff, count ≤ execution.observedCount read cutoff) : NonZeno read := by
  intro execution start
  by_contra absent
  have erased (n : ℕ) : start ≤ n → read (execution.event n) = none := by
    intro after
    cases found : read (execution.event n) with
    | none => rfl
    | some value => exact False.elim (absent ⟨n, after, by simp [found]⟩)
  have constant (n : ℕ) :
      execution.observedCount read (start + n) = execution.observedCount read start := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Nat.add_succ, Execution.observedCount_succ, erased (start + n) (by omega)]
        simpa using ih
  obtain ⟨cutoff, enough⟩ := unbounded execution (execution.observedCount read start + 1)
  by_cases before : cutoff ≤ start
  · have bound := execution.observedCount_monotone read before
    omega
  · have eq := constant (cutoff - start)
    rw [Nat.add_sub_of_le (by omega : start ≤ cutoff)] at eq
    omega

/-- Unbounded finite observations and productive infinite observations coincide. -/
theorem nonZeno_iff_unbounded_observations : NonZeno read ↔
    ∀ execution : Execution V, ∀ count : ℕ,
      ∃ cutoff, count ≤ execution.observedCount read cutoff :=
  ⟨unbounded_observations read, nonZeno_of_unbounded_observations read⟩

end Mettapedia.Machines.ProgressObservation
