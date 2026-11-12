import Mettapedia.Machines.ProgressObservation

/-!
# Canonical compression of administrative event prefixes

A well-founded observer finds the next retained event along a supplied
execution. The search follows that execution alone: it enumerates neither the
event fibre nor alternative futures. Its certificate proves that every skipped
event was erased. Repeated searches retain every observed event, in order.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ProgressObservation

universe u v w

variable {V : Type u} [Quiver.{v} V] {Label : Type w}
variable (read : Observation V Label)

structure NextObserved (execution : Execution V) (start : ℕ) where
  index : ℕ
  lowerBound : start ≤ index
  observed : (read (execution.event index)).isSome = true
  skipped : ∀ n, start ≤ n → n < index → read (execution.event n) = none

/-- A constructive search, justified by accessibility of erased transitions. -/
def nextObserved (termination : WellFounded (fun b a => Administrative read a b))
    (execution : Execution V) (start : ℕ) : NextObserved read execution start :=
  termination.fix
    (C := fun state => ∀ current : ℕ, execution.state current = state → NextObserved read execution current)
    (fun state recurse current located =>
      match found : read (execution.event current) with
      | some _ => ⟨current, Nat.le_refl _, by simp [found], by intro n lower upper; omega⟩
      | none =>
          have decreases : Administrative read state (execution.state (current + 1)) := by
            rw [← located]
            exact ⟨execution.event current, found⟩
          let later := recurse (execution.state (current + 1)) decreases (current + 1) rfl
          ⟨later.index, Nat.le_trans (Nat.le_succ current) later.lowerBound, later.observed,
            by
              intro n lower upper
              by_cases same : n = current
              · subst n
                exact found
              · exact later.skipped n (by omega) upper⟩)
    (execution.state start) start rfl

theorem nonZeno_constructive (termination : WellFounded (fun b a => Administrative read a b)) :
    NonZeno read := fun execution start =>
  ⟨(nextObserved read termination execution start).index,
    (nextObserved read termination execution start).lowerBound,
    (nextObserved read termination execution start).observed⟩

namespace NextObserved

variable {read} {execution : Execution V} {start : ℕ}

theorem index_le (next : NextObserved read execution start) {n : ℕ} (after : start ≤ n)
    (observed : (read (execution.event n)).isSome = true) : next.index ≤ n := by
  by_contra beyond
  have erased := next.skipped n after (by omega)
  simp [erased] at observed

/-- The first observed position is independent of which termination proof finds it. -/
theorem index_unique (first second : NextObserved read execution start) : first.index = second.index :=
  Nat.le_antisymm (first.index_le second.lowerBound second.observed)
    (second.index_le first.lowerBound first.observed)

end NextObserved

def observedIndex (termination : WellFounded (fun b a => Administrative read a b))
    (execution : Execution V) : ℕ → ℕ
  | 0 => (nextObserved read termination execution 0).index
  | n + 1 => (nextObserved read termination execution (observedIndex termination execution n + 1)).index

theorem observedIndex_present (termination : WellFounded (fun b a => Administrative read a b))
    (execution : Execution V) (n : ℕ) :
    (read (execution.event (observedIndex read termination execution n))).isSome = true := by
  cases n with
  | zero => exact (nextObserved read termination execution 0).observed
  | succ n => exact (nextObserved read termination execution
      (observedIndex read termination execution n + 1)).observed

theorem observedIndex_step (termination : WellFounded (fun b a => Administrative read a b))
    (execution : Execution V) (n : ℕ) :
    observedIndex read termination execution n < observedIndex read termination execution (n + 1) := by
  exact (nextObserved read termination execution
    (observedIndex read termination execution n + 1)).lowerBound

theorem observedIndex_strictMono (termination : WellFounded (fun b a => Administrative read a b))
    (execution : Execution V) : StrictMono (observedIndex read termination execution) :=
  strictMono_nat_of_lt_succ (observedIndex_step read termination execution)

theorem observedIndex_ge (termination : WellFounded (fun b a => Administrative read a b))
    (execution : Execution V) (n : ℕ) : n ≤ observedIndex read termination execution n := by
  induction n with
  | zero => omega
  | succ n ih =>
      have later := observedIndex_step read termination execution n
      omega

/-- Every retained event occurs in the compression; it cannot be silently skipped. -/
theorem observedIndex_covers (termination : WellFounded (fun b a => Administrative read a b))
    (execution : Execution V) {position : ℕ}
    (present : (read (execution.event position)).isSome = true) :
    ∃ n, observedIndex read termination execution n = position := by
  have available : ∃ n, position ≤ observedIndex read termination execution n :=
    ⟨position, observedIndex_ge read termination execution position⟩
  have enough := Nat.find_spec available
  generalize chosen : Nat.find available = n at enough
  refine ⟨n, Nat.le_antisymm ?_ enough⟩
  cases n with
  | zero => exact (nextObserved read termination execution 0).index_le (Nat.zero_le _) present
  | succ n =>
      have previous : observedIndex read termination execution n < position := by
        have excluded := Nat.find_min available (show n < Nat.find available by omega)
        omega
      exact (nextObserved read termination execution
        (observedIndex read termination execution n + 1)).index_le (by omega) present

def compressedLabel (termination : WellFounded (fun b a => Administrative read a b))
    (execution : Execution V) (n : ℕ) : Label :=
  (read (execution.event (observedIndex read termination execution n))).get
    (observedIndex_present read termination execution n)

theorem compressedLabel_present (termination : WellFounded (fun b a => Administrative read a b))
    (execution : Execution V) (n : ℕ) :
    read (execution.event (observedIndex read termination execution n)) =
      some (compressedLabel read termination execution n) := by
  exact (Option.some_get (observedIndex_present read termination execution n)).symm

end Mettapedia.Machines.ProgressObservation
