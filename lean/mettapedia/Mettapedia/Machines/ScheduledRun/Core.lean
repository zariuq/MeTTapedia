import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.ModEq

/-!
# Ordered-successor runs under deterministic schedules

This language-independent theory belongs with machines, not with a particular
rewriting calculus. A state has a fixed ordered list of successors. Termination
is explicit: a terminal state is visible at its final turn; the following turn
is `none`, which is absorbing. Thus two stopped observations are not a live
return and cannot establish nontermination.

The natural-number turn models the mathematical schedule. A bounded or wrapping
machine clock needs a separate correspondence. Successor distinctness is not
needed for these soundness laws.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ScheduledRun

structure Schedule where
  pick : Nat → Nat → Nat
  bounded : ∀ turn count, 0 < count → pick turn count < count

def canonical : Schedule := ⟨fun _ _ => 0, fun _ _ positive => positive⟩
def rotating : Schedule := ⟨fun turn count => turn % count, fun _ _ positive => Nat.mod_lt _ positive⟩

inductive Mode where
  | canonical
  | rotating
  deriving DecidableEq, Repr

def Mode.schedule : Mode → Schedule
  | .canonical => Mettapedia.Machines.ScheduledRun.canonical
  | .rotating => Mettapedia.Machines.ScheduledRun.rotating

universe u
variable {S : Type u}

def step (next : S → List S) (schedule : Schedule) (turn : Nat) : Option S → Option S
  | none => none
  | some state =>
    if empty : (next state).length = 0 then none
    else some ((next state).get ⟨schedule.pick turn (next state).length,
      schedule.bounded turn _ (Nat.pos_of_ne_zero empty)⟩)

def run (next : S → List S) (schedule : Schedule) (initial : S) : Nat → Option S
  | 0 => some initial
  | turn + 1 => step next schedule turn (run next schedule initial turn)

def Nonterminating (next : S → List S) (schedule : Schedule) (initial : S) : Prop :=
  ∀ turn, run next schedule initial turn ≠ none

def EndsAt (next : S → List S) (schedule : Schedule) (initial : S) (turn : Nat) : Prop :=
  ∃ state, run next schedule initial turn = some state ∧ next state = []

def PeriodicFrom (next : S → List S) (schedule : Schedule) (initial : S)
    (start period : Nat) : Prop :=
  ∀ offset, run next schedule initial (start + offset + period) =
    run next schedule initial (start + offset)

@[simp] theorem run_zero (next : S → List S) (schedule : Schedule) (initial : S) :
    run next schedule initial 0 = some initial := rfl

@[simp] theorem run_succ (next : S → List S) (schedule : Schedule) (initial : S) (turn : Nat) :
    run next schedule initial (turn + 1) = step next schedule turn (run next schedule initial turn) := rfl

@[simp] theorem step_none (next : S → List S) (schedule : Schedule) (turn : Nat) :
    step next schedule turn none = none := rfl

theorem step_terminal (next : S → List S) (schedule : Schedule) (turn : Nat) (state : S)
    (terminal : next state = []) : step next schedule turn (some state) = none := by
  simp [step, terminal]

theorem step_eq_none_iff (next : S → List S) (schedule : Schedule) (turn : Nat) (state : S) :
    step next schedule turn (some state) = none ↔ next state = [] := by
  by_cases empty : next state = []
  · simp [step, empty]
  · have length : (next state).length ≠ 0 := fun h => empty (List.length_eq_zero_iff.mp h)
    simp [step, length, empty]

theorem step_eq_of_picks (next : S → List S) (schedule : Schedule)
    (first second : Nat) (observation : Option S)
    (same : ∀ state, observation = some state →
      schedule.pick first (next state).length = schedule.pick second (next state).length) :
    step next schedule first observation = step next schedule second observation := by
  cases observation with
  | none => rfl
  | some state =>
    by_cases empty : (next state).length = 0
    · simp [step, empty]
    · simp only [step, empty, ↓reduceDIte]
      apply congrArg some
      apply congrArg (next state).get
      exact Fin.ext (same state rfl)

theorem successor_of_present (next : S → List S) (schedule : Schedule) (initial : S)
    {turn : Nat} {state : S} (present : run next schedule initial turn = some state)
    (positive : 0 < (next state).length) :
    run next schedule initial (turn + 1) =
      some ((next state).get ⟨schedule.pick turn (next state).length, schedule.bounded turn _ positive⟩) := by
  rw [run_succ, present]
  simp [step, Nat.ne_of_gt positive]

theorem step_next_congr (first second : S → List S) (schedule : Schedule) (turn : Nat) (state : S)
    (same : first state = second state) :
    step first schedule turn (some state) = step second schedule turn (some state) :=
  congrArg (fun rows : List S => if empty : rows.length = 0 then (none : Option S)
    else some (rows.get ⟨schedule.pick turn rows.length,
      schedule.bounded turn _ (Nat.pos_of_ne_zero empty)⟩)) same

theorem none_persistent (next : S → List S) (schedule : Schedule) (initial : S)
    {turn : Nat} (stopped : run next schedule initial turn = none) (offset : Nat) :
    run next schedule initial (turn + offset) = none := by
  induction offset with
  | zero => simpa using stopped
  | succ offset ih => rw [Nat.add_succ, run_succ, ih, step_none]

theorem none_of_le (next : S → List S) (schedule : Schedule) (initial : S)
    {early late : Nat} (order : early ≤ late) (stopped : run next schedule initial early = none) :
    run next schedule initial late = none := by
  simpa only [Nat.add_sub_of_le order] using none_persistent next schedule initial stopped (late - early)

theorem present_before (next : S → List S) (schedule : Schedule) (initial : S)
    {early late : Nat} {state : S} (order : early ≤ late)
    (present : run next schedule initial late = some state) :
    run next schedule initial early ≠ none := by
  intro stopped
  have later := none_of_le next schedule initial order stopped
  rw [present] at later
  cases later

theorem ended_not_nonterminating (next : S → List S) (schedule : Schedule) (initial : S)
    {turn : Nat} (ended : EndsAt next schedule initial turn) :
    ¬ Nonterminating next schedule initial := by
  rintro infinite
  obtain ⟨state, present, terminal⟩ := ended
  exact infinite (turn + 1) (by rw [run_succ, present, step_terminal next schedule turn state terminal])

theorem nonterminating_of_tail (next : S → List S) (schedule : Schedule) (initial : S)
    (start : Nat) (tail : ∀ offset, run next schedule initial (start + offset) ≠ none) :
    Nonterminating next schedule initial := by
  intro turn
  by_cases order : start ≤ turn
  · simpa only [Nat.add_sub_of_le order] using tail (turn - start)
  · intro stopped
    have later := none_of_le next schedule initial (by omega : turn ≤ start) stopped
    exact tail 0 (by simpa using later)

theorem nonterminal_on_infinite (next : S → List S) (schedule : Schedule) (initial : S)
    (infinite : Nonterminating next schedule initial) {turn : Nat} {state : S}
    (present : run next schedule initial turn = some state) : 0 < (next state).length := by
  apply Nat.pos_of_ne_zero
  intro zero
  exact infinite (turn + 1) (by rw [run_succ, present,
    step_terminal next schedule turn state (List.length_eq_zero_iff.mp zero)])

theorem nonterminal_before_present (next : S → List S) (schedule : Schedule) (initial : S)
    {early late : Nat} {before after : S} (order : early < late)
    (previous : run next schedule initial early = some before)
    (present : run next schedule initial late = some after) : 0 < (next before).length := by
  apply Nat.pos_of_ne_zero
  intro zero
  have stopped : run next schedule initial (early + 1) = none := by
    rw [run_succ, previous, step_terminal next schedule early before (List.length_eq_zero_iff.mp zero)]
  exact present_before next schedule initial (by omega : early + 1 ≤ late) present stopped

theorem nonterminating_iff_no_ending (next : S → List S) (schedule : Schedule) (initial : S) :
    Nonterminating next schedule initial ↔ ∀ turn, ¬ EndsAt next schedule initial turn := by
  constructor
  · intro infinite turn ended
    exact ended_not_nonterminating next schedule initial ended infinite
  · intro noEnding turn
    induction turn with
    | zero => simp
    | succ turn ih =>
      intro stopped
      cases current : run next schedule initial turn with
      | none => exact ih current
      | some state =>
        have terminal : next state = [] :=
          (step_eq_none_iff next schedule turn state).mp (by simpa only [run_succ, current] using stopped)
        exact noEnding turn ⟨state, current, terminal⟩

end Mettapedia.Machines.ScheduledRun
