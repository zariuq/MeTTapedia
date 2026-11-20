import Mettapedia.Machines.ScheduledRun.Replay
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Live-return and LCM licences for scheduled periodicity

The rotating licence needs divisibility only for counts met in the candidate
segment, not for all successors or all future states. Canonical choice has no
time dependence. `return_mod_lcm_periodic` is the mathematical contract behind
the shared runner's state/phase key; it does not prove its hash table, bounded
counter arithmetic, memory behavior or interpretation of language states.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ScheduledRun

universe u
variable {S : Type u}

theorem canonical_shift_compatible (start period count : Nat) :
    ShiftCompatible canonical start period count := fun _ => rfl

theorem rotating_shift_compatible (start period count : Nat) (divides : count ∣ period) :
    ShiftCompatible rotating start period count := by
  intro offset
  change (start + offset) % count = (start + offset % period) % count
  rw [Nat.add_mod start offset count, Nat.add_mod start (offset % period) count,
    Nat.mod_mod_of_dvd _ divides]

theorem rotating_return_periodic (next : S → List S) (initial : S)
    {first last : Nat} (order : first < last) (state : S)
    (firstPresent : run next rotating initial first = some state)
    (lastPresent : run next rotating initial last = some state)
    (divides : ∀ turn, first ≤ turn → turn < last → ∀ value,
      run next rotating initial turn = some value → (next value).length ∣ last - first) :
    Nonterminating next rotating initial ∧ PeriodicFrom next rotating initial first (last - first) := by
  apply return_periodic_of_shift_compatible next rotating initial first (last - first)
    (Nat.sub_pos_of_lt order) state firstPresent
    (by simpa only [Nat.add_sub_of_le order.le] using lastPresent)
  intro offset inside value present
  exact rotating_shift_compatible _ _ _ (divides (first + offset) (by omega) (by omega) value present)

theorem canonical_return_periodic (next : S → List S) (initial : S)
    {first last : Nat} (order : first < last) (state : S)
    (firstPresent : run next canonical initial first = some state)
    (lastPresent : run next canonical initial last = some state) :
    Nonterminating next canonical initial ∧ PeriodicFrom next canonical initial first (last - first) := by
  apply return_periodic_of_shift_compatible next canonical initial first (last - first)
    (Nat.sub_pos_of_lt order) state firstPresent
    (by simpa only [Nat.add_sub_of_le order.le] using lastPresent)
  exact fun _ _ _ _ => canonical_shift_compatible _ _ _

def arityAt (next : S → List S) (schedule : Schedule) (initial : S) (turn : Nat) : Nat :=
  (run next schedule initial turn).elim 0 (fun state => (next state).length)

def segmentPeriod (next : S → List S) (schedule : Schedule) (initial : S) (first last : Nat) : Nat :=
  (Finset.Ico first last).lcm (arityAt next schedule initial)

theorem arity_dvd_segmentPeriod (next : S → List S) (schedule : Schedule) (initial : S)
    {first last turn : Nat} (inside : first ≤ turn ∧ turn < last) {state : S}
    (present : run next schedule initial turn = some state) :
    (next state).length ∣ segmentPeriod next schedule initial first last := by
  have divides := Finset.dvd_lcm (f := arityAt next schedule initial) (Finset.mem_Ico.mpr inside)
  change arityAt next schedule initial turn ∣ segmentPeriod next schedule initial first last at divides
  simpa only [arityAt, present, Option.elim_some] using divides

/-- Any supplied common period suffices; being the least one is not needed
for soundness. This permits both prefix and segment-local LCM certificates. -/
theorem return_mod_common_period (next : S → List S) (initial : S)
    {first last period : Nat} (order : first < last) (state : S)
    (firstPresent : run next rotating initial first = some state)
    (lastPresent : run next rotating initial last = some state)
    (phase : Nat.ModEq period first last)
    (counts : ∀ turn, first ≤ turn → turn < last → ∀ value,
      run next rotating initial turn = some value → (next value).length ∣ period) :
    Nonterminating next rotating initial ∧ PeriodicFrom next rotating initial first (last - first) := by
  apply rotating_return_periodic next initial order state firstPresent lastPresent
  intro turn lower upper value present
  exact (counts turn lower upper value present).trans phase.dvd'

theorem return_mod_lcm_periodic (next : S → List S) (initial : S)
    {first last : Nat} (order : first < last) (state : S)
    (firstPresent : run next rotating initial first = some state)
    (lastPresent : run next rotating initial last = some state)
    (phase : Nat.ModEq (segmentPeriod next rotating initial first last) first last) :
    Nonterminating next rotating initial ∧ PeriodicFrom next rotating initial first (last - first) :=
  return_mod_common_period next initial order state firstPresent lastPresent phase
    (fun _ lower upper _ present => arity_dvd_segmentPeriod next rotating initial ⟨lower, upper⟩ present)

theorem return_mod_prefix_lcm_periodic (next : S → List S) (initial : S)
    {first last : Nat} (order : first < last) (state : S)
    (firstPresent : run next rotating initial first = some state)
    (lastPresent : run next rotating initial last = some state)
    (phase : Nat.ModEq (segmentPeriod next rotating initial 0 last) first last) :
    Nonterminating next rotating initial ∧ PeriodicFrom next rotating initial first (last - first) :=
  return_mod_common_period next initial order state firstPresent lastPresent phase
    (fun _ _ upper _ present => arity_dvd_segmentPeriod next rotating initial ⟨Nat.zero_le _, upper⟩ present)

theorem finite_run_never_claimed (next : S → List S) (initial : S)
    {ending first last period : Nat} (ended : EndsAt next rotating initial ending)
    (order : first < last) (state : S)
    (firstPresent : run next rotating initial first = some state)
    (lastPresent : run next rotating initial last = some state)
    (counts : ∀ turn, first ≤ turn → turn < last → ∀ value,
      run next rotating initial turn = some value → (next value).length ∣ period) :
    ¬ Nat.ModEq period first last := by
  intro phase
  exact ended_not_nonterminating next rotating initial ended
    (return_mod_common_period next initial order state firstPresent lastPresent phase counts).1

end Mettapedia.Machines.ScheduledRun
