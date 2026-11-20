import Mettapedia.Machines.ScheduledRun.Finite

/-!
# Prefix periods learned from actual successor counts

The tracker starts at one. Canonical choice leaves it unchanged; rotating
choice joins a positive count by LCM. A terminal/absent observation contributes
no choice and leaves the period unchanged, matching `run_period` at count zero.
Natural arithmetic here has no overflow-disabled sentinel.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ScheduledRun

def updatePeriod (mode : Mode) (period count : Nat) : Nat :=
  match mode with
  | .canonical => period
  | .rotating => if count = 0 then period else Nat.lcm period count

universe u
variable {S : Type u}

def observedArity (next : S → List S) (observation : Option S) : Nat :=
  observation.elim 0 (fun state => (next state).length)

def prefixPeriod (next : S → List S) (mode : Mode) (trace : Nat → Option S) : Nat → Nat
  | 0 => 1
  | turn + 1 => updatePeriod mode (prefixPeriod next mode trace turn) (observedArity next (trace turn))

theorem updatePeriod_pos (mode : Mode) {period : Nat} (count : Nat) (positive : 0 < period) :
    0 < updatePeriod mode period count := by
  cases mode with
  | canonical => exact positive
  | rotating =>
    by_cases empty : count = 0
    · simpa [updatePeriod, empty] using positive
    · simpa [updatePeriod, empty] using Nat.lcm_pos positive (Nat.pos_of_ne_zero empty)

theorem dvd_updatePeriod (mode : Mode) (period count : Nat) : period ∣ updatePeriod mode period count := by
  cases mode with
  | canonical => exact dvd_rfl
  | rotating =>
    by_cases empty : count = 0
    · simp [updatePeriod, empty]
    · simpa [updatePeriod, empty] using Nat.dvd_lcm_left period count

theorem count_dvd_updatePeriod (period : Nat) {count : Nat} (positive : 0 < count) :
    count ∣ updatePeriod .rotating period count := by
  simp only [updatePeriod, if_neg (Nat.ne_of_gt positive)]
  exact Nat.dvd_lcm_right period count

theorem prefixPeriod_pos (next : S → List S) (mode : Mode) (trace : Nat → Option S) (turn : Nat) :
    0 < prefixPeriod next mode trace turn := by
  induction turn with
  | zero => exact Nat.zero_lt_one
  | succ turn ih => exact updatePeriod_pos mode _ ih

theorem prefixPeriod_dvd_add (next : S → List S) (mode : Mode) (trace : Nat → Option S)
    (turn offset : Nat) : prefixPeriod next mode trace turn ∣ prefixPeriod next mode trace (turn + offset) := by
  induction offset with
  | zero => exact dvd_rfl
  | succ offset ih =>
    exact ih.trans (dvd_updatePeriod mode _ (observedArity next (trace (turn + offset))))

theorem prefixPeriod_dvd_of_le (next : S → List S) (mode : Mode) (trace : Nat → Option S)
    {early late : Nat} (order : early ≤ late) :
    prefixPeriod next mode trace early ∣ prefixPeriod next mode trace late := by
  simpa only [Nat.add_sub_of_le order] using prefixPeriod_dvd_add next mode trace early (late - early)

theorem canonical_prefixPeriod (next : S → List S) (trace : Nat → Option S) (turn : Nat) :
    prefixPeriod next .canonical trace turn = 1 := by
  induction turn with
  | zero => rfl
  | succ turn ih => exact ih

theorem arity_dvd_prefixPeriod (next : S → List S) (trace : Nat → Option S)
    {early late : Nat} (order : early < late) {state : S}
    (present : trace early = some state) (positive : 0 < (next state).length) :
    (next state).length ∣ prefixPeriod next .rotating trace late := by
  have first : (next state).length ∣ prefixPeriod next .rotating trace (early + 1) := by
    change (next state).length ∣ updatePeriod .rotating _ (observedArity next (trace early))
    rw [present]
    exact count_dvd_updatePeriod _ positive
  exact first.trans (prefixPeriod_dvd_of_le next .rotating trace (by omega : early + 1 ≤ late))

theorem prefixPeriod_dvd_common (next : S → List S) (trace : Nat → Option S) (period : Nat) :
    ∀ last, (∀ turn < last, ∀ state, trace turn = some state →
      0 < (next state).length → (next state).length ∣ period) →
      prefixPeriod next .rotating trace last ∣ period := by
  intro last
  induction last with
  | zero => intro _; exact one_dvd _
  | succ last ih =>
    intro counts
    have previous := ih (fun turn inside => counts turn (by omega))
    cases observed : trace last with
    | none => simpa [prefixPeriod, observed, observedArity, updatePeriod] using previous
    | some state =>
      by_cases empty : (next state).length = 0
      · simpa [prefixPeriod, observed, observedArity, updatePeriod, empty] using previous
      · change updatePeriod .rotating _ (observedArity next (trace last)) ∣ period
        rw [observed]
        simpa [observedArity, updatePeriod, empty] using
          Nat.lcm_dvd previous (counts last (by omega) state observed (Nat.pos_of_ne_zero empty))

end Mettapedia.Machines.ScheduledRun
