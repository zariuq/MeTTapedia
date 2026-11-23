import Mathlib.Tactic

/-!
# Best early decisions from a partial observation

A cheap observation need not determine a costly predicate. Its best
one-sided test is whether the predicate is possible anywhere in the fiber
of histories still consistent with the observation. For numeric gates the
best threshold is the least reachable value at which the predicate can be
true. A bound on an unread quantity is one way to calculate that value;
the formula changes if the reachable pairs are correlated.

The work saved by changing a threshold is charged only at measurements
actually made, not at every integer between the thresholds. The model
changes when a previously excluded history becomes reachable.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ObservationThreshold

section Observations

variable {State Observation : Type*}

def possibleHit (observe : State → Observation) (possible due : State → Prop)
    (readout : Observation) : Prop :=
  ∃ state, possible state ∧ observe state = readout ∧ due state

/-- Every no-false-negative gate keeps the whole shadow of the true
states. This identifies the exact information needed for an early skip. -/
theorem gate_iff_contains_shadow (observe : State → Observation)
    (possible due : State → Prop) (gate : Observation → Prop) :
    (∀ state, possible state → (gate (observe state) ∧ due state ↔ due state)) ↔
      ∀ readout, possibleHit observe possible due readout → gate readout := by
  constructor
  · rintro exact readout ⟨state, valid, rfl, hit⟩
    exact ((exact state valid).mpr hit).1
  · intro largest state allowed
    refine ⟨And.right, fun hit => ⟨?_, hit⟩⟩
    exact largest _ ⟨state, allowed, rfl, hit⟩

theorem refining_observation_can_only_remove_false_alarms {Finer : Type*}
    (see : State → Finer) (forget : Finer → Observation) (possible due : State → Prop)
    (token : Finer) (hit : possibleHit see possible due token) :
    possibleHit (forget ∘ see) possible due (forget token) := by
  obtain ⟨state, valid, readout, dueAtState⟩ := hit
  exact ⟨state, valid, congrArg forget readout, dueAtState⟩

end Observations

/-- Checking only when `cutoff ≤ visible` misses no possible trigger. -/
def SafeBelow (candidate : Nat → Prop) (cutoff : Nat) : Prop :=
  ∀ visible, candidate visible → cutoff ≤ visible

noncomputable def firstPossible (candidate : Nat → Prop) (witness : ∃ x, candidate x) : Nat := by
  classical
  exact Nat.find witness

theorem firstPossible_witness (candidate : Nat → Prop) (witness : ∃ x, candidate x) :
    candidate (firstPossible candidate witness) := by
  classical
  exact Nat.find_spec witness

/-- The maximal safe cutoff is not an approximation. If raised even once,
the history witnessing the first possible trigger is omitted. -/
theorem safeBelow_iff_le_first (candidate : Nat → Prop) (witness : ∃ x, candidate x)
    (cutoff : Nat) : SafeBelow candidate cutoff ↔ cutoff ≤ firstPossible candidate witness := by
  classical
  constructor
  · intro all
    exact all _ (firstPossible_witness candidate witness)
  · intro lower visible hit
    exact lower.trans (Nat.find_min' witness hit)

theorem every_cutoff_safe_iff (candidate : Nat → Prop) :
    (∀ cutoff, SafeBelow candidate cutoff) ↔ ¬ ∃ x, candidate x := by
  constructor
  · rintro all ⟨x, due⟩
    exact (Nat.not_succ_le_self x) (all (x + 1) x due)
  · intro none _ x hit
    exact (none ⟨x, hit⟩).elim

/-- `floor` bounds the cheap reading from below, and `limit` bounds the
unread addend from above. The rectangular envelope assumes every pair
satisfying these bounds is still possible. -/
def boxHit (floor limit budget visible : Nat) : Prop :=
  floor ≤ visible ∧ ∃ hidden ≤ limit, budget ≤ visible + hidden

theorem boxHit_iff (floor limit budget visible : Nat) :
    boxHit floor limit budget visible ↔ max floor (budget - limit) ≤ visible := by
  rw [boxHit, max_le_iff]
  constructor
  · rintro ⟨above, hidden, bounded, due⟩
    exact ⟨above, by omega⟩
  · rintro ⟨above, ready⟩
    exact ⟨above, limit, le_rfl, by omega⟩

theorem cutoff_in_box (floor limit budget cutoff : Nat) :
    SafeBelow (boxHit floor limit budget) cutoff ↔ cutoff ≤ max floor (budget - limit) := by
  constructor
  · intro safe
    exact safe _ ((boxHit_iff floor limit budget _).mpr le_rfl)
  · intro safe visible hit
    exact safe.trans ((boxHit_iff floor limit budget visible).mp hit)

/-- If fewer pairs are reachable, a sound cutoff for the entire box can
still be used. It need not be the best cutoff for the actual histories. -/
theorem cutoff_transfers_to_subset (candidate envelope : Nat → Prop)
    (cutoff : Nat) (subset : ∀ x, candidate x → envelope x)
    (safe : SafeBelow envelope cutoff) : SafeBelow candidate cutoff :=
  fun x hit => safe x (subset x hit)

def checked (cutoff : Nat) (measurements : List Nat) : Nat :=
  (measurements.filter fun x => decide (cutoff ≤ x)).length

def inGap (low high : Nat) (measurements : List Nat) : Nat :=
  (measurements.filter fun x => decide (low ≤ x ∧ x < high)).length

/-- Raising a cutoff avoids exactly the checks at inputs in the half-open
gap. It saves nothing on a run that does not visit that gap. -/
theorem checked_difference (measurements : List Nat) (low high : Nat) (order : low ≤ high) :
    checked low measurements = checked high measurements + inGap low high measurements := by
  induction measurements with
  | nil => rfl
  | cons value rest ih =>
      by_cases atHigh : high ≤ value
      · have atLow := order.trans atHigh
        have notInside := Nat.not_lt.mpr atHigh
        simp [checked, inGap, atHigh, atLow, notInside] at ih ⊢
        omega
      · have belowHigh := Nat.lt_of_not_ge atHigh
        by_cases atLow : low ≤ value <;>
          simp [checked, inGap, atHigh, belowHigh, atLow] at ih ⊢ <;> omega

namespace Controls

theorem old_bound_initially_safe : SafeBelow (boxHit 0 2 10) 8 := by
  rw [cutoff_in_box]
  decide

/-- The visible reading can stay put while an unread allocation changes
the decision, so a previously safe threshold may cease to be safe. -/
theorem unread_change_can_make_same_readout_due :
    ¬ boxHit 0 2 10 7 ∧ boxHit 0 3 10 7 ∧ 7 < 8 := by
  simp [boxHit_iff]

theorem some_runs_do_not_pay_for_a_conservative_cutoff :
    checked 4 [0, 3, 8, 9] = checked 8 [0, 3, 8, 9] ∧
      checked 4 [0, 6, 8, 9] = checked 8 [0, 6, 8, 9] + 1 := by decide

end Controls
end Mettapedia.Machines.ObservationThreshold
