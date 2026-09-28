import Mathlib.Tactic

/-!
# Work, span, and the waves of a level schedule

A dependency structure whose occurrences have unit duration can be presented
by its **levels**: the widths `w₁, …, w_L` of successive antichains, each of
which may run in parallel once the previous one is done.  Three quantities are
then distinct, and this module keeps them apart:

* **work** `∑ wᵢ` — how much is done, independent of any schedule;
* **span** `L` — the critical path, a property of the dependency structure;
* **waves** — the rounds a *chosen* schedule takes on `p` processors, here the
  level-synchronous schedule `∑ ⌈wᵢ / p⌉`.

The theorems are Brent-type bounds, proved exactly in `ℕ`:

```
span ≤ waves p            work ≤ p · waves p            p · waves p ≤ work + (p − 1) · span
```

so waves sit between `max (work / p) span` and `work / p + span`.  With one
processor waves equal work (`waves_one`); with enough processors they equal
span (`waves_eq_span_of_wide`).

**Assumptions**, stated rather than implied: unit-duration occurrences, `p`
identical processors, a level-synchronous greedy schedule, and **no
scheduling overhead**.  The ideal bounds say nothing about overhead, and
`overhead_can_defeat_parallelism` shows a per-wave synchronisation cost
making the parallel schedule slower than the serial one.  Elapsed time is a
measurement of a realisation, not a consequence of these bounds.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.LevelSchedule

/-- Rounds needed to run `w` unit occurrences on `p` processors. -/
def ceilDiv (w p : ℕ) : ℕ := (w + p - 1) / p

/-- Total work. -/
def work (levels : List ℕ) : ℕ := levels.sum

/-- The critical path: one unit per level. -/
def span (levels : List ℕ) : ℕ := levels.length

/-- Rounds of the level-synchronous schedule on `p` processors. -/
def waves (p : ℕ) (levels : List ℕ) : ℕ := (levels.map fun w => ceilDiv w p).sum

theorem le_mul_ceilDiv {p : ℕ} (hp : 0 < p) (w : ℕ) : w ≤ p * ceilDiv w p := by
  have h1 := Nat.div_add_mod (w + p - 1) p
  have h2 := Nat.mod_lt (w + p - 1) hp
  unfold ceilDiv
  generalize p * ((w + p - 1) / p) = X at *
  omega

theorem mul_ceilDiv_le {p : ℕ} (hp : 0 < p) (w : ℕ) : p * ceilDiv w p ≤ w + (p - 1) := by
  have h1 := Nat.div_add_mod (w + p - 1) p
  unfold ceilDiv
  generalize p * ((w + p - 1) / p) = X at *
  omega

theorem one_le_ceilDiv {p w : ℕ} (hp : 0 < p) (hw : 0 < w) : 1 ≤ ceilDiv w p :=
  Nat.div_pos (by omega) hp

theorem ceilDiv_eq_one {p w : ℕ} (hw : 0 < w) (hwp : w ≤ p) : ceilDiv w p = 1 := by
  have hp : 0 < p := lt_of_lt_of_le hw hwp
  refine le_antisymm ?_ (one_le_ceilDiv hp hw)
  have : (w + p - 1) / p < 2 := (Nat.div_lt_iff_lt_mul hp).2 (by omega)
  unfold ceilDiv; omega

theorem ceilDiv_one (w : ℕ) : ceilDiv w 1 = w := by simp [ceilDiv]

/-! ## The bounds -/

/-- **Span is a lower bound on waves**: every nonempty level takes a round. -/
theorem span_le_waves {p : ℕ} (hp : 0 < p) :
    ∀ levels : List ℕ, (∀ w ∈ levels, 0 < w) → span levels ≤ waves p levels
  | [], _ => by simp [span, waves]
  | w :: rest, h => by
      have := span_le_waves hp rest (fun x hx => h x (List.mem_cons_of_mem _ hx))
      have hw := one_le_ceilDiv hp (h w List.mem_cons_self)
      simp only [span, waves, List.length_cons, List.map_cons, List.sum_cons] at *
      omega

/-- **Work over processors is a lower bound on waves.** -/
theorem work_le_mul_waves {p : ℕ} (hp : 0 < p) :
    ∀ levels : List ℕ, work levels ≤ p * waves p levels
  | [] => by simp [work, waves]
  | w :: rest => by
      have := work_le_mul_waves hp rest
      have hw := le_mul_ceilDiv hp w
      simp only [work, waves, List.map_cons, List.sum_cons, mul_add] at *
      omega

/-- **Brent's bound**: `p · waves ≤ work + (p − 1) · span`. -/
theorem mul_waves_le {p : ℕ} (hp : 0 < p) :
    ∀ levels : List ℕ, p * waves p levels ≤ work levels + (p - 1) * span levels
  | [] => by simp [work, waves, span]
  | w :: rest => by
      have := mul_waves_le hp rest
      have hw := mul_ceilDiv_le hp w
      simp only [work, waves, span, List.map_cons, List.sum_cons, List.length_cons,
        mul_add] at *
      nlinarith

/-- One processor: the schedule is serial, and waves are work. -/
theorem waves_one (levels : List ℕ) : waves 1 levels = work levels := by
  simp [waves, work, ceilDiv_one]

/-- Enough processors: waves are span. -/
theorem waves_eq_span_of_wide {p : ℕ} :
    ∀ levels : List ℕ, (∀ w ∈ levels, 0 < w ∧ w ≤ p) → waves p levels = span levels
  | [], _ => by simp [waves, span]
  | w :: rest, h => by
      have hrest := waves_eq_span_of_wide rest (fun x hx => h x (List.mem_cons_of_mem _ hx))
      have hw := h w List.mem_cons_self
      simp only [waves, span, List.map_cons, List.sum_cons, List.length_cons] at *
      rw [ceilDiv_eq_one hw.1 hw.2, hrest]; omega

/-! ## Controls -/

/-- **Span and waves differ on bounded processors**: a single level of four
independent occurrences has span `1`, work `4`, and takes `2` waves on two
processors. -/
theorem wide_level_on_two :
    span [4] = 1 ∧ work [4] = 4 ∧ waves 2 [4] = 2 := by decide

/-- **Work and span differ**: the same work of four, as one wide level or as
a chain, has span `1` or `4`. -/
theorem same_work_different_span :
    work [4] = work [1, 1, 1, 1] ∧ span [4] ≠ span [1, 1, 1, 1] := by decide

/-- Elapsed time of a realisation that pays `overhead` per round of
synchronisation. -/
def elapsedWithOverhead (overhead p : ℕ) (levels : List ℕ) : ℕ :=
  waves p levels * (1 + overhead)

/-- **Negative control: the ideal bounds exclude overhead.**  Two independent
occurrences take one wave on two processors and two on one; with a
synchronisation cost of two units per parallel round, the parallel run takes
`3` against the serial run's `2`. -/
theorem overhead_can_defeat_parallelism :
    waves 2 [2] < waves 1 [2] ∧
      work [2] < elapsedWithOverhead 2 2 [2] := by decide

end Mettapedia.Algebra.LevelSchedule

#print axioms Mettapedia.Algebra.LevelSchedule.mul_waves_le
#print axioms Mettapedia.Algebra.LevelSchedule.span_le_waves
#print axioms Mettapedia.Algebra.LevelSchedule.overhead_can_defeat_parallelism
