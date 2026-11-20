import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Upper
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Lower

/-!
# Exact when the certificates meet; otherwise not decided

An accepted upper certificate and a lower certificate bracket the metric at a pair. Two answers
are read from the bracket:

* **a measurement** (`measure`): the exact value when the two bounds meet, otherwise the interval,
  which asserts the bracket and nothing more;
* **a verdict on "the distance is at most `ε`"** (`within`), with three outcomes: it holds (the
  upper bound is at most `ε`), it fails (the lower bound exceeds `ε`), or it is not decided (the
  interval contains `ε` in its upper part). An interval that does not close is never a refutation.

These follow the shape of the budgeted conversion check of the native types on the step: each
decided outcome is sound (`within_holds`, `within_fails`); "not decided" is exactly the bracket
straddling `ε` (`within_undecided_iff`); tighter evidence never changes a decided verdict
(`within_refine`), and two brackets of the same distance never decide differently
(`within_consistent`).

**With the certificates of this folder** (`measureByTest`, `withinByTest`): the upper bound is an
accepted prefixpoint and the lower bound the gap of a test DAG.
* `bisimulationMetric_eq_of_meet`: if the checker accepts the kernel and the test's gap at a pair
  equals the kernel there, the metric at that pair is that rational, at every discount
  `0 ≤ c ≤ 1`.
* `measureByTest_exact`, `measureByTest_between`, `withinByTest_holds`, `withinByTest_fails`,
  `withinByTest_undecided_iff`: the general laws, read on the real chain.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates

open Mettapedia.Cybernetics.ApproximateAdequacy

/-! ## Two kinds of answers -/

/-- **A measured distance**: an exact value, or an interval that does not close. -/
inductive Measurement where
  | exact (value : ℚ)
  | between (lower upper : ℚ)
  deriving DecidableEq, Repr

/-- **The three outcomes of "the distance is at most `ε`"**. -/
inductive Verdict where
  | holds
  | fails
  | undecided
  deriving DecidableEq, Repr

/-- Measure from a lower and an upper bound: exact when they meet, the interval otherwise. -/
def measure (lower upper : ℚ) : Measurement :=
  if lower = upper then .exact upper else .between lower upper

/-- Decide "at most `ε`" from a lower and an upper bound. -/
def within (lower upper ε : ℚ) : Verdict :=
  if upper ≤ ε then .holds else if ε < lower then .fails else .undecided

section Laws

variable {d : ℝ} {lower upper : ℚ}

/-- **An exact measurement is the distance.** -/
theorem measure_exact (below : (lower : ℝ) ≤ d) (above : d ≤ upper) {r : ℚ}
    (measured : measure lower upper = .exact r) : d = r := by
  unfold measure at measured
  split_ifs at measured with meet
  · obtain rfl : upper = r := Measurement.exact.inj measured
    have meet' : (lower : ℝ) = upper := by exact_mod_cast meet
    exact le_antisymm above (by rw [← meet']; exact below)

/-- **An interval asserts the bracket, and it does not close.** -/
theorem measure_between (below : (lower : ℝ) ≤ d) (above : d ≤ upper) {l u : ℚ}
    (measured : measure lower upper = .between l u) :
    l = lower ∧ u = upper ∧ lower < upper ∧ (l : ℝ) ≤ d ∧ d ≤ u := by
  unfold measure at measured
  split_ifs at measured with meet
  cases measured
  exact ⟨rfl, rfl, lt_of_le_of_ne (by exact_mod_cast below.trans above) meet, below, above⟩

variable {ε : ℚ}

/-- **"Holds" is sound.** -/
theorem within_holds (above : d ≤ upper) (verdict : within lower upper ε = .holds) : d ≤ ε := by
  unfold within at verdict
  split_ifs at verdict with small
  · exact above.trans (by exact_mod_cast small)

/-- **"Fails" is sound**: the distance exceeds `ε`. -/
theorem within_fails (below : (lower : ℝ) ≤ d) (verdict : within lower upper ε = .fails) :
    (ε : ℝ) < d := by
  unfold within at verdict
  split_ifs at verdict with small large
  exact (by exact_mod_cast large : (ε : ℝ) < lower).trans_le below

/-- **"Not decided" is exactly a bracket straddling `ε`.** -/
theorem within_undecided_iff : within lower upper ε = .undecided ↔ ε < upper ∧ lower ≤ ε := by
  unfold within
  split_ifs with small large
  · simp only [false_iff, not_and, not_le]
    intro large'
    exact absurd small (not_le.mpr large')
  · simp only [false_iff, not_and, not_le]
    intro _
    exact large
  · simp only [true_iff]
    exact ⟨not_le.mp small, not_lt.mp large⟩

/-- **Tighter evidence never changes a decided verdict.** -/
theorem within_refine {lower' upper' : ℚ} (raise : lower ≤ lower') (drop : upper' ≤ upper)
    (ordered : lower' ≤ upper') (decided : within lower upper ε ≠ .undecided) :
    within lower' upper' ε = within lower upper ε := by
  unfold within at decided ⊢
  split_ifs at decided ⊢ <;> first | rfl | exact absurd rfl decided | (exfalso; linarith)

/-- **Two brackets of the same distance never decide differently.** -/
theorem within_consistent {lower' upper' : ℚ} (below : (lower : ℝ) ≤ d) (above : d ≤ upper)
    (below' : (lower' : ℝ) ≤ d) (above' : d ≤ upper') (decided : within lower upper ε ≠ .undecided)
    (decided' : within lower' upper' ε ≠ .undecided) :
    within lower upper ε = within lower' upper' ε := by
  have cases_of : ∀ v : Verdict, v ≠ .undecided → v = .holds ∨ v = .fails := by
    intro v; cases v <;> simp
  rcases cases_of _ decided with first | first <;> rcases cases_of _ decided' with second | second
  · rw [first, second]
  · exact absurd (within_holds above first) (not_le.mpr (within_fails below' second))
  · exact absurd (within_holds above' second) (not_le.mpr (within_fails below first))
  · rw [first, second]

end Laws

/-! ## With a prefixpoint and a test -/

section Certificates

variable {A Atom S : Type*} [Fintype S] [DecidableEq S] [Fintype A] [Fintype Atom]

/-- **Measure the distance at a pair** from a prefixpoint and a test; nothing unless the prefixpoint
is accepted and the test evaluates. -/
def measureByTest (P : LabelledMarkovChain ℚ A Atom S) (c : ℚ) (cert : Prefixpoint A S)
    (nodes : List (TestNode A Atom)) (x y : S) : Option Measurement :=
  if check P c cert then
    match testGap P c nodes x y with
    | some (g, _) => some (measure g (cert.kernel x y))
    | none => none
  else none

/-- **Decide "at most `ε`" at a pair** from a prefixpoint and a test; nothing unless the prefixpoint
is accepted and the test evaluates. -/
def withinByTest (P : LabelledMarkovChain ℚ A Atom S) (c : ℚ) (cert : Prefixpoint A S)
    (nodes : List (TestNode A Atom)) (x y : S) (ε : ℚ) : Option Verdict :=
  if check P c cert then
    match testGap P c nodes x y with
    | some (g, _) => some (within g (cert.kernel x y) ε)
    | none => none
  else none

variable {P : LabelledMarkovChain ℚ A Atom S} {c : ℚ} {cert : Prefixpoint A S}
  {nodes : List (TestNode A Atom)} {x y : S}

/-- **The bracket**: an accepted prefixpoint and an evaluated test bracket the metric at the pair, at
every discount `0 ≤ c ≤ 1`. -/
theorem bracket_of_test (accepted : check P c cert = true) {g : ℚ} {d : ℕ}
    (gap : testGap P c nodes x y = some (g, d)) (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) :
    (g : ℝ) ≤ bisimulationMetric (realChain P) (realChain P) (c : ℝ) x y ∧
      bisimulationMetric (realChain P) (realChain P) (c : ℝ) x y ≤ (cert.kernel x y : ℝ) :=
  ⟨testGap_le_bisimulationMetric gap c_nonneg c_le, check_sound accepted c_nonneg x y⟩

/-- **Exact when the certificates meet**: if the checker accepts the kernel and the test's gap at a
pair equals the kernel there, the metric at that pair is that rational, at every discount
`0 ≤ c ≤ 1`. -/
theorem bisimulationMetric_eq_of_meet (accepted : check P c cert = true) {g : ℚ} {d : ℕ}
    (gap : testGap P c nodes x y = some (g, d)) (meet : g = cert.kernel x y) (c_nonneg : 0 ≤ c)
    (c_le : c ≤ 1) : bisimulationMetric (realChain P) (realChain P) (c : ℝ) x y = (g : ℝ) := by
  obtain ⟨below, above⟩ := bracket_of_test accepted gap c_nonneg c_le
  rw [← meet] at above
  exact le_antisymm above below

theorem measureByTest_some {m : Measurement} (measured : measureByTest P c cert nodes x y = some m) :
    check P c cert = true ∧ ∃ g d, testGap P c nodes x y = some (g, d) ∧
      m = measure g (cert.kernel x y) := by
  unfold measureByTest at measured
  split_ifs at measured with accepted
  rcases evaluated : testGap P c nodes x y with _ | ⟨g, d⟩
  · simp [evaluated] at measured
  · simp only [evaluated, Option.some.injEq] at measured
    exact ⟨accepted, g, d, rfl, measured.symm⟩

/-- **An exact measurement is the metric**, at every discount `0 ≤ c ≤ 1`. -/
theorem measureByTest_exact {r : ℚ} (measured : measureByTest P c cert nodes x y = some (.exact r))
    (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) :
    bisimulationMetric (realChain P) (realChain P) (c : ℝ) x y = (r : ℝ) := by
  obtain ⟨accepted, g, d, gap, shape⟩ := measureByTest_some measured
  obtain ⟨below, above⟩ := bracket_of_test accepted gap c_nonneg c_le
  exact measure_exact below above shape.symm

/-- **An interval brackets the metric and does not close**, at every discount `0 ≤ c ≤ 1`. -/
theorem measureByTest_between {l u : ℚ}
    (measured : measureByTest P c cert nodes x y = some (.between l u)) (c_nonneg : 0 ≤ c)
    (c_le : c ≤ 1) :
    l < u ∧ (l : ℝ) ≤ bisimulationMetric (realChain P) (realChain P) (c : ℝ) x y ∧
      bisimulationMetric (realChain P) (realChain P) (c : ℝ) x y ≤ (u : ℝ) := by
  obtain ⟨accepted, g, d, gap, shape⟩ := measureByTest_some measured
  obtain ⟨below, above⟩ := bracket_of_test accepted gap c_nonneg c_le
  obtain ⟨rfl, rfl, lt, below', above'⟩ := measure_between below above shape.symm
  exact ⟨lt, below', above'⟩

theorem withinByTest_some {ε : ℚ} {v : Verdict}
    (verdict : withinByTest P c cert nodes x y ε = some v) :
    check P c cert = true ∧ ∃ g d, testGap P c nodes x y = some (g, d) ∧
      v = within g (cert.kernel x y) ε := by
  unfold withinByTest at verdict
  split_ifs at verdict with accepted
  rcases evaluated : testGap P c nodes x y with _ | ⟨g, d⟩
  · simp [evaluated] at verdict
  · simp only [evaluated, Option.some.injEq] at verdict
    exact ⟨accepted, g, d, rfl, verdict.symm⟩

/-- **"Holds" is sound**, at every discount `0 ≤ c`. -/
theorem withinByTest_holds {ε : ℚ} (verdict : withinByTest P c cert nodes x y ε = some .holds)
    (c_nonneg : 0 ≤ c) :
    bisimulationMetric (realChain P) (realChain P) (c : ℝ) x y ≤ (ε : ℝ) := by
  obtain ⟨accepted, g, d, _, shape⟩ := withinByTest_some verdict
  exact within_holds (check_sound accepted c_nonneg x y) shape.symm

/-- **"Fails" is sound**, at every discount `0 ≤ c ≤ 1`. -/
theorem withinByTest_fails {ε : ℚ} (verdict : withinByTest P c cert nodes x y ε = some .fails)
    (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) :
    (ε : ℝ) < bisimulationMetric (realChain P) (realChain P) (c : ℝ) x y := by
  obtain ⟨_, g, d, gap, shape⟩ := withinByTest_some verdict
  exact within_fails (testGap_le_bisimulationMetric gap c_nonneg c_le) shape.symm

/-- **"Not decided" is exactly the bracket straddling `ε`**; it asserts nothing about the distance
beyond the bracket. -/
theorem withinByTest_undecided_iff {ε : ℚ} (accepted : check P c cert = true) {g : ℚ} {d : ℕ}
    (gap : testGap P c nodes x y = some (g, d)) :
    withinByTest P c cert nodes x y ε = some .undecided ↔ ε < cert.kernel x y ∧ g ≤ ε := by
  unfold withinByTest
  rw [if_pos accepted]
  simp only [gap, Option.some.injEq]
  exact within_undecided_iff

end Certificates

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates
