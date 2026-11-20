import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.Controls

/-!
# Which closures keep a prefixpoint a prefixpoint

A certificate given on fewer pairs and completed by a closure rule is sound when the rule maps coupling
bounds to coupling bounds. Classified:

* **meets** (`couplingBound_min`): the pointwise minimum of two coupling bounds is one; the symmetric
  minimum (`couplingBound_min_swap`) is the case of a bound and its reverse;
* **the triangle** (`couplingBound_triangle`): the infimal convolution of a coupling bound with itself is
  one, by gluing (the tree's sequential composition);
* **pullback along a lumping** (`couplingBound_lift`);
* **convex combination is not a closure** (`average_not_couplingBound`): on `crossing` (two states
  each moving to two absorbing states, all reading alike), two accepted certificates claim distance `0`
  between the two states through two different couplings; their average is no coupling bound, because
  every coupling costs at least `1/2` under it, by a potential (`cost_average_ge`). Its claims are
  still true (`average_claims_true`): the valid upper bounds form a convex set, the prefixpoints do
  not. So a convex combination of accepted certificates is a sound rule for claims, but its result
  cannot be checked as a prefixpoint: both certificates must be checked.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact

open Mettapedia.Cybernetics.ApproximateAdequacy

section Closures

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {A Atom S T : Type*} [Fintype S] [Fintype T]
  {P : LabelledMarkovChain 𝕜 A Atom S} {Q : LabelledMarkovChain 𝕜 A Atom T} {c : 𝕜}

/-- **Meets**: the pointwise minimum of two coupling bounds is a coupling bound. -/
theorem couplingBound_min {m m' : S → T → 𝕜} (first : CouplingBound P Q c m)
    (second : CouplingBound P Q c m') (c_nonneg : 0 ≤ c) :
    CouplingBound P Q c fun s t => min (m s t) (m' s t) where
  nonneg s t := le_min (first.nonneg s t) (second.nonneg s t)
  observe_le i s t := le_min (first.observe_le i s t) (second.observe_le i s t)
  step_le a s t := by
    by_cases order : m s t ≤ m' s t
    · obtain ⟨ω, le⟩ := first.step_le a s t
      refine ⟨ω, ?_⟩
      rw [min_eq_left order]
      exact (mul_le_mul_of_nonneg_left (ω.cost_mono fun x y => min_le_left _ _) c_nonneg).trans le
    · obtain ⟨ω, le⟩ := second.step_le a s t
      refine ⟨ω, ?_⟩
      rw [min_eq_right (le_of_lt (not_le.mp order))]
      exact (mul_le_mul_of_nonneg_left (ω.cost_mono fun x y => min_le_right _ _) c_nonneg).trans le

/-- **The triangle**: the infimal convolution of a coupling bound of a chain with itself is a coupling
bound, by the tree's sequential composition. -/
theorem couplingBound_triangle [Nonempty S] {P : LabelledMarkovChain 𝕜 A Atom S} {m : S → S → 𝕜}
    (bound : CouplingBound P P c m) (c_nonneg : 0 ≤ c) :
    CouplingBound P P c (infConvolution m m) :=
  bound.comp bound c_nonneg

end Closures

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.UpToControls

open Mettapedia.Cybernetics.ApproximateAdequacy
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Controls

/-! ## Convex combination: a counterexample -/

/-- `0` moves to `2, 3`, `1` moves to `4, 5`, each with probability `1/2`; `2, 3, 4, 5` stay. -/
def crossingTrans : Fin 6 → Fin 6 → ℚ :=
  ![![0, 0, 1 / 2, 1 / 2, 0, 0], ![0, 0, 0, 0, 1 / 2, 1 / 2], ![0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]

theorem crossingTrans_nonneg : ∀ s x, 0 ≤ crossingTrans s x := by decide +kernel

theorem crossingTrans_total : ∀ s, ∑ x, crossingTrans s x = 1 := by decide +kernel

/-- **Two states each moving to two absorbing states**, every state reading alike. -/
def crossing : LabelledMarkovChain ℚ Unit Unit (Fin 6) where
  trans _ := crossingTrans
  isDistribution _ s := ⟨crossingTrans_nonneg s, crossingTrans_total s⟩
  observe _ _ := 0

/-- Zero on the diagonal, between `0` and `1`, and on the pairs `zero` relates; one elsewhere. -/
def kernelVia (zero : Fin 6 → Fin 6 → Bool) : Fin 6 → Fin 6 → ℚ := fun u v =>
  if u = v ∨ (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨ zero u v = true then 0 else 1

/-- The first certificate: `2` with `4` and `3` with `5`. -/
def straight : Fin 6 → Fin 6 → Bool := fun u v =>
  (u = 2 ∧ v = 4) || (u = 4 ∧ v = 2) || (u = 3 ∧ v = 5) || (u = 5 ∧ v = 3)

/-- The second certificate: `2` with `5` and `3` with `4`. -/
def crossed : Fin 6 → Fin 6 → Bool := fun u v =>
  (u = 2 ∧ v = 5) || (u = 5 ∧ v = 2) || (u = 3 ∧ v = 4) || (u = 4 ∧ v = 3)

/-- A table listed at `(0, 1)` only. -/
def listedAt01 (θ : Fin 6 → Fin 6 → ℚ) : Unit → Fin 6 → Fin 6 → Option (Fin 6 → Fin 6 → ℚ) :=
  fun _ s t => if s = 0 ∧ t = 1 then some θ else none

/-- The coupling matching `2` with `4` and `3` with `5`. -/
def straightTable : Fin 6 → Fin 6 → ℚ := fun u v =>
  if (u = 2 ∧ v = 4) ∨ (u = 3 ∧ v = 5) then 1 / 2 else 0

/-- The coupling matching `2` with `5` and `3` with `4`. -/
def crossedTable : Fin 6 → Fin 6 → ℚ := fun u v =>
  if (u = 2 ∧ v = 5) ∨ (u = 3 ∧ v = 4) then 1 / 2 else 0

def straightCert : Prefixpoint Unit (Fin 6) := ⟨kernelVia straight, listedAt01 straightTable⟩

def crossedCert : Prefixpoint Unit (Fin 6) := ⟨kernelVia crossed, listedAt01 crossedTable⟩

theorem straightCert_accepted : check crossing discount straightCert = true := by decide +kernel

theorem crossedCert_accepted : check crossing discount crossedCert = true := by decide +kernel

/-- **The average of the two kernels.** -/
def average : Fin 6 → Fin 6 → ℚ := fun u v => (kernelVia straight u v + kernelVia crossed u v) / 2

/-- The potentials: `1/2` on `2` and `3`, zero elsewhere, on both sides. -/
def potential : Fin 6 → ℚ := ![0, 0, 1 / 2, 1 / 2, 0, 0]

theorem potential_le : ∀ u v, potential u - potential v ≤ average u v := by decide +kernel

theorem potential_gain :
    expect (crossing.trans () 0) potential - expect (crossing.trans () 1) potential = 1 / 2 := by
  decide +kernel

/-- **Every coupling of the two states' successors costs at least `1/2` under the average.** -/
theorem cost_average_ge (ω : Coupling (crossing.trans () 0) (crossing.trans () 1)) :
    1 / 2 ≤ ω.cost average := by
  rw [← potential_gain, ω.expect_sub_expect]
  unfold Coupling.cost
  exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
    mul_le_mul_of_nonneg_left (potential_le x y) (ω.nonneg x y)

/-- **The average of two accepted prefixpoints is not a coupling bound.** -/
theorem average_not_couplingBound : ¬ CouplingBound crossing crossing discount average := by
  intro bound
  obtain ⟨ω, le⟩ := bound.step_le () 0 1
  have zero : average 0 1 = 0 := by decide +kernel
  rw [zero] at le
  have cost := cost_average_ge ω
  have positive : (0 : ℚ) < discount := by norm_num [discount]
  nlinarith

/-- **Its claims are true**: the metric is below both kernels, hence below their average. -/
theorem average_claims_true (u v : Fin 6) :
    bisimulationMetric (realChain crossing) (realChain crossing) (discount : ℝ) u v ≤
      (average u v : ℝ) := by
  have first := check_sound straightCert_accepted discount_nonneg u v
  have second := check_sound crossedCert_accepted discount_nonneg u v
  change _ ≤ ((kernelVia straight u v : ℚ) : ℝ) at first
  change _ ≤ ((kernelVia crossed u v : ℚ) : ℝ) at second
  simp only [average, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
  linarith

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.UpToControls
