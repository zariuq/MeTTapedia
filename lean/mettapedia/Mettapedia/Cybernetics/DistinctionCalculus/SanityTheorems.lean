import Mettapedia.Cybernetics.DistinctionCalculus.EvidenceContexts
import Mettapedia.Cybernetics.DistinctionCalculus.Ledger
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Sanity theorems for distinction, pattern and resonance

Goertzel, *Hyperseed in the d-Calculus*, ch. 4. Statement identifiers `HS4.*`
are the chapter's. The exact coarsening account `HS4.01` and the valuation law
of `HS4.02` are in `Ledger` (rational observers); this module adds the rest.

* **Weakness** (`HS4.02`, `HS4.03`). Pair masses of relations obey
  inclusion–exclusion; on real observers expected indistinction is the integral
  of its threshold masses (`graphtropy_eq_integral_layers`). A change of
  sampling measure moves it by at most twice the total variation
  (`abs_graphtropy_sub_le_measure`); identity observers show the bound is
  needed.
* **A concrete pattern score** (`HS4.Score`, `HS4.04`–`HS4.06`). The fraction of
  baseline distinction removed, less a task-weighted cost, is bounded, has an
  exact marginal value, attains a maximum on the compact polytope of coherent
  coarsenings (`exists_max_score`), and closure is the least-cost coherent
  repair. In the worked model two useful merges compose badly after closure,
  and the graded optimum `1/30` carries a two-slack certificate.
* **Dissonance** (`HS4.07`–`HS4.10`). In any real inner product space,
  `R²/M² = 1 − 2H` and `D/M = 1 − √(1 − 2H)` with `H` the squared
  directional-distinction bracket; `H ≤ D/M ≤ 2H`; interference is
  `M²(1 − 2H − Σ π²)`. A distinction kernel is a chord distance of unit vectors
  iff `1 − 2δ²` is positive semidefinite (`exists_unit_vectors_iff`); the rank
  claims are not formalized. Isometries preserve all quantities; resonance and
  dissonance move Lipschitz in the contributions.
* **Change of algebra** (`HS4.11`, `HS4.12`). Peak weakness moves along quantale
  morphisms (`QuantaleHom.map_weakness`); a strict homomorphism, one that also
  keeps the unit, commutes with max-tensor composition and the path star. A
  scalar map commutes with every finite expectation iff it is affine. Squaring keeps the
  max-product quantale and breaks expectation; the square root breaks metric
  coherence.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.DistinctionCalculus

universe u v w

/-! ## Weakness: relations, layers and attention (`HS4.02`, `HS4.03`) -/

section Weakness

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {V : Type u} [Fintype V]

/-- The pair mass `W_μ(H) = ⟨μ|1_H|μ⟩` of a relation. -/
def pairMass (p : Distribution V R) (H : V → V → Prop) [DecidableRel H] : R :=
  p.pairAverage fun x y => if H x y then 1 else 0

/-- **Inclusion–exclusion for pair masses** (`HS4.02`). -/
theorem pairMass_union (p : Distribution V R) (H K : V → V → Prop) [DecidableRel H]
    [DecidableRel K] :
    pairMass p (fun x y => H x y ∨ K x y) =
      pairMass p H + pairMass p K - pairMass p (fun x y => H x y ∧ K x y) := by
  unfold pairMass
  rw [eq_sub_iff_add_eq, ← p.pairAverage_add, ← p.pairAverage_add]
  congr 1
  funext x y
  by_cases h : H x y <;> by_cases k : K x y <;> simp [h, k]

/-- Total variation `½ Σ |μ − ν|`. -/
def totalVariation (p q : Distribution V R) : R := (∑ x, |p.weight x - q.weight x|) / 2

/-- Expectations of functions in `[0, 1]` differ by at most the total variation. -/
theorem abs_expectation_sub_le (p q : Distribution V R) (f : V → R)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    |∑ x, (p.weight x - q.weight x) * f x| ≤ totalVariation p q := by
  have centre : ∑ x, (p.weight x - q.weight x) * f x =
      ∑ x, (p.weight x - q.weight x) * (f x - 1 / 2) := by
    have zero : ∑ x, (p.weight x - q.weight x) = 0 := by
      rw [Finset.sum_sub_distrib, p.normalized, q.normalized, sub_self]
    have : ∑ x, (p.weight x - q.weight x) * (f x - 1 / 2) =
        ∑ x, (p.weight x - q.weight x) * f x - (∑ x, (p.weight x - q.weight x)) * (1 / 2) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [this, zero, zero_mul, sub_zero]
  rw [centre, totalVariation, Finset.sum_div]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [abs_mul]
  have : |f x - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [(hf x).1], by linarith [(hf x).2]⟩
  calc |p.weight x - q.weight x| * |f x - 1 / 2| ≤ |p.weight x - q.weight x| * (1 / 2) :=
        mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = |p.weight x - q.weight x| / 2 := by ring

/-- **Changing the sampling measure** (`HS4.03`): `|g_μ(α) − g_ν(α)| ≤ 2 TV(μ, ν)`. -/
theorem abs_graphtropy_sub_le_measure (p q : Distribution V R) (a : Tolerance V R) :
    |p.graphtropy a - q.graphtropy a| ≤ 2 * totalVariation p q := by
  have split : p.graphtropy a - q.graphtropy a =
      ∑ x, (p.weight x - q.weight x) * (∑ y, a.similarity x y * p.weight y) +
        ∑ y, (p.weight y - q.weight y) * (∑ x, q.weight x * a.similarity x y) := by
    simp only [Distribution.graphtropy, Distribution.pairAverage, Finset.mul_sum]
    rw [Finset.sum_comm (f := fun y x => (p.weight y - q.weight y) * (q.weight x * a.similarity x y)),
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  have row : ∀ x, 0 ≤ ∑ y, a.similarity x y * p.weight y ∧ ∑ y, a.similarity x y * p.weight y ≤ 1 :=
    fun x => ⟨Finset.sum_nonneg fun y _ => mul_nonneg (a.nonnegative x y) (p.nonnegative y),
      (Finset.sum_le_sum fun y _ => mul_le_of_le_one_left (p.nonnegative y) (a.bounded x y)).trans
        p.normalized.le⟩
  have column : ∀ y, 0 ≤ ∑ x, q.weight x * a.similarity x y ∧
      ∑ x, q.weight x * a.similarity x y ≤ 1 :=
    fun y => ⟨Finset.sum_nonneg fun x _ => mul_nonneg (q.nonnegative x) (a.nonnegative x y),
      (Finset.sum_le_sum fun x _ => mul_le_of_le_one_right (q.nonnegative x) (a.bounded x y)).trans
        q.normalized.le⟩
  rw [split]
  refine (abs_add_le _ _).trans ?_
  linarith [abs_expectation_sub_le p q _ row, abs_expectation_sub_le p q _ column]

/-- **Changing measure and kernel** (`HS4.03`):
`|g_μ(α) − g_ν(β)| ≤ ⟨μ| |α − β| |μ⟩ + 2 TV(μ, ν)`. -/
theorem abs_graphtropy_sub_le (p q : Distribution V R) (a b : Tolerance V R) :
    |p.graphtropy a - q.graphtropy b| ≤
      p.pairAverage (fun x y => |a.similarity x y - b.similarity x y|) + 2 * totalVariation p q := by
  have kernel : |p.graphtropy a - p.graphtropy b| ≤
      p.pairAverage fun x y => |a.similarity x y - b.similarity x y| := by
    rw [Distribution.graphtropy, Distribution.graphtropy, ← p.pairAverage_sub]
    exact p.abs_pairAverage_le _
  calc |p.graphtropy a - q.graphtropy b|
      = |(p.graphtropy a - p.graphtropy b) + (p.graphtropy b - q.graphtropy b)| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add kernel (abs_graphtropy_sub_le_measure p q b))

end Weakness

/-- **Attention is not discrimination** (`HS4.03`): the identity observer on two
tokens has `g = ½` under the uniform measure and `g = 1` under a point mass. -/
theorem attention_moves_graphtropy :
    (Distribution.uniform Bool ℚ).graphtropy (Tolerance.ofReport id) = 1 / 2 ∧
      Examples.pointMass.graphtropy (Tolerance.ofReport id) = 1 := by
  constructor
  · rw [Distribution.graphtropy, EvidenceExamples.uniform_bool_pairAverage]
    norm_num [Tolerance.ofReport]
  · simp [Distribution.graphtropy, Distribution.pairAverage, Examples.pointMass, Tolerance.ofReport]

/-! ### Layer decomposition on real observers (`HS4.02`) -/

theorem integral_layer {a : ℝ} (h₀ : 0 ≤ a) (h₁ : a ≤ 1) :
    ∫ t in (0 : ℝ)..1, (if t ≤ a then (1 : ℝ) else 0) = a := by
  have anti : Antitone fun t : ℝ => if t ≤ a then (1 : ℝ) else 0 := by
    intro s t st
    by_cases ht : t ≤ a
    · simp [ht, st.trans ht]
    · simp only [ht, if_false]
      split_ifs <;> norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := a) anti.intervalIntegrable
    anti.intervalIntegrable]
  have lower : ∫ t in (0 : ℝ)..a, (if t ≤ a then (1 : ℝ) else 0) = ∫ t in (0 : ℝ)..a, (1 : ℝ) :=
    intervalIntegral.integral_congr fun t ht => by
      rw [Set.uIcc_of_le h₀] at ht
      simp [ht.2]
  have upper : ∫ t in a..1, (if t ≤ a then (1 : ℝ) else 0) = ∫ t in a..1, (0 : ℝ) :=
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => by
      rw [Set.uIoc_of_le h₁] at ht
      simp [not_le.mpr ht.1])
  rw [lower, upper]
  simp

/-- **Layer decomposition** (`HS4.02`): `g_μ(α) = ∫₀¹ W_μ{α ≥ t} dt`. -/
theorem graphtropy_eq_integral_layers {V : Type u} [Fintype V] (p : Distribution V ℝ)
    (a : Tolerance V ℝ) :
    p.graphtropy a = ∫ t in (0 : ℝ)..1, p.pairAverage fun x y => if t ≤ a.similarity x y then 1 else 0 := by
  have term : ∀ x y, Antitone fun t : ℝ =>
      p.weight x * p.weight y * (if t ≤ a.similarity x y then (1 : ℝ) else 0) := by
    intro x y s t st
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (p.nonnegative x) (p.nonnegative y))
    by_cases ht : t ≤ a.similarity x y
    · simp [ht, st.trans ht]
    · simp only [ht, if_false]
      split_ifs <;> norm_num
  have row : ∀ x, Antitone fun t : ℝ =>
      ∑ y, p.weight x * p.weight y * (if t ≤ a.similarity x y then (1 : ℝ) else 0) :=
    fun x _ _ st => Finset.sum_le_sum fun y _ => term x y st
  show _ = ∫ t in (0 : ℝ)..1,
    ∑ x, ∑ y, p.weight x * p.weight y * (if t ≤ a.similarity x y then (1 : ℝ) else 0)
  rw [intervalIntegral.integral_finsetSum fun x _ => (row x).intervalIntegrable]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [intervalIntegral.integral_finsetSum fun y _ => (term x y).intervalIntegrable]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_layer (a.nonnegative x y) (a.bounded x y)]

/-! ## A concrete pattern score (`HS4.Score`, `HS4.04`–`HS4.06`) -/

section Score

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {V : Type u} [Fintype V]
variable (p : Distribution V R) (base : Tolerance V R) (task : V → V → R) (rate : R)

/-- The baseline distinction budget `b = h_μ(α₀)`. -/
def budget : R := p.distinction base

/-- `γ(P)`: the fraction of baseline distinction a coarsening removes
(`HS4.Score`); zero when the budget vanishes. -/
def removedFraction (β : Tolerance V R) : R :=
  if budget p base = 0 then 0
  else p.pairAverage (fun x y => β.similarity x y - base.similarity x y) / budget p base

/-- `ℓ(P)`: the task-weighted fraction (`HS4.Score`). -/
def taskFraction (β : Tolerance V R) : R :=
  if budget p base = 0 then 0
  else p.pairAverage (fun x y => task x y * (β.similarity x y - base.similarity x y)) /
    budget p base

/-- `J_λ(P) = γ(P) − λ ℓ(P)` (`HS4.Score`). -/
def patternScore (β : Tolerance V R) : R :=
  removedFraction p base β - rate * taskFraction p base task β

variable {p base task rate}

theorem budget_eq (positive : 0 < budget p base) (β : Tolerance V R) :
    removedFraction p base β =
        p.pairAverage (fun x y => β.similarity x y - base.similarity x y) / budget p base ∧
      taskFraction p base task β =
        p.pairAverage (fun x y => task x y * (β.similarity x y - base.similarity x y)) /
          budget p base := by
  simp [removedFraction, taskFraction, positive.ne']

/-- **Bounds** (`HS4.04`): `0 ≤ ℓ ≤ γ ≤ 1` and `−max(λ − 1, 0) ≤ J_λ ≤ 1`. -/
theorem score_bounds (positive : 0 < budget p base) (htask : ∀ x y, 0 ≤ task x y ∧ task x y ≤ 1)
    (hrate : 0 ≤ rate) {β : Tolerance V R} (coarser : base.Extends β) :
    0 ≤ taskFraction p base task β ∧ taskFraction p base task β ≤ removedFraction p base β ∧
      removedFraction p base β ≤ 1 ∧ -max (rate - 1) 0 ≤ patternScore p base task rate β ∧
      patternScore p base task rate β ≤ 1 := by
  obtain ⟨hγ, hℓ⟩ := budget_eq (task := task) positive β
  have change : ∀ x y, 0 ≤ β.similarity x y - base.similarity x y := fun x y =>
    sub_nonneg.mpr (coarser x y)
  have ℓnonneg : 0 ≤ taskFraction p base task β := by
    rw [hℓ]
    exact div_nonneg (p.pairAverage_nonnegative fun x y => mul_nonneg (htask x y).1 (change x y))
      positive.le
  have ℓle : taskFraction p base task β ≤ removedFraction p base β := by
    rw [hℓ, hγ]
    exact div_le_div_of_nonneg_right (p.pairAverage_mono fun x y =>
      mul_le_of_le_one_left (change x y) (htask x y).2) positive.le
  have γle : removedFraction p base β ≤ 1 := by
    rw [hγ, div_le_one positive, budget, Distribution.distinction]
    exact p.pairAverage_mono fun x y => by
      simp only [Tolerance.distance]; linarith [β.bounded x y]
  have γnonneg : 0 ≤ removedFraction p base β := ℓnonneg.trans ℓle
  refine ⟨ℓnonneg, ℓle, γle, ?_, ?_⟩
  · unfold patternScore
    rcases le_total rate 1 with small | large
    · rw [max_eq_right (by linarith)]
      nlinarith
    · rw [max_eq_left (by linarith)]
      nlinarith
  · unfold patternScore
    nlinarith

theorem score_baseline : patternScore p base task rate base = 0 := by
  simp [patternScore, removedFraction, taskFraction]

/-- **The marginal value of extra collapse** (`HS4.04`):
`J(Q) − J(P) = ⟨μ|(1 − λτ)(β_Q − β_P)|μ⟩ / b`. -/
theorem score_sub (positive : 0 < budget p base) (P Q : Tolerance V R) :
    patternScore p base task rate Q - patternScore p base task rate P =
      p.pairAverage (fun x y => (1 - rate * task x y) * (Q.similarity x y - P.similarity x y)) /
        budget p base := by
  obtain ⟨hQγ, hQℓ⟩ := budget_eq (task := task) positive Q
  obtain ⟨hPγ, hPℓ⟩ := budget_eq (task := task) positive P
  unfold patternScore
  rw [hQγ, hQℓ, hPγ, hPℓ]
  field_simp
  rw [← p.pairAverage_mul_left, ← p.pairAverage_mul_left, ← p.pairAverage_sub, ← p.pairAverage_sub,
    ← p.pairAverage_sub]
  congr 1
  funext x y
  ring

/-- Extra collapse only where `λτ ≤ 1` cannot lower the score; only where
`λτ ≥ 1` it cannot raise it (`HS4.04`). -/
theorem score_mono_of_cheap (positive : 0 < budget p base) {P Q : Tolerance V R}
    (coarser : P.Extends Q)
    (cheap : ∀ x y, P.similarity x y < Q.similarity x y → rate * task x y ≤ 1) :
    patternScore p base task rate P ≤ patternScore p base task rate Q := by
  have := score_sub (task := task) (rate := rate) positive P Q
  have nonneg : 0 ≤ p.pairAverage
      (fun x y => (1 - rate * task x y) * (Q.similarity x y - P.similarity x y)) :=
    p.pairAverage_nonnegative fun x y => by
      rcases (coarser x y).lt_or_eq with lt | eq
      · exact mul_nonneg (by linarith [cheap x y lt]) (by linarith)
      · rw [eq, sub_self, mul_zero]
  linarith [div_nonneg nonneg positive.le]

theorem score_anti_of_costly (positive : 0 < budget p base) {P Q : Tolerance V R}
    (coarser : P.Extends Q)
    (costly : ∀ x y, P.similarity x y < Q.similarity x y → 1 ≤ rate * task x y) :
    patternScore p base task rate Q ≤ patternScore p base task rate P := by
  have := score_sub (task := task) (rate := rate) positive P Q
  have nonpos : p.pairAverage
      (fun x y => (1 - rate * task x y) * (Q.similarity x y - P.similarity x y)) ≤ 0 := by
    have := p.pairAverage_nonnegative (f := fun x y =>
      (rate * task x y - 1) * (Q.similarity x y - P.similarity x y)) fun x y => by
      rcases (coarser x y).lt_or_eq with lt | eq
      · exact mul_nonneg (by linarith [costly x y lt]) (by linarith)
      · rw [eq, sub_self, mul_zero]
    have neg : p.pairAverage (fun x y => (1 - rate * task x y) * (Q.similarity x y - P.similarity x y)) =
        -p.pairAverage (fun x y => (rate * task x y - 1) * (Q.similarity x y - P.similarity x y)) := by
      rw [show -p.pairAverage (fun x y => (rate * task x y - 1) * (Q.similarity x y - P.similarity x y)) =
          -1 * p.pairAverage (fun x y => (rate * task x y - 1) * (Q.similarity x y - P.similarity x y))
        by ring, ← p.pairAverage_mul_left]
      congr 1
      funext x y
      ring
    linarith
  linarith [div_nonpos_of_nonpos_of_nonneg nonpos positive.le]

variable [DecidableEq V]

/-- **Closure is the least nonnegative-cost coherent repair** (`HS4.06`): for
prices `k ≥ 0` and a metric `β ≥ α`, `⟨μ|k(α♭ − α)|μ⟩ ≤ ⟨μ|k(β − α)|μ⟩`. -/
theorem closure_least_cost (a : Tolerance V R) (price : V → V → R) (hprice : ∀ x y, 0 ≤ price x y)
    {β : Tolerance V R} (metric : β.Metric) (above : a.Extends β) :
    p.pairAverage (fun x y => price x y * ((shortestTolerance a).similarity x y - a.similarity x y)) ≤
      p.pairAverage (fun x y => price x y * (β.similarity x y - a.similarity x y)) :=
  p.pairAverage_mono fun x y => mul_le_mul_of_nonneg_left
    (sub_le_sub_right ((shortestTolerance_is_least a).2.2 β above metric x y) _) (hprice x y)

/-- The score change from closing a preliminary candidate (`HS4.06`). -/
theorem score_closure_sub (positive : 0 < budget p base) (a : Tolerance V R) :
    patternScore p base task rate (shortestTolerance a) - patternScore p base task rate a =
      p.pairAverage (fun x y => (1 - rate * task x y) *
        ((shortestTolerance a).similarity x y - a.similarity x y)) / budget p base :=
  score_sub positive a (shortestTolerance a)

end Score

/-! ### The coherent feasible set is a compact polytope (`HS4.05`) -/

section Polytope

variable {V : Type u} [Fintype V]

/-- The coherent coarsenings `𝒞(α₀)` of a baseline, as raw kernels: symmetric,
unit diagonal, between the baseline and one, and metric. -/
def coherentSet (base : Tolerance V ℝ) : Set (V → V → ℝ) :=
  (⋂ x, ⋂ y, {β | β x y = β y x}) ∩ (⋂ x, {β | β x x = 1}) ∩
    (⋂ x, ⋂ y, {β | base.similarity x y ≤ β x y ∧ β x y ≤ 1}) ∩
    (⋂ x, ⋂ y, ⋂ z, {β | β x y + β y z - 1 ≤ β x z})

omit [Fintype V] in
theorem mem_coherentSet {base : Tolerance V ℝ} {β : V → V → ℝ} :
    β ∈ coherentSet base ↔ (∀ x y, β x y = β y x) ∧ (∀ x, β x x = 1) ∧
      (∀ x y, base.similarity x y ≤ β x y ∧ β x y ≤ 1) ∧ ∀ x y z, β x y + β y z - 1 ≤ β x z := by
  simp only [coherentSet, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, and_assoc]

omit [Fintype V] in
theorem coherentSet_isCompact (base : Tolerance V ℝ) : IsCompact (coherentSet base) := by
  have box : IsCompact (Set.univ.pi fun _ : V => Set.univ.pi fun _ : V => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  have cont : ∀ x y, Continuous fun β : V → V → ℝ => β x y := fun x y =>
    (continuous_apply y).comp (continuous_apply x)
  refine box.of_isClosed_subset ?_ ?_
  · refine ((IsClosed.inter ?_ ?_).inter ?_).inter ?_
    · exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq (cont x y) (cont y x)
    · exact isClosed_iInter fun x => isClosed_eq (cont x x) continuous_const
    · exact isClosed_iInter fun x => isClosed_iInter fun y =>
        (isClosed_le continuous_const (cont x y)).inter (isClosed_le (cont x y) continuous_const)
    · exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun z =>
        isClosed_le (((cont x y).add (cont y z)).sub continuous_const) (cont x z)
  · intro β hβ
    have bounds := (mem_coherentSet.mp hβ).2.2.1
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_true_left]
    exact fun x y => ⟨(base.nonnegative x y).trans (bounds x y).1, (bounds x y).2⟩

omit [Fintype V] in
theorem base_mem_coherentSet {base : Tolerance V ℝ} (metric : base.Metric) :
    base.similarity ∈ coherentSet base :=
  mem_coherentSet.mpr ⟨base.symmetric, base.reflexive, fun x y => ⟨le_rfl, base.bounded x y⟩,
    (Tolerance.metric_iff_similarity base).mp metric⟩

/-- **An attained coherent optimum** (`HS4.05`): every objective affine in the
kernel, in particular `J_λ`, attains its maximum on the coherent polytope of a
metric baseline. -/
theorem exists_max_on_coherentSet {base : Tolerance V ℝ} (metric : base.Metric)
    (c : V → V → ℝ) (c₀ : ℝ) :
    ∃ β ∈ coherentSet base, ∀ β' ∈ coherentSet base,
      c₀ + ∑ x, ∑ y, c x y * β' x y ≤ c₀ + ∑ x, ∑ y, c x y * β x y := by
  have cont : Continuous fun β : V → V → ℝ => c₀ + ∑ x, ∑ y, c x y * β x y := by
    fun_prop
  obtain ⟨β, mem, max⟩ := (coherentSet_isCompact base).exists_isMaxOn
    ⟨_, base_mem_coherentSet metric⟩ cont.continuousOn
  exact ⟨β, mem, fun β' mem' => max mem'⟩

/-- **With a task budget the optimum is still attained** (`HS4.05`): adding a
closed affine constraint keeps a nonempty compact feasible set when the
baseline satisfies it. -/
theorem exists_max_on_budgeted {base : Tolerance V ℝ} (metric : base.Metric)
    (c d : V → V → ℝ) (ε : ℝ)
    (baseline : ∑ x, ∑ y, d x y * base.similarity x y ≤ ε) :
    ∃ β ∈ coherentSet base ∩ {β | ∑ x, ∑ y, d x y * β x y ≤ ε},
      ∀ β' ∈ coherentSet base ∩ {β | ∑ x, ∑ y, d x y * β x y ≤ ε},
        ∑ x, ∑ y, c x y * β' x y ≤ ∑ x, ∑ y, c x y * β x y := by
  have closed : IsClosed {β : V → V → ℝ | ∑ x, ∑ y, d x y * β x y ≤ ε} :=
    isClosed_le (by fun_prop) continuous_const
  obtain ⟨β, mem, max⟩ := ((coherentSet_isCompact base).inter_right closed).exists_isMaxOn
    ⟨_, base_mem_coherentSet metric, baseline⟩
    (show Continuous fun β : V → V → ℝ => ∑ x, ∑ y, c x y * β x y by fun_prop).continuousOn
  exact ⟨β, mem, fun β' mem' => max mem'⟩

end Polytope

/-! ### The worked model: two useful abstractions compose badly (ch. 4, §3.4) -/

namespace PatternExample

open Examples (uniformThree uniformThree_average)

/-- A tolerance on three tokens from its off-diagonal similarities
`x = β(a, b)`, `y = β(b, c)`, `z = β(a, c)`. -/
def triple (x y z : ℚ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) (hz : 0 ≤ z ∧ z ≤ 1) :
    Tolerance (Fin 3) where
  similarity i j := 1 - EvidenceExamples.table (1 - x) (1 - y) (1 - z) i j
  nonnegative i j := by
    unfold EvidenceExamples.table
    split_ifs <;> linarith [hx.1, hx.2, hy.1, hy.2, hz.1, hz.2]
  bounded i j := by
    unfold EvidenceExamples.table
    split_ifs <;> linarith [hx.1, hx.2, hy.1, hy.2, hz.1, hz.2]
  reflexive i := by simp [EvidenceExamples.table]
  symmetric i j := by
    fin_cases i <;> fin_cases j <;> simp [EvidenceExamples.table]

/-- The identity baseline. -/
def identity : Tolerance (Fin 3) := Tolerance.ofReport id

/-- The task metric `τ(a, b) = τ(b, c) = ½`, `τ(a, c) = 1`. -/
def task : Fin 3 → Fin 3 → ℚ := EvidenceExamples.table (1 / 2) (1 / 2) 1

theorem identity_budget : budget uniformThree identity = 2 / 3 := by
  rw [budget, Distribution.distinction_eq_one_sub, Distribution.graphtropy, uniformThree_average]
  norm_num [identity, Tolerance.ofReport, Fin.ext_iff]

/-- **The score in coordinates**: `J_{9/5}(β) = (x + y − 8z)/30`. -/
theorem score_coordinates (β : Tolerance (Fin 3)) :
    patternScore uniformThree identity task (9 / 5) β =
      (β.similarity 0 1 + β.similarity 1 2 - 8 * β.similarity 0 2) / 30 := by
  obtain ⟨hγ, hℓ⟩ := budget_eq (task := task) (by rw [identity_budget]; norm_num) β
  unfold patternScore
  rw [hγ, hℓ, identity_budget, uniformThree_average, uniformThree_average, β.reflexive 0,
    β.reflexive 1, β.reflexive 2, β.symmetric 1 0, β.symmetric 2 1, β.symmetric 2 0]
  norm_num [identity, Tolerance.ofReport, task, EvidenceExamples.table, Fin.ext_iff]
  ring

/-- **The optimum is `1/30`, with a two-slack certificate** (ch. 4, §3.4 and
§6.1): for every metric coarsening of the identity,
`1/30 − J = (1 + z − x − y)/30 + 7z/30 ≥ 0`. -/
theorem score_le_of_metric (β : Tolerance (Fin 3)) (metric : β.Metric) :
    1 / 30 - patternScore uniformThree identity task (9 / 5) β =
        (1 + β.similarity 0 2 - β.similarity 0 1 - β.similarity 1 2) / 30 +
          7 * β.similarity 0 2 / 30 ∧
      patternScore uniformThree identity task (9 / 5) β ≤ 1 / 30 := by
  have triangle := (Tolerance.metric_iff_similarity β).mp metric 0 1 2
  have hz := β.nonnegative 0 2
  rw [score_coordinates]
  constructor
  · ring
  · linarith

/-- The two crisp merges, their raw join, total collapse and the graded
compromise. -/
def mergeAB : Tolerance (Fin 3) := triple 1 0 0 (by norm_num) (by norm_num) (by norm_num)
def mergeBC : Tolerance (Fin 3) := triple 0 1 0 (by norm_num) (by norm_num) (by norm_num)
def rawJoin : Tolerance (Fin 3) := triple 1 1 0 (by norm_num) (by norm_num) (by norm_num)
def collapse : Tolerance (Fin 3) := triple 1 1 1 (by norm_num) (by norm_num) (by norm_num)
def graded : Tolerance (Fin 3) := triple (1 / 2) (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num)

open EvidenceExamples (table)

theorem mergeAB_sim (i j : Fin 3) : mergeAB.similarity i j = 1 - table 0 1 1 i j := by
  simp only [mergeAB, triple]; norm_num
theorem mergeBC_sim (i j : Fin 3) : mergeBC.similarity i j = 1 - table 1 0 1 i j := by
  simp only [mergeBC, triple]; norm_num
theorem rawJoin_sim (i j : Fin 3) : rawJoin.similarity i j = 1 - table 0 0 1 i j := by
  simp only [rawJoin, triple]; norm_num
theorem collapse_sim (i j : Fin 3) : collapse.similarity i j = 1 - table 0 0 0 i j := by
  simp only [collapse, triple]; norm_num
theorem graded_sim (i j : Fin 3) : graded.similarity i j = 1 - table (1 / 2) (1 / 2) 1 i j := by
  simp only [graded, triple]; norm_num

/-- **The table of the worked model** (ch. 4, §3.4). -/
theorem worked_table :
    uniformThree.graphtropy identity = 1 / 3 ∧ uniformThree.graphtropy mergeAB = 5 / 9 ∧
      uniformThree.graphtropy mergeBC = 5 / 9 ∧ uniformThree.graphtropy rawJoin = 7 / 9 ∧
      uniformThree.graphtropy collapse = 1 ∧
      patternScore uniformThree identity task (9 / 5) mergeAB = 1 / 30 ∧
      patternScore uniformThree identity task (9 / 5) mergeBC = 1 / 30 ∧
      patternScore uniformThree identity task (9 / 5) rawJoin = 1 / 15 ∧
      patternScore uniformThree identity task (9 / 5) collapse = -1 / 5 ∧
      patternScore uniformThree identity task (9 / 5) graded = 1 / 30 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Distribution.graphtropy, uniformThree_average]
    norm_num [identity, Tolerance.ofReport, Fin.ext_iff]
  all_goals first
    | (rw [Distribution.graphtropy, uniformThree_average]
       simp only [mergeAB_sim, mergeBC_sim, rawJoin_sim, collapse_sim, table]
       norm_num [Fin.ext_iff])
    | (rw [score_coordinates]
       simp only [mergeAB_sim, mergeBC_sim, rawJoin_sim, collapse_sim, graded_sim, table]
       norm_num [Fin.ext_iff])

/-- The raw join of the two merges is their pointwise maximum, and it is not
metric: expected weakness is not the maximum of the two weaknesses. -/
theorem rawJoin_not_metric :
    (mergeAB.sup mergeBC).similarity = rawJoin.similarity ∧ ¬ rawJoin.Metric ∧
      uniformThree.graphtropy rawJoin ≠
        max (uniformThree.graphtropy mergeAB) (uniformThree.graphtropy mergeBC) := by
  refine ⟨?_, ?_, ?_⟩
  · funext i j
    simp only [Tolerance.sup, mergeAB_sim, mergeBC_sim, rawJoin_sim]
    fin_cases i <;> fin_cases j <;> norm_num [table, Fin.ext_iff]
  · intro metric
    have := (Tolerance.metric_iff_similarity rawJoin).mp metric 0 1 2
    simp only [rawJoin_sim, table] at this
    norm_num [Fin.ext_iff] at this
  · obtain ⟨-, h₁, h₂, h₃, -⟩ := worked_table
    rw [h₁, h₂, h₃]
    norm_num

/-- **Coherence forces the costly comparison**: the least metric tolerance above
the raw join is total collapse, adding `2/9` of expected indistinction and
lowering the score by `4/15`. -/
theorem join_closure :
    (shortestTolerance rawJoin).similarity = collapse.similarity ∧
      uniformThree.graphtropy collapse - uniformThree.graphtropy rawJoin = 2 / 9 ∧
      patternScore uniformThree identity task (9 / 5) collapse -
        patternScore uniformThree identity task (9 / 5) rawJoin = -4 / 15 := by
  have collapseOne : ∀ i j, collapse.similarity i j = 1 := fun i j => by
    rw [collapse_sim]
    unfold table
    split_ifs <;> norm_num
  have least : LeastMetricExtension rawJoin collapse := by
    refine ⟨fun i j => ?_, ?_, fun other above metric i j => ?_⟩
    · rw [collapseOne]
      exact rawJoin.bounded i j
    · rw [Tolerance.metric_iff_similarity]
      intro i j k
      rw [collapseOne, collapseOne, collapseOne]
      norm_num
    · have ab : other.similarity 0 1 = 1 := le_antisymm (other.bounded 0 1) (by
        have := above 0 1
        rw [rawJoin_sim] at this
        simpa [table, Fin.ext_iff] using this)
      have bc : other.similarity 1 2 = 1 := le_antisymm (other.bounded 1 2) (by
        have := above 1 2
        rw [rawJoin_sim] at this
        simpa [table, Fin.ext_iff] using this)
      have tri := (Tolerance.metric_iff_similarity other).mp metric 0 1 2
      have ac : other.similarity 0 2 = 1 := le_antisymm (other.bounded 0 2) (by linarith)
      rw [collapseOne]
      fin_cases i <;> fin_cases j <;>
        simp [other.reflexive, ab, bc, ac, other.symmetric 1 0, other.symmetric 2 1,
          other.symmetric 2 0]
  obtain ⟨-, -, -, h₄, h₅, -, -, j₄, j₅, -⟩ := worked_table
  refine ⟨leastMetricExtension_unique (shortestTolerance_is_least rawJoin) least, ?_, ?_⟩
  · rw [h₄, h₅]; norm_num
  · rw [j₄, j₅]; norm_num

/-- The graded optimum distinguishes exactly as the task does. -/
theorem graded_matches_task (i j : Fin 3) : graded.distance i j = task i j := by
  rw [Tolerance.distance, graded_sim, task]
  ring

end PatternExample

/-! ## Dissonance is a directional distinction budget (`HS4.07`–`HS4.10`) -/

/-- `|√a − √b| ≤ √|a − b|` on nonnegative reals. -/
theorem abs_sqrt_sub_sqrt_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : |√a - √b| ≤ √|a - b| := by
  apply Real.abs_le_sqrt
  have hs := Real.sq_sqrt ha
  have ht := Real.sq_sqrt hb
  have s₀ := Real.sqrt_nonneg a
  have t₀ := Real.sqrt_nonneg b
  rcases le_total √b √a with h | h
  · rw [abs_of_nonneg (by nlinarith : 0 ≤ a - b)]
    nlinarith
  · rw [abs_of_nonpos (by nlinarith : a - b ≤ 0)]
    nlinarith

section Dissonance

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type v} [Fintype ι] (y : ι → E)

open scoped RealInnerProductSpace

/-- Total magnitude `M = Σ ‖y_i‖`. -/
noncomputable def totalMagnitude : ℝ := ∑ i, ‖y i‖

/-- Resonance `R = ‖Σ y_i‖`. -/
noncomputable def resultant : ℝ := ‖∑ i, y i‖

/-- Dissonance `D = M − R`. -/
noncomputable def dissonance : ℝ := totalMagnitude y - resultant y

/-- The direction `u_i = y_i / ‖y_i‖` (zero for a zero contribution). -/
noncomputable def direction (i : ι) : E := ‖y i‖⁻¹ • y i

/-- The contribution weight `π_i = ‖y_i‖ / M`. -/
noncomputable def contributionWeight (i : ι) : ℝ := ‖y i‖ / totalMagnitude y

/-- The chord distance `δ(i, j) = ‖u_i − u_j‖ / 2`. -/
noncomputable def chord (i j : ι) : ℝ := ‖direction y i - direction y j‖ / 2

/-- The directional distinction energy `H = ⟨π|δ²|π⟩`. -/
noncomputable def directionalEnergy : ℝ :=
  ∑ i, ∑ j, contributionWeight y i * contributionWeight y j * chord y i j ^ 2

theorem weight_smul_direction (i : ι) :
    contributionWeight y i • direction y i = (totalMagnitude y)⁻¹ • y i := by
  by_cases zero : y i = 0
  · simp [zero, direction]
  · have : ‖y i‖ ≠ 0 := norm_ne_zero_iff.mpr zero
    rw [contributionWeight, direction, smul_smul, div_eq_mul_inv, mul_comm (‖y i‖),
      mul_assoc, mul_inv_cancel₀ this, mul_one]

omit [Fintype ι] in
theorem norm_direction {i : ι} (nonzero : y i ≠ 0) : ‖direction y i‖ = 1 := by
  rw [direction, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr nonzero)]

omit [InnerProductSpace ℝ E] in
theorem sum_contributionWeight (positive : 0 < totalMagnitude y) :
    ∑ i, contributionWeight y i = 1 := by
  simp only [contributionWeight]
  rw [← Finset.sum_div]
  exact div_self positive.ne'

/-- **The exact dissonance bracket** (`HS4.07`): `R²/M² = 1 − 2H`. -/
theorem resultant_ratio_sq (positive : 0 < totalMagnitude y) :
    (resultant y / totalMagnitude y) ^ 2 = 1 - 2 * directionalEnergy y := by
  have mean : ∑ i, contributionWeight y i • direction y i =
      (totalMagnitude y)⁻¹ • ∑ i, y i := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => weight_smul_direction y i
  have ratio : resultant y / totalMagnitude y = ‖∑ i, contributionWeight y i • direction y i‖ := by
    rw [mean, norm_smul, norm_inv, Real.norm_of_nonneg positive.le, resultant, inv_mul_eq_div]
  have expand : ‖∑ i, contributionWeight y i • direction y i‖ ^ 2 =
      ∑ i, ∑ j, contributionWeight y i * contributionWeight y j *
        ⟪direction y i, direction y j⟫ := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  have term : ∀ i j, contributionWeight y i * contributionWeight y j *
      ⟪direction y i, direction y j⟫ =
      contributionWeight y i * contributionWeight y j * (1 - 2 * chord y i j ^ 2) := by
    intro i j
    by_cases zi : y i = 0
    · simp [contributionWeight, zi]
    by_cases zj : y j = 0
    · simp [contributionWeight, zj]
    congr 1
    have := norm_sub_sq_real (direction y i) (direction y j)
    rw [norm_direction y zi, norm_direction y zj] at this
    unfold chord
    nlinarith
  rw [ratio, expand, Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => term i j]
  have total : ∑ i, ∑ j, contributionWeight y i * contributionWeight y j = 1 := by
    rw [← Finset.sum_mul_sum, sum_contributionWeight y positive, one_mul]
  unfold directionalEnergy
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, total]
  rw [Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

omit [InnerProductSpace ℝ E] in
theorem resultant_le (_positive : 0 < totalMagnitude y) : resultant y ≤ totalMagnitude y :=
  norm_sum_le _ _

/-- **Dissonance as a function of the energy** (`HS4.07`):
`D/M = 1 − √(1 − 2H)`, with `0 ≤ H ≤ ½` and `H ≤ D/M ≤ 2H ≤ 1`. -/
theorem dissonance_ratio (positive : 0 < totalMagnitude y) :
    dissonance y / totalMagnitude y = 1 - √(1 - 2 * directionalEnergy y) ∧
      0 ≤ directionalEnergy y ∧ directionalEnergy y ≤ 1 / 2 ∧
      directionalEnergy y ≤ dissonance y / totalMagnitude y ∧
      dissonance y / totalMagnitude y ≤ 2 * directionalEnergy y ∧
      2 * directionalEnergy y ≤ 1 := by
  have sq := resultant_ratio_sq y positive
  have r₀ : 0 ≤ resultant y / totalMagnitude y := div_nonneg (norm_nonneg _) positive.le
  have r₁ : resultant y / totalMagnitude y ≤ 1 := (div_le_one positive).mpr (resultant_le y positive)
  have root : resultant y / totalMagnitude y = √(1 - 2 * directionalEnergy y) := by
    rw [← sq, Real.sqrt_sq r₀]
  have ratio : dissonance y / totalMagnitude y = 1 - resultant y / totalMagnitude y := by
    rw [dissonance, sub_div, div_self positive.ne']
  set s := resultant y / totalMagnitude y
  refine ⟨by rw [ratio, root], ?_, ?_, ?_, ?_, ?_⟩ <;> rw [ratio] at * <;> nlinarith

/-- **Interference from the energy** (`HS4.07`):
`R² − Σ ‖y_i‖² = M² (1 − 2H − Σ π_i²)`. -/
theorem interference_eq_energy (positive : 0 < totalMagnitude y) :
    resultant y ^ 2 - ∑ i, ‖y i‖ ^ 2 =
      totalMagnitude y ^ 2 * (1 - 2 * directionalEnergy y - ∑ i, contributionWeight y i ^ 2) := by
  have sq := resultant_ratio_sq y positive
  have weights : ∑ i, ‖y i‖ ^ 2 = totalMagnitude y ^ 2 * ∑ i, contributionWeight y i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [contributionWeight, div_pow]
    field_simp
  rw [weights, ← sq, div_pow]
  field_simp

omit [Fintype ι] in
/-- Directional chords are at most one. -/
theorem chord_le_one (i j : ι) : chord y i j ≤ 1 := by
  have bound : ∀ k, ‖direction y k‖ ≤ 1 := fun k => by
    by_cases z : y k = 0
    · simp [direction, z]
    · rw [norm_direction y z]
  unfold chord
  linarith [norm_sub_le (direction y i) (direction y j), bound i, bound j]

/-- The contribution weights as a probability vector. -/
noncomputable def contributionDistribution (positive : 0 < totalMagnitude y) : Distribution ι ℝ where
  weight := contributionWeight y
  nonnegative _ := div_nonneg (norm_nonneg _) positive.le
  normalized := sum_contributionWeight y positive

/-- `h_dir² ≤ H ≤ h_dir` for the ordinary directional bracket (`HS4.07`). -/
theorem directional_bracket_bounds (positive : 0 < totalMagnitude y) :
    ((contributionDistribution y positive).pairAverage (chord y)) ^ 2 ≤ directionalEnergy y ∧
      directionalEnergy y ≤ (contributionDistribution y positive).pairAverage (chord y) := by
  have energy : directionalEnergy y =
      (contributionDistribution y positive).pairAverage fun i j => chord y i j ^ 2 := rfl
  rw [energy]
  exact ⟨Distribution.pairAverage_sq_le _ _, Distribution.pairAverage_sq_le_self _ fun i j =>
    ⟨div_nonneg (norm_nonneg _) zero_le_two, chord_le_one y i j⟩⟩

/-- **Unit vectors have energy at most ½** under any probability vector: a
distinction kernel can be a directional chord geometry only under this bound. -/
theorem chord_energy_le_half (u : ι → E) (unit : ∀ i, ‖u i‖ = 1) (p : Distribution ι ℝ) :
    p.pairAverage (fun i j => (‖u i - u j‖ / 2) ^ 2) ≤ 1 / 2 := by
  have expand : ‖∑ i, p.weight i • u i‖ ^ 2 =
      1 - 2 * p.pairAverage (fun i j => (‖u i - u j‖ / 2) ^ 2) := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    have term : ∀ i j, ⟪p.weight i • u i, p.weight j • u j⟫ =
        p.weight i * p.weight j - 2 * (p.weight i * p.weight j * (‖u i - u j‖ / 2) ^ 2) := by
      intro i j
      rw [real_inner_smul_left, real_inner_smul_right]
      have := norm_sub_sq_real (u i) (u j)
      rw [unit i, unit j] at this
      have inner : ⟪u i, u j⟫ = 1 - 2 * (‖u i - u j‖ / 2) ^ 2 := by linarith
      rw [inner]
      ring
    simp only [inner_sum, term, Finset.sum_sub_distrib, Distribution.pairAverage, Finset.mul_sum]
    rw [← Finset.sum_mul_sum, p.normalized, one_mul]
  have := sq_nonneg ‖∑ i, p.weight i • u i‖
  linarith

/-- **Not every bounded pseudometric is a directional geometry** (ch. 4, §4.2):
the discrete distance on three uniformly weighted tokens has `H = 2/3 > ½`, so
it is the chord distance of no three unit vectors. -/
theorem discrete_not_chord (u : Fin 3 → E) (unit : ∀ i, ‖u i‖ = 1) :
    ¬ ∀ i j, ‖u i - u j‖ / 2 = if i = j then 0 else 1 := by
  intro chordEq
  have bound := chord_energy_le_half u unit (Distribution.uniform (Fin 3) ℝ)
  simp only [chordEq] at bound
  rw [EvidenceExamples.uniform_three_pairAverage] at bound
  norm_num [Fin.ext_iff] at bound

/-- **A finite certificate for directional geometry** (`HS4.08`), necessity:
the matrix `1 − 2δ²` of a chord geometry of unit vectors is positive
semidefinite. -/
theorem gram_posSemidef_of_unit (u : ι → E) (unit : ∀ i, ‖u i‖ = 1) :
    (Matrix.of fun i j => 1 - 2 * (‖u i - u j‖ / 2) ^ 2 : Matrix ι ι ℝ).PosSemidef := by
  have equal : (Matrix.of fun i j => 1 - 2 * (‖u i - u j‖ / 2) ^ 2 : Matrix ι ι ℝ) =
      Matrix.gram ℝ u := by
    ext i j
    rw [Matrix.of_apply, Matrix.gram_apply]
    have := norm_sub_sq_real (u i) (u j)
    rw [unit i, unit j] at this
    nlinarith
  rw [equal]
  exact Matrix.posSemidef_gram ℝ u

/-- **Sufficiency** (`HS4.08`): if `1 − 2δ²` (with unit diagonal) is positive
semidefinite, `δ` is the chord distance of unit vectors in a real Euclidean
space. -/
theorem exists_unit_vectors_of_posSemidef (δ : ι → ι → ℝ) (nonneg : ∀ i j, 0 ≤ δ i j)
    (diag : ∀ i, δ i i = 0)
    (psd : (Matrix.of fun i j => 1 - 2 * δ i j ^ 2 : Matrix ι ι ℝ).PosSemidef) :
    ∃ (m : ℕ) (u : ι → EuclideanSpace ℝ (Fin m)), (∀ i, ‖u i‖ = 1) ∧
      ∀ i j, ‖u i - u j‖ / 2 = δ i j := by
  obtain ⟨m, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp psd
  let u : ι → EuclideanSpace ℝ (Fin m) := fun i => WithLp.toLp 2 fun k => v k i
  have inner : ∀ i j, ⟪u i, u j⟫ = 1 - 2 * δ i j ^ 2 := by
    intro i j
    have entry := congrFun (congrFun hv i) j
    simp only [Matrix.of_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, star_trivial] at entry
    rw [entry]
    simp only [u, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [mul_comm]
  refine ⟨m, u, fun i => ?_, fun i j => ?_⟩
  · have := inner i i
    rw [diag, real_inner_self_eq_norm_sq] at this
    have : ‖u i‖ ^ 2 = 1 := by linarith
    nlinarith [norm_nonneg (u i)]
  · have unit : ∀ k, ‖u k‖ = 1 := fun k => by
      have := inner k k
      rw [diag, real_inner_self_eq_norm_sq] at this
      nlinarith [norm_nonneg (u k)]
    have := norm_sub_sq_real (u i) (u j)
    rw [unit i, unit j, inner] at this
    have sq : (‖u i - u j‖ / 2) ^ 2 = δ i j ^ 2 := by nlinarith
    exact (sq_eq_sq₀ (div_nonneg (norm_nonneg _) zero_le_two) (nonneg i j)).mp sq

/-- **The dimension bound** (`HS4.08`, necessity of the rank condition): a chord
geometry of unit vectors in `ℝᵏ` has `rank (1 − 2δ²) ≤ k`; unit complex scalars,
the case `k = 2`, force rank at most two. -/
theorem rank_le_of_unit_vectors {k : ℕ} (u : ι → EuclideanSpace ℝ (Fin k))
    (unit : ∀ i, ‖u i‖ = 1) :
    (Matrix.of fun i j => 1 - 2 * (‖u i - u j‖ / 2) ^ 2 : Matrix ι ι ℝ).rank ≤ k := by
  let B : Matrix (Fin k) ι ℝ := Matrix.of fun a i => u i a
  have gram : (Matrix.of fun i j => 1 - 2 * (‖u i - u j‖ / 2) ^ 2 : Matrix ι ι ℝ) = B.transpose * B := by
    ext i j
    rw [Matrix.of_apply, Matrix.mul_apply]
    have norms := norm_sub_sq_real (u i) (u j)
    rw [unit i, unit j] at norms
    have inner : ⟪u i, u j⟫ = ∑ a, u i a * u j a := by
      simp [PiLp.inner_apply, mul_comm]
    simp only [B, Matrix.transpose_apply, Matrix.of_apply]
    rw [← inner]
    nlinarith
  rw [gram, Matrix.rank_transpose_mul_self]
  exact (Matrix.rank_le_card_height B).trans (by simp)

/-- **Isometries preserve every resonance quantity** (`HS4.09`). -/
theorem isometry_invariance (U : E →ₗᵢ[ℝ] E) :
    totalMagnitude (fun i => U (y i)) = totalMagnitude y ∧
      resultant (fun i => U (y i)) = resultant y ∧
      dissonance (fun i => U (y i)) = dissonance y ∧
      directionalEnergy (fun i => U (y i)) = directionalEnergy y := by
  have M : totalMagnitude (fun i => U (y i)) = totalMagnitude y := by
    simp [totalMagnitude]
  have Rr : resultant (fun i => U (y i)) = resultant y := by
    simp [resultant, ← map_sum]
  refine ⟨M, Rr, by rw [dissonance, dissonance, M, Rr], ?_⟩
  unfold directionalEnergy contributionWeight chord direction
  simp only [LinearIsometry.norm_map, M, ← LinearIsometry.map_smul, ← map_sub]

/-- **Zero dissonance is a common ray** (`HS4.09`): for `M > 0`, `D = 0` iff
`H = 0` iff all nonzero contributions share one direction. -/
theorem dissonance_eq_zero_iff (positive : 0 < totalMagnitude y) :
    (dissonance y = 0 ↔ directionalEnergy y = 0) ∧
      (directionalEnergy y = 0 ↔ ∀ i j, y i ≠ 0 → y j ≠ 0 → direction y i = direction y j) := by
  obtain ⟨ratio, nonneg, -, lower, upper, -⟩ := dissonance_ratio y positive
  constructor
  · constructor
    · intro zero
      rw [zero, zero_div] at lower
      linarith
    · intro zero
      rw [zero, mul_zero] at upper
      have : dissonance y / totalMagnitude y = 0 := le_antisymm upper (by
        rw [← zero_div (totalMagnitude y)]
        exact div_le_div_of_nonneg_right (by
          rw [dissonance, sub_nonneg]; exact resultant_le y positive) positive.le)
      rwa [div_eq_zero_iff, or_iff_left positive.ne'] at this
  · constructor
    · intro zero i j zi zj
      have terms := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (mul_nonneg (div_nonneg (norm_nonneg (y i)) positive.le)
          (div_nonneg (norm_nonneg (y j)) positive.le)) (sq_nonneg (chord y i j))).mp zero i
          (Finset.mem_univ i)
      have term := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
        mul_nonneg (mul_nonneg (div_nonneg (norm_nonneg (y i)) positive.le)
          (div_nonneg (norm_nonneg (y j)) positive.le)) (sq_nonneg (chord y i j))).mp terms j
          (Finset.mem_univ j)
      have wi : contributionWeight y i ≠ 0 :=
        div_ne_zero (norm_ne_zero_iff.mpr zi) positive.ne'
      have wj : contributionWeight y j ≠ 0 :=
        div_ne_zero (norm_ne_zero_iff.mpr zj) positive.ne'
      have : chord y i j = 0 := by
        rcases mul_eq_zero.mp term with h | h
        · exact absurd h (mul_ne_zero wi wj)
        · exact pow_eq_zero_iff two_ne_zero |>.mp h
      rw [chord, div_eq_zero_iff, or_iff_left two_ne_zero, norm_eq_zero, sub_eq_zero] at this
      exact this
    · intro common
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      by_cases zi : y i = 0
      · simp [contributionWeight, zi]
      by_cases zj : y j = 0
      · simp [contributionWeight, zj]
      simp [chord, common i j zi zj]

/-- **At fixed magnitudes, less directional distinction means more resonance**
(`HS4.09`). -/
theorem resultant_anti_energy (y' : ι → E) (same : ∀ i, ‖y' i‖ = ‖y i‖)
    (positive : 0 < totalMagnitude y) (less : directionalEnergy y' ≤ directionalEnergy y) :
    resultant y ≤ resultant y' ∧ dissonance y' ≤ dissonance y := by
  have M : totalMagnitude y' = totalMagnitude y := by simp [totalMagnitude, same]
  have positive' : 0 < totalMagnitude y' := M ▸ positive
  have sq := resultant_ratio_sq y positive
  have sq' := resultant_ratio_sq y' positive'
  rw [M] at sq'
  have r₀ : 0 ≤ resultant y / totalMagnitude y := div_nonneg (norm_nonneg _) positive.le
  have r₀' : 0 ≤ resultant y' / totalMagnitude y := div_nonneg (norm_nonneg _) positive.le
  have ratio : resultant y / totalMagnitude y ≤ resultant y' / totalMagnitude y := by
    nlinarith
  have := (div_le_div_iff_of_pos_right positive).mp ratio
  exact ⟨this, by rw [dissonance, dissonance, M]; linarith⟩

omit [InnerProductSpace ℝ E] in
/-- **Stability of resonance and dissonance** (`HS4.10`). -/
theorem resonance_stability (y' : ι → E) :
    |resultant y - resultant y'| ≤ ∑ i, ‖y i - y' i‖ ∧
      |totalMagnitude y - totalMagnitude y'| ≤ ∑ i, ‖y i - y' i‖ ∧
      |dissonance y - dissonance y'| ≤ 2 * ∑ i, ‖y i - y' i‖ := by
  have hR : |resultant y - resultant y'| ≤ ∑ i, ‖y i - y' i‖ := by
    unfold resultant
    refine (abs_norm_sub_norm_le _ _).trans ?_
    rw [← Finset.sum_sub_distrib]
    exact norm_sum_le _ _
  have hM : |totalMagnitude y - totalMagnitude y'| ≤ ∑ i, ‖y i - y' i‖ := by
    unfold totalMagnitude
    rw [← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ => abs_norm_sub_norm_le _ _)
  refine ⟨hR, hM, ?_⟩
  unfold dissonance
  rw [abs_le] at hR hM ⊢
  constructor <;> linarith [hR.1, hR.2, hM.1, hM.2]

omit [InnerProductSpace ℝ E] in
/-- The normalized dissonance moves by at most `2E/M₀` (`HS4.10`). -/
theorem normalized_dissonance_stability (y' : ι → E) {M₀ : ℝ} (hM₀ : 0 < M₀)
    (big : M₀ ≤ totalMagnitude y) (big' : M₀ ≤ totalMagnitude y') :
    |dissonance y / totalMagnitude y - dissonance y' / totalMagnitude y'| ≤
      2 * (∑ i, ‖y i - y' i‖) / M₀ := by
  obtain ⟨hR, hM, -⟩ := resonance_stability y y'
  set E₀ := ∑ i, ‖y i - y' i‖
  have pos : 0 < totalMagnitude y := hM₀.trans_le big
  have pos' : 0 < totalMagnitude y' := hM₀.trans_le big'
  have r' : resultant y' ≤ totalMagnitude y' := resultant_le y' pos'
  have r'0 : 0 ≤ resultant y' := norm_nonneg _
  have key : |resultant y / totalMagnitude y - resultant y' / totalMagnitude y'| ≤ 2 * E₀ / M₀ := by
    have split : resultant y / totalMagnitude y - resultant y' / totalMagnitude y' =
        (resultant y - resultant y') / totalMagnitude y +
          (resultant y' / totalMagnitude y') * (totalMagnitude y' - totalMagnitude y) /
            totalMagnitude y := by
      field_simp
      ring
    rw [split]
    refine (abs_add_le _ _).trans ?_
    have t₁ : |(resultant y - resultant y') / totalMagnitude y| ≤ E₀ / M₀ := by
      rw [abs_div, abs_of_pos pos]
      exact div_le_div₀ (by positivity) hR hM₀ big
    have t₂ : |(resultant y' / totalMagnitude y') * (totalMagnitude y' - totalMagnitude y) /
        totalMagnitude y| ≤ E₀ / M₀ := by
      rw [abs_div, abs_mul, abs_of_pos pos, abs_of_nonneg (div_nonneg r'0 pos'.le), abs_sub_comm]
      have q : resultant y' / totalMagnitude y' ≤ 1 := (div_le_one pos').mpr r'
      refine div_le_div₀ (by positivity) ?_ hM₀ big
      calc resultant y' / totalMagnitude y' * |totalMagnitude y - totalMagnitude y'|
          ≤ 1 * |totalMagnitude y - totalMagnitude y'| :=
            mul_le_mul_of_nonneg_right q (abs_nonneg _)
        _ ≤ E₀ := by rw [one_mul]; exact hM
    have : 2 * E₀ / M₀ = E₀ / M₀ + E₀ / M₀ := by ring
    linarith
  have dy : dissonance y / totalMagnitude y = 1 - resultant y / totalMagnitude y := by
    rw [dissonance, sub_div, div_self pos.ne']
  have dy' : dissonance y' / totalMagnitude y' = 1 - resultant y' / totalMagnitude y' := by
    rw [dissonance, sub_div, div_self pos'.ne']
  rw [dy, dy', show 1 - resultant y / totalMagnitude y - (1 - resultant y' / totalMagnitude y') =
    -(resultant y / totalMagnitude y - resultant y' / totalMagnitude y') by ring, abs_neg]
  exact key

/-- In the energy coordinate the dissonance moves by at most `√(2|H − H'|)`, and
by `|H − H'|/r₀` away from cancellation (`HS4.10`). -/
theorem energy_stability (y' : ι → E) (pos : 0 < totalMagnitude y) (pos' : 0 < totalMagnitude y') :
    |dissonance y / totalMagnitude y - dissonance y' / totalMagnitude y'| ≤
        √(2 * |directionalEnergy y - directionalEnergy y'|) ∧
      ∀ r₀ > 0, r₀ ≤ resultant y / totalMagnitude y → r₀ ≤ resultant y' / totalMagnitude y' →
        |dissonance y / totalMagnitude y - dissonance y' / totalMagnitude y'| ≤
          |directionalEnergy y - directionalEnergy y'| / r₀ := by
  obtain ⟨d, h0, h1, -, -, -⟩ := dissonance_ratio y pos
  obtain ⟨d', h0', h1', -, -, -⟩ := dissonance_ratio y' pos'
  have sq := resultant_ratio_sq y pos
  have sq' := resultant_ratio_sq y' pos'
  have a₀ : 0 ≤ 1 - 2 * directionalEnergy y := by linarith
  have b₀ : 0 ≤ 1 - 2 * directionalEnergy y' := by linarith
  rw [d, d', show 1 - √(1 - 2 * directionalEnergy y) - (1 - √(1 - 2 * directionalEnergy y')) =
    -(√(1 - 2 * directionalEnergy y) - √(1 - 2 * directionalEnergy y')) by ring, abs_neg]
  constructor
  · have := abs_sqrt_sub_sqrt_le a₀ b₀
    calc |√(1 - 2 * directionalEnergy y) - √(1 - 2 * directionalEnergy y')|
        ≤ √|1 - 2 * directionalEnergy y - (1 - 2 * directionalEnergy y')| := this
      _ = √(2 * |directionalEnergy y - directionalEnergy y'|) := by
        congr 1
        rw [show 1 - 2 * directionalEnergy y - (1 - 2 * directionalEnergy y') =
          -2 * (directionalEnergy y - directionalEnergy y') by ring, abs_mul]
        norm_num
  · intro r₀ hr₀ big big'
    have root : resultant y / totalMagnitude y = √(1 - 2 * directionalEnergy y) := by
      rw [← sq, Real.sqrt_sq (show 0 ≤ resultant y / totalMagnitude y from
        div_nonneg (norm_nonneg _) pos.le)]
    have root' : resultant y' / totalMagnitude y' = √(1 - 2 * directionalEnergy y') := by
      rw [← sq', Real.sqrt_sq (show 0 ≤ resultant y' / totalMagnitude y' from
        div_nonneg (norm_nonneg _) pos'.le)]
    rw [root] at big
    rw [root'] at big'
    set s := √(1 - 2 * directionalEnergy y)
    set t := √(1 - 2 * directionalEnergy y')
    have hs : s ^ 2 = 1 - 2 * directionalEnergy y := Real.sq_sqrt a₀
    have ht : t ^ 2 = 1 - 2 * directionalEnergy y' := Real.sq_sqrt b₀
    have prod : |s - t| * (s + t) = 2 * |directionalEnergy y - directionalEnergy y'| := by
      rw [← abs_of_pos (show 0 < s + t by linarith), ← abs_mul,
        show (s - t) * (s + t) = s ^ 2 - t ^ 2 by ring, hs, ht,
        show 1 - 2 * directionalEnergy y - (1 - 2 * directionalEnergy y') =
          2 * (directionalEnergy y' - directionalEnergy y) by ring, abs_mul, abs_sub_comm]
      norm_num
    rw [le_div_iff₀ hr₀]
    nlinarith [abs_nonneg (s - t)]

end Dissonance

/-- The real contributions `(1, −1, 2)`. -/
def contributionsBefore : Fin 3 → ℝ
  | 0 => 1
  | 1 => -1
  | 2 => 2

/-- The same contributions with the first flipped: `(−1, −1, 2)`. -/
def contributionsAfter : Fin 3 → ℝ
  | 0 => -1
  | 1 => -1
  | 2 => 2

/-- **Improving one pair can worsen the aggregate** (ch. 4, §4.3): `(1, −1, 2)`
has `R = 2`, `D = 2`, `H = 3/8`; flipping the first contribution makes the first
pair agree, yet `R = 0`, `D = 4`, `H = 1/2`. -/
theorem one_pair_worsens :
    resultant contributionsBefore = 2 ∧ dissonance contributionsBefore = 2 ∧
      directionalEnergy contributionsBefore = 3 / 8 ∧
      resultant contributionsAfter = 0 ∧ dissonance contributionsAfter = 4 ∧
      directionalEnergy contributionsAfter = 1 / 2 := by
  have M₁ : totalMagnitude contributionsBefore = 4 := by
    norm_num [totalMagnitude, Fin.sum_univ_succ, contributionsBefore]
  have M₂ : totalMagnitude contributionsAfter = 4 := by
    norm_num [totalMagnitude, Fin.sum_univ_succ, contributionsAfter]
  have R₁ : resultant contributionsBefore = 2 := by
    norm_num [resultant, Fin.sum_univ_succ, contributionsBefore]
  have R₂ : resultant contributionsAfter = 0 := by
    norm_num [resultant, Fin.sum_univ_succ, contributionsAfter]
  refine ⟨R₁, by rw [dissonance, M₁, R₁]; norm_num, ?_, R₂, by rw [dissonance, M₂, R₂]; norm_num,
    ?_⟩
  · simp only [directionalEnergy, contributionWeight, chord, direction, M₁, Fin.sum_univ_succ]
    norm_num [contributionsBefore]
  · simp only [directionalEnergy, contributionWeight, chord, direction, M₂, Fin.sum_univ_succ]
    norm_num [contributionsAfter]

/-! ### Geometric invariance is not p-bit semantics (ch. 4, §4.4) -/

/-- A unit vector inside the diamond is one of its vertices. -/
theorem unit_in_diamond {b c : ℝ} (unit : b ^ 2 + c ^ 2 = 1) (diamond : |b| + |c| ≤ 1) :
    b = 0 ∨ c = 0 := by
  have : |b| * |c| = 0 := by
    nlinarith [abs_nonneg b, abs_nonneg c, sq_abs b, sq_abs c]
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl (abs_eq_zero.mp h)
  · exact Or.inr (abs_eq_zero.mp h)

/-- **Only quarter turns keep the p-bit diamond**: a rotation by `θ` that keeps
the image of `T` inside the diamond has `cos θ = 0` or `sin θ = 0`. -/
theorem rotation_keeps_diamond (θ : ℝ)
    (keeps : ∃ v : PBit ℝ, v.embed = (Real.cos θ, Real.sin θ)) :
    Real.cos θ = 0 ∨ Real.sin θ = 0 := by
  obtain ⟨v, hv⟩ := keeps
  have diamond := v.embed_mem_diamond
  rw [hv] at diamond
  exact unit_in_diamond (Real.cos_sq_add_sin_sq θ) diamond

/-- **A π/4 turn leaves the p-bit domain**: `(1/√2, 1/√2)` decodes to support
`(1 + √2)/2 > 1`, so it is the image of no p-bit. -/
theorem eighth_turn_leaves :
    ¬ ∃ v : PBit ℝ, v.embed = (1 / √2, 1 / √2) := by
  rintro ⟨v, hv⟩
  have diamond := v.embed_mem_diamond
  rw [hv] at diamond
  have s : (1 : ℝ) < √2 := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have pos : 0 < √2 := by positivity
  have : |1 / √2| + |1 / √2| = 2 / √2 := by
    rw [abs_of_pos (by positivity)]; ring
  rw [this, div_le_one pos] at diamond
  have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  nlinarith

/-- **A quarter turn changes evidence roles**: it acts as `(p, n) ↦ (1 − n, p)`,
sending `T` to `B`. -/
theorem quarter_turn {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (v : PBit R) :
    (-v.embed.2, v.embed.1) =
      (PBit.mk (1 - v.opposition) v.support (sub_nonneg.mpr v.opposition_le_one)
        (sub_le_self _ v.opposition_nonneg) v.support_nonneg v.support_le_one).embed ∧
      (PBit.mk (1 - (PBit.supported : PBit R).opposition) (PBit.supported : PBit R).support
        (by norm_num [PBit.supported]) (by norm_num [PBit.supported]) (by norm_num [PBit.supported])
        (by norm_num [PBit.supported])) = PBit.both := by
  constructor
  · simp only [PBit.embed, Prod.mk.injEq]
    constructor <;> ring
  · ext <;> simp [PBit.supported, PBit.both]

/-! ## Which changes of representation preserve which calculations (`HS4.11`, `HS4.12`) -/

section ChangeOfBase

open Mettapedia.Algebra.QuantaleWeakness (QuantaleHom)

variable {V W : Type*} [Monoid V] [CompleteLattice V] [Monoid W] [CompleteLattice W]

/-- A strict quantale homomorphism: a quantale morphism (arbitrary joins and the
tensor) that also preserves the unit. Peak weakness already moves along any
quantale morphism (`QuantaleHom.map_weakness`); the unit is what the path star
needs. -/
structure StrictQuantaleHom (V W : Type*) [Monoid V] [CompleteLattice V] [Monoid W]
    [CompleteLattice W] extends QuantaleHom V W where
  map_one_eq : toFun 1 = 1

namespace StrictQuantaleHom

variable (φ : StrictQuantaleHom V W)

theorem map_iSup {κ : Sort*} (f : κ → V) : φ.toFun (⨆ k, f k) = ⨆ k, φ.toFun (f k) := by
  rw [iSup, φ.map_sSup', ← Set.range_comp, iSup]
  rfl

theorem map_bot : φ.toFun ⊥ = ⊥ := by
  rw [← sSup_empty, φ.map_sSup', Set.image_empty, sSup_empty]

end StrictQuantaleHom

variable {X : Type*}

/-- Max-tensor matrix composition, target first: `(A ∘ B)_{xz} = ⋁_y A_{xy} ⊗ B_{yz}`. -/
def matComp (A B : X → X → V) : X → X → V := fun x z => ⨆ y, A x y * B y z

/-- The unit matrix. -/
def matOne [DecidableEq X] : X → X → V := fun x z => if x = z then 1 else ⊥

/-- Matrix powers. -/
def matPow [DecidableEq X] (A : X → X → V) : ℕ → X → X → V
  | 0 => matOne
  | n + 1 => matComp (matPow A n) A

/-- The path star `A* = ⋁_n Aⁿ`. -/
def matStar [DecidableEq X] (A : X → X → V) : X → X → V := fun x z => ⨆ n, matPow A n x z

/-- **Change of base for composition** (`HS4.11`). -/
theorem map_matComp (φ : StrictQuantaleHom V W) (A B : X → X → V) (x z : X) :
    φ.toFun (matComp A B x z) =
      matComp (fun x y => φ.toFun (A x y)) (fun x y => φ.toFun (B x y)) x z := by
  unfold matComp
  rw [φ.map_iSup]
  simp only [φ.map_mul']

/-- **Change of base for the path star** (`HS4.11`). -/
theorem map_matStar [DecidableEq X] (φ : StrictQuantaleHom V W) (A : X → X → V) (x z : X) :
    φ.toFun (matStar A x z) = matStar (fun x y => φ.toFun (A x y)) x z := by
  have pow : ∀ n x z, φ.toFun (matPow A n x z) = matPow (fun x y => φ.toFun (A x y)) n x z := by
    intro n
    induction n with
    | zero =>
        intro x z
        simp only [matPow, matOne]
        split_ifs
        · exact φ.map_one_eq
        · exact φ.map_bot
    | succ n ih =>
        intro x z
        simp only [matPow]
        rw [map_matComp]
        congr 1
        funext x y
        exact ih x y
  unfold matStar
  rw [φ.map_iSup]
  simp only [pow]

end ChangeOfBase

/-- **A quantale map need not preserve expectation** (ch. 4, §5.2): squaring keeps
maxima, products, `0` and `1` on `[0, 1]`, yet `φ(g_μ(I)) = ¼` while
`g_μ(φ ∘ I) = ½` for the identity observer on two uniformly sampled tokens. -/
theorem square_breaks_expectation :
    (∀ s t : ℚ, 0 ≤ s → 0 ≤ t → max s t ^ 2 = max (s ^ 2) (t ^ 2)) ∧
      (∀ s t : ℚ, (s * t) ^ 2 = s ^ 2 * t ^ 2) ∧ (0 : ℚ) ^ 2 = 0 ∧ (1 : ℚ) ^ 2 = 1 ∧
      ((Distribution.uniform Bool ℚ).graphtropy (Tolerance.ofReport id)) ^ 2 = 1 / 4 ∧
      (Distribution.uniform Bool ℚ).graphtropy (Tolerance.ofReport id) = 1 / 2 := by
  have g := attention_moves_graphtropy.1
  refine ⟨fun s t hs ht => ?_, fun s t => by ring, by norm_num, by norm_num, by rw [g]; norm_num, g⟩
  rcases le_total s t with h | h
  · rw [max_eq_right h, max_eq_right (pow_le_pow_left₀ hs h 2)]
  · rw [max_eq_left h, max_eq_left (pow_le_pow_left₀ ht h 2)]

/-- **The tensor matters** (ch. 4, §5.3): the metric tolerance with
`α(a, b) = α(b, c) = ½`, `α(a, c) = 0` satisfies the Łukasiewicz triangle; after
the square root, which also keeps the max-product structure, it fails. -/
theorem sqrt_breaks_metric :
    (1 / 2 : ℝ) + 1 / 2 - 1 ≤ 0 ∧ ¬ (√(1 / 2 : ℝ) + √(1 / 2) - 1 ≤ √0) := by
  refine ⟨by norm_num, fun h => ?_⟩
  have sq : √(1 / 2 : ℝ) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have pos : 0 ≤ √(1 / 2 : ℝ) := Real.sqrt_nonneg _
  rw [Real.sqrt_zero] at h
  nlinarith

/-- **All finite expectations force an affine map** (`HS4.12`): a scalar map
commutes with every finite convex combination of points of `[0, 1]` iff it is
affine there. -/
theorem commutes_with_expectations_iff_affine {R : Type} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] (f : R → R) :
    (∀ (n : ℕ) (p x : Fin n → R), (∀ i, 0 ≤ p i) → ∑ i, p i = 1 → (∀ i, 0 ≤ x i ∧ x i ≤ 1) →
        f (∑ i, p i * x i) = ∑ i, p i * f (x i)) ↔
      ∀ t, 0 ≤ t → t ≤ 1 → f t = (1 - t) * f 0 + t * f 1 := by
  constructor
  · intro commutes t h₀ h₁
    have := commutes 2 ![1 - t, t] ![0, 1] (fun i => by fin_cases i <;> simp [h₀, h₁])
      (by simp [Fin.sum_univ_succ]) (fun i => by fin_cases i <;> simp)
    simpa [Fin.sum_univ_succ] using this
  · intro affine n p x hp hsum hx
    have mean₀ : 0 ≤ ∑ i, p i * x i := Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (hx i).1
    have mean₁ : ∑ i, p i * x i ≤ 1 :=
      (Finset.sum_le_sum fun i _ => mul_le_of_le_one_right (hp i) (hx i).2).trans hsum.le
    rw [affine _ mean₀ mean₁]
    have rhs : ∑ i, p i * f (x i) = ∑ i, (p i * f 0 + p i * x i * (f 1 - f 0)) :=
      Finset.sum_congr rfl fun i _ => by rw [affine (x i) (hx i).1 (hx i).2]; ring
    rw [rhs, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hsum]
    ring

end Mettapedia.Cybernetics.DistinctionCalculus
