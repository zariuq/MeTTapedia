/-
LLM primer:
- `ProbSimplex k = ↥(stdSimplex ℝ (Fin k))` — subtype of `Fin k → ℝ`
- `catWeight θ xs = ENNReal.ofReal (categoricalProductPMF θ xs)`
- `catPMF θ n` is a `PMF (Fin n → Fin k)` via `PMF.ofFintype` + `sum_catWeight_eq_one`
- `catKernel k n` is the Markov kernel `ProbSimplex k → Measure (Fin n → Fin k)`
- Measurability of the kernel uses polynomial structure of categoricalProductPMF
- The flatten bridge identifies `flatten(pd M n) {xs} = ENNReal.ofReal (M.prob xs)`
-/
import Mettapedia.Logic.CategoricalMixture
import Mettapedia.ProbabilityTheory.HigherOrderProbability.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Categorical de Finetti as Kyburg Flattening

This file packages categorical mixtures from `CategoricalMixture.lean` as instances of
Kyburg's higher-order probability structure (`ParametrizedDistribution`).

This generalizes `DeFinettiConnection.lean` from binary (Bool/Bernoulli) to k-ary
(Fin k / Categorical) observations.

## Main Definitions

* `CategoricalConnection.catWeight` : ENNReal weight of a word under parameter θ
* `CategoricalConnection.catPMF` : PMF on `Fin n → Fin k` from a simplex point
* `CategoricalConnection.catKernel` : Markov kernel ProbSimplex k → Measure (Fin n → Fin k)
* `CategoricalConnection.pd` : Kyburg parametrized distribution for a categorical mixture

## Main Theorems

* `CategoricalConnection.sum_catWeight_eq_one` : Weight function is a valid PMF
* `CategoricalConnection.catKernel_isMarkov` : The kernel is Markov
* `CategoricalConnection.flatten_apply_singleton` : The Kyburg flattening bridge

## References

* `DeFinettiConnection.lean` (the binary case)
* `CategoricalMixture.lean` (the categorical mixture structure)
* `Basic.lean` (Kyburg's ParametrizedDistribution)
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.ProbabilityTheory.HigherOrderProbability

open MeasureTheory ProbabilityTheory Finset BigOperators ENNReal
open Mettapedia.Logic.CategoricalDeFinetti

namespace CategoricalConnection

/-! ## ENNReal weight and PMF -/

/-- The `ENNReal` weight of a word `xs` under a simplex parameter `θ`. -/
def catWeight {k n : ℕ} (θ : ProbSimplex k) (xs : Fin n → Fin k) : ENNReal :=
  ENNReal.ofReal (categoricalProductPMF (↑θ : Fin k → ℝ) xs)

/-- The categorical weight function sums to `1` over all words of length `n`.

    This is the key normalization lemma enabling the PMF construction.
    The proof proceeds by induction on `n`, decomposing `Fin (n+1) → Fin k`
    via `Fin.consEquiv` and using `∑ₐ θ(a) = 1` at each step. -/
theorem sum_catWeight_eq_one {k n : ℕ} (θ : ProbSimplex k) :
    ∑ xs : Fin n → Fin k, catWeight θ xs = 1 := by
  classical
  unfold catWeight
  induction n with
  | zero => simp [categoricalProductPMF]
  | succ n ih =>
    -- Decompose via Fin.consEquiv: (Fin (n+1) → Fin k) ≃ Fin k × (Fin n → Fin k)
    have hdecomp :
        ∑ xs : Fin (n + 1) → Fin k, ENNReal.ofReal (categoricalProductPMF (↑θ) xs) =
          ∑ p : Fin k × (Fin n → Fin k),
            ENNReal.ofReal (categoricalProductPMF (↑θ) (Fin.cons p.1 p.2)) := by
      simpa using
        (Fintype.sum_equiv (Fin.consEquiv (n := n) (α := fun _ : Fin (n + 1) => Fin k))
          (fun p => ENNReal.ofReal (categoricalProductPMF (↑θ) (Fin.cons p.1 p.2)))
          (fun xs => ENNReal.ofReal (categoricalProductPMF (↑θ) xs))
          (fun _p => rfl)).symm
    rw [hdecomp, Fintype.sum_prod_type]
    -- Factor head * tail in each term
    have hcons (a : Fin k) (xs : Fin n → Fin k) :
        ENNReal.ofReal (categoricalProductPMF (↑θ) (Fin.cons a xs)) =
          ENNReal.ofReal ((↑θ : Fin k → ℝ) a) *
            ENNReal.ofReal (categoricalProductPMF (↑θ) xs) := by
      have hhead : 0 ≤ (↑θ : Fin k → ℝ) a := probSimplex_nonneg θ a
      rw [show categoricalProductPMF (↑θ) (Fin.cons a xs) =
          (↑θ : Fin k → ℝ) a * categoricalProductPMF (↑θ) xs from by
        unfold categoricalProductPMF; rw [Fin.prod_univ_succ]; simp]
      exact ENNReal.ofReal_mul hhead
    simp_rw [hcons, ← Finset.mul_sum]
    -- Use IH: ∑ xs, ofReal(prod θ xs) = 1
    rw [show ∑ xs : Fin n → Fin k,
        ENNReal.ofReal (categoricalProductPMF (↑θ) xs) = 1 from ih]
    simp [mul_one]
    -- ∑ₐ ofReal(θ a) = ofReal(∑ₐ θ a) = ofReal(1) = 1
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => probSimplex_nonneg θ a)]
    simp

/-- The `PMF` on `Fin n → Fin k` induced by a simplex point `θ`. -/
def catPMF {k : ℕ} (θ : ProbSimplex k) (n : ℕ) : PMF (Fin n → Fin k) :=
  PMF.ofFintype (catWeight θ) (sum_catWeight_eq_one θ)

@[simp] lemma catPMF_apply {k : ℕ} (θ : ProbSimplex k) (n : ℕ) (xs : Fin n → Fin k) :
    catPMF θ n xs = catWeight θ xs := by
  simp [catPMF]

@[simp] lemma catPMF_toMeasure_apply_singleton {k : ℕ} (θ : ProbSimplex k) (n : ℕ)
    (xs : Fin n → Fin k) :
    (catPMF θ n).toMeasure {xs} = catWeight θ xs := by
  simp [catPMF]

/-! ## Markov kernel -/

/-- The categorical product kernel: for each simplex point θ, produces the
    product measure on `Fin n → Fin k` with step distribution θ.

    This generalizes `DeFinettiConnection.kernel` from Bool to Fin k. -/
def catKernel (k n : ℕ) : _root_.ProbabilityTheory.Kernel (ProbSimplex k) (Fin n → Fin k) :=
  { toFun := fun θ => (catPMF θ n).toMeasure
    measurable' := by
      refine Measure.measurable_of_measurable_coe _ ?_
      intro s _hs
      classical
      -- Rewrite as finite sum of indicators
      have hrewrite :
          (fun θ : ProbSimplex k => (catPMF θ n).toMeasure s) =
            fun θ => ∑ x : Fin n → Fin k,
              (if x ∈ s then catWeight θ x else 0) := by
        funext θ
        simp [PMF.toMeasure_apply_fintype, catPMF, catWeight, Set.indicator]
      rw [hrewrite]
      refine Finset.measurable_fun_sum _ (fun x _ => ?_)
      by_cases hx : x ∈ s
      · simp only [hx, ↓reduceIte]
        -- catWeight is measurable: polynomial in θ-coordinates
        unfold catWeight categoricalProductPMF
        refine ENNReal.measurable_ofReal.comp ?_
        refine Finset.measurable_prod _ (fun i _ => ?_)
        exact (measurable_pi_apply (x i)).comp measurable_subtype_coe
      · simp [hx] }

instance catKernel_isMarkov (k n : ℕ) : _root_.ProbabilityTheory.IsMarkovKernel (catKernel k n) := by
  refine ⟨fun θ => ?_⟩
  show IsProbabilityMeasure ((catPMF θ n).toMeasure)
  infer_instance

/-! ## Kyburg parametrized distribution -/

/-- Pull a mixing measure supported on the simplex back to the `ProbSimplex k` subtype. -/
def mixingMeasureSimplex {k : ℕ} (M : CategoricalMixture k) : Measure (ProbSimplex k) :=
  M.mixingMeasure.comap (fun θ : ProbSimplex k => (θ : Fin k → ℝ))

instance mixingMeasureSimplex_isProbability {k : ℕ} (M : CategoricalMixture k) :
    IsProbabilityMeasure (mixingMeasureSimplex M) := by
  classical
  haveI : IsProbabilityMeasure M.mixingMeasure := M.isProbability
  have hIcc :
      mixingMeasureSimplex M Set.univ = M.mixingMeasure (stdSimplex ℝ (Fin k)) := by
    simpa [mixingMeasureSimplex, measurableSet_stdSimplex] using
      (comap_subtype_coe_apply (s := stdSimplex ℝ (Fin k))
        (measurableSet_stdSimplex k)
        (μ := M.mixingMeasure) (t := Set.univ))
  have hIcc_one : M.mixingMeasure (stdSimplex ℝ (Fin k)) = 1 := by
    have hIcc_eq_univ :
        M.mixingMeasure (stdSimplex ℝ (Fin k)) = M.mixingMeasure Set.univ := by
      simpa using
        (measure_of_measure_compl_eq_zero (μ := M.mixingMeasure)
          (s := stdSimplex ℝ (Fin k)) M.support_simplex)
    simpa [measure_univ] using hIcc_eq_univ
  exact ⟨by simp [hIcc, hIcc_one]⟩

/-- The Kyburg parametrized distribution for a categorical mixture at horizon `n`. -/
def pd {k : ℕ} (M : CategoricalMixture k) (n : ℕ) :
    ParametrizedDistribution (ProbSimplex k) (Fin n → Fin k) :=
  { kernel := catKernel k n
    kernel_isMarkov := catKernel_isMarkov k n
    mixingMeasure := mixingMeasureSimplex M
    mixing_isProbability := inferInstance }

/-! ## Bridge lemma -/

/-- **The Kyburg flattening bridge for categorical mixtures**:

    `flatten(pd M n) {xs} = ENNReal.ofReal (M.prob xs)`

    This identifies the Kyburg-flattened distribution evaluated at a singleton
    with the categorical mixture probability. It generalizes
    `DeFinettiConnection.flatten_apply_singleton` from Bool to Fin k. -/
theorem flatten_apply_singleton {k : ℕ} (M : CategoricalMixture k) (n : ℕ)
    (xs : Fin n → Fin k) :
    (ParametrizedDistribution.flatten (pd M n)) {xs}
      = ENNReal.ofReal (M.prob xs) := by
  classical
  -- Expand flatten as lintegral
  have hmeas : MeasurableSet ({xs} : Set (Fin n → Fin k)) := by simp
  have hflat :
      (ParametrizedDistribution.flatten (pd M n)) {xs} =
        ∫⁻ θ : ProbSimplex k,
          ENNReal.ofReal (categoricalProductPMF (↑θ : Fin k → ℝ) xs)
            ∂mixingMeasureSimplex M := by
    simpa [pd, catKernel, catPMF_toMeasure_apply_singleton, catPMF, catWeight] using
      (ParametrizedDistribution.flatten_apply (pd M n) {xs} hmeas)
  -- Convert subtype integral to set integral
  have hs : MeasurableSet (stdSimplex ℝ (Fin k)) := measurableSet_stdSimplex k
  have hsub :
      (∫⁻ θ : ProbSimplex k,
        ENNReal.ofReal (categoricalProductPMF (↑θ : Fin k → ℝ) xs)
          ∂mixingMeasureSimplex M) =
        ∫⁻ t in stdSimplex ℝ (Fin k),
          ENNReal.ofReal (categoricalProductPMF t xs) ∂M.mixingMeasure := by
    simpa [mixingMeasureSimplex, hs] using
      (lintegral_subtype_comap (μ := M.mixingMeasure) (s := stdSimplex ℝ (Fin k)) hs
        (f := fun t : Fin k → ℝ => ENNReal.ofReal (categoricalProductPMF t xs)))
  -- Convert lintegral of ofReal to ofReal of integral
  have hcont : Continuous fun t : Fin k → ℝ => categoricalProductPMF t xs := by
    unfold categoricalProductPMF
    exact continuous_finset_prod _ (fun i _ => continuous_apply (xs i))
  have hint :
      Integrable (fun t : Fin k → ℝ => categoricalProductPMF t xs)
        (M.mixingMeasure.restrict (stdSimplex ℝ (Fin k))) := by
    haveI : IsProbabilityMeasure M.mixingMeasure := M.isProbability
    have hmeas' : AEStronglyMeasurable (fun t => categoricalProductPMF t xs)
        M.mixingMeasure := hcont.measurable.aestronglyMeasurable
    have hbound :
        ∀ᵐ t ∂(M.mixingMeasure.restrict (stdSimplex ℝ (Fin k))),
          ‖categoricalProductPMF t xs‖ ≤ (1 : ℝ) := by
      refine ae_restrict_of_forall_mem (measurableSet_stdSimplex k) ?_
      intro t ht
      have hnonneg : 0 ≤ categoricalProductPMF t xs := by
        unfold categoricalProductPMF
        exact Finset.prod_nonneg (fun i _ => ht.1 (xs i))
      have hle1 : categoricalProductPMF t xs ≤ 1 := by
        rw [categoricalProductPMF_eq_power]
        refine Finset.prod_le_one (fun a _ => pow_nonneg (ht.1 a) _) (fun a _ => ?_)
        exact pow_le_one₀ (ht.1 a) (by
          have := Finset.single_le_sum (fun j _ => ht.1 j) (Finset.mem_univ a)
          linarith [ht.2])
      simp [Real.norm_of_nonneg hnonneg, hle1]
    have hs_finite : M.mixingMeasure (stdSimplex ℝ (Fin k)) ≠ ∞ := by
      have hle : M.mixingMeasure (stdSimplex ℝ (Fin k)) ≤ M.mixingMeasure Set.univ :=
        measure_mono (Set.subset_univ _)
      have huniv : M.mixingMeasure Set.univ = 1 := measure_univ
      exact ne_of_lt (lt_of_le_of_lt (hle.trans_eq huniv) (by simp))
    exact Measure.integrableOn_of_bounded hs_finite hmeas' hbound
  have hnonneg :
      (0 : (Fin k → ℝ) → ℝ) ≤ᵐ[(M.mixingMeasure.restrict (stdSimplex ℝ (Fin k)))]
        (fun t => categoricalProductPMF t xs) := by
    refine ae_restrict_of_forall_mem (measurableSet_stdSimplex k) ?_
    intro t ht
    unfold categoricalProductPMF
    exact Finset.prod_nonneg (fun i _ => ht.1 (xs i))
  have hconv :
      ∫⁻ t in stdSimplex ℝ (Fin k),
        ENNReal.ofReal (categoricalProductPMF t xs) ∂M.mixingMeasure =
      ENNReal.ofReal (∫ t in stdSimplex ℝ (Fin k),
        categoricalProductPMF t xs ∂M.mixingMeasure) := by
    simpa using
      (ofReal_integral_eq_lintegral_ofReal
        (μ := M.mixingMeasure.restrict (stdSimplex ℝ (Fin k)))
        (f := fun t => categoricalProductPMF t xs) hint hnonneg).symm
  -- Assemble
  calc
    (ParametrizedDistribution.flatten (pd M n)) {xs}
        = ∫⁻ θ : ProbSimplex k,
            ENNReal.ofReal (categoricalProductPMF (↑θ) xs)
              ∂mixingMeasureSimplex M := hflat
    _ = ∫⁻ t in stdSimplex ℝ (Fin k),
            ENNReal.ofReal (categoricalProductPMF t xs) ∂M.mixingMeasure := hsub
    _ = ENNReal.ofReal (∫ t in stdSimplex ℝ (Fin k),
            categoricalProductPMF t xs ∂M.mixingMeasure) := hconv
    _ = ENNReal.ofReal (M.prob xs) := by
          simp [CategoricalMixture.prob]

end CategoricalConnection

end Mettapedia.ProbabilityTheory.HigherOrderProbability
