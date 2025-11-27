import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Integral
import Mettapedia.MeasureTheory.FromSymmetry

/-
# Integration with symmetric measures

Week 3 extends the symmetry-based measure theory to standard integration
results by reusing Mathlib's machinery via `toMeasure`.
-/

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory

namespace Mettapedia.MeasureTheory

/-- Symmetric measures support Lebesgue integrability, restated using the
standard `Integrable` criterion. The proof is immediate since `toMeasure`
produces a Mathlib measure. -/
theorem symmetric_measure_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : UnnormalizedValuation (Set Ω))
    (cox : UnnormalizedCox (Set Ω) μ)
    (h_sigma : ∀ (f : ℕ → Set Ω), (∀ i j, i ≠ j → Disjoint (f i) (f j)) →
               μ.val (⨆ i, f i) = ∑' i, μ.val (f i))
    (f : Ω → ℝ) (hf : Measurable f) :
    Integrable f (toMeasure μ cox h_sigma) ↔
    (∫⁻ x, ‖f x‖ₑ ∂(toMeasure μ cox h_sigma)) < ⊤ := by
  classical
  -- Directly by definition of `Integrable`.
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨hf.aestronglyMeasurable, h⟩

/-- Change of variables for translation-invariant symmetric measures.
This reduces to the left invariance obtained in `translation_invariant_is_haar`. -/
theorem change_of_variables_translation
    (G : Type*) [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [BorelSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    (μ : UnnormalizedValuation (Set G))
    (cox : UnnormalizedCox (Set G) μ)
    (h_sigma : ∀ (f : ℕ → Set G), (∀ i j, i ≠ j → Disjoint (f i) (f j)) →
               μ.val (⨆ i, f i) = ∑' i, μ.val (f i))
    (h_trans : TranslationInvariant G μ)
    (f : G → ℝ) (g : G) :
    ∫ x, f (g * x) ∂(toMeasure μ cox h_sigma) =
    ∫ x, f x ∂(toMeasure μ cox h_sigma) := by
  classical
  -- Equip `toMeasure` with the left-invariance instance and reuse the
  -- standard lemma `integral_mul_left_eq_self`.
  have inst : Measure.IsMulLeftInvariant (toMeasure μ cox h_sigma) :=
    translation_invariant_is_haar (μ := μ) (cox := cox)
      (h_sigma := h_sigma) (h_trans := h_trans)
  -- Provide the typeclass instance for the integral lemma.
  let _ : Measure.IsMulLeftInvariant (toMeasure μ cox h_sigma) := inst
  simpa using (integral_mul_left_eq_self (μ := toMeasure μ cox h_sigma) f g)

/-- Monotone convergence for symmetric measures, lifted from Mathlib. -/
theorem monotone_convergence_symmetric
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : UnnormalizedValuation (Set Ω))
    (cox : UnnormalizedCox (Set Ω) μ)
    (h_sigma : ∀ (f : ℕ → Set Ω), (∀ i j, i ≠ j → Disjoint (f i) (f j)) →
               μ.val (⨆ i, f i) = ∑' i, μ.val (f i))
    (f : ℕ → Ω → ℝ≥0∞) (hf_meas : ∀ n, Measurable (f n))
    (hf_mono : ∀ x, Monotone (fun n => f n x)) :
    (∫⁻ x, ⨆ n, f n x ∂(toMeasure μ cox h_sigma)) =
    ⨆ n, ∫⁻ x, f n x ∂(toMeasure μ cox h_sigma) := by
  classical
  -- Direct application of the monotone convergence theorem for `lintegral`.
  have hmono_fun : Monotone f := fun n m hnm x => hf_mono x hnm
  have := lintegral_iSup (μ := toMeasure μ cox h_sigma) (f := f) hf_meas hmono_fun
  simpa using this

end Mettapedia.MeasureTheory
