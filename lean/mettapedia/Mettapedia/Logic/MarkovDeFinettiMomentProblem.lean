import Mettapedia.Logic.MarkovDeFinettiHardBase
import Mettapedia.Logic.MarkovDeFinettiRecurrence
import Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
import Mettapedia.Logic.MarkovExchangeability
import Mettapedia.ProbabilityTheory.FiniteMeasureSupport
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov

/-! LLM primer:
- Route B proof of Markov de Finetti: direct moment problem on compact parameter space.
- Bypasses row kernels entirely. Key insight: prefix-measure additivity reduces
  length-≤-n constraints to length-=n constraints.
- MeasurableSpace on MarkovParam k: the ACTIVE HardBase uses wordProb-generated σ-algebra.
  This file needs the BOREL σ-algebra (from compact topology) for Prokhorov + continuity.
  Compatibility: wordProb-generated ≤ Borel (since wordProb is continuous).
  Final bridge uses Measure.trim.

# Markov de Finetti via Moment Problem on Compact Parameter Space
-/

noncomputable section

namespace Mettapedia.Logic

open scoped Classical BigOperators NNReal ENNReal
open MeasureTheory Finset
open Mettapedia.ProbabilityTheory.FiniteMeasureSupport

namespace MarkovDeFinettiHard

variable {k : ℕ}

/-! ## Layer 1: Topology and compactness on MarkovParam k

Ported from `_archive/MarkovDeFinetti/Logic/MarkovDeFinettiHardBase.lean`.
MarkovParam k ≅ ProbabilityMeasure (Fin k) × (Fin k → ProbabilityMeasure (Fin k)),
which is a product of compact spaces. -/

namespace MarkovParam

/-- Project MarkovParam to the product type. -/
def toProd (θ : MarkovParam k) :
    ProbabilityMeasure (Fin k) × (Fin k → ProbabilityMeasure (Fin k)) :=
  (θ.init, θ.trans)

/-- Reconstruct MarkovParam from the product type. -/
def ofProd (p :
    ProbabilityMeasure (Fin k) × (Fin k → ProbabilityMeasure (Fin k))) :
    MarkovParam k :=
  ⟨p.1, p.2⟩

@[simp] lemma toProd_ofProd
    (p : ProbabilityMeasure (Fin k) × (Fin k → ProbabilityMeasure (Fin k))) :
    toProd (ofProd (k := k) p) = p := by
  cases p; rfl

@[simp] lemma ofProd_toProd (θ : MarkovParam k) :
    ofProd (k := k) (toProd θ) = θ := by
  cases θ; rfl

instance : TopologicalSpace (MarkovParam k) :=
  TopologicalSpace.induced (toProd (k := k)) inferInstance

lemma continuous_toProd : Continuous (toProd (k := k)) :=
  continuous_induced_dom

lemma continuous_ofProd : Continuous (ofProd (k := k)) := by
  have : Continuous ((toProd (k := k)) ∘ (ofProd (k := k))) := by
    simp only [Function.comp_def, toProd_ofProd]
    exact continuous_id
  exact (continuous_induced_rng (f := toProd (k := k)) (g := ofProd (k := k))).2 this

noncomputable def homeomorphProd :
    MarkovParam k ≃ₜ
      (ProbabilityMeasure (Fin k) × (Fin k → ProbabilityMeasure (Fin k))) :=
{ toEquiv :=
  { toFun := toProd (k := k)
    invFun := ofProd (k := k)
    left_inv := by intro θ; simp
    right_inv := by intro p; simp }
  continuous_toFun := continuous_toProd (k := k)
  continuous_invFun := continuous_ofProd (k := k) }

instance : CompactSpace (MarkovParam k) :=
  (homeomorphProd (k := k)).symm.compactSpace

instance : T2Space (MarkovParam k) :=
  (homeomorphProd (k := k)).symm.t2Space

/-- The Borel σ-algebra on MarkovParam k (from the compact product topology).
This is FINER than the wordProb-generated σ-algebra from HardBase. -/
def borelMS : MeasurableSpace (MarkovParam k) := borel (MarkovParam k)

end MarkovParam

/-! ## Layer 2: Continuity of wordProb in θ

Ported from archived HardBase. The key chain:
  θ.init({a}) continuous (singleton evaluation on ProbabilityMeasure)
  → initProb continuous → stepProb continuous → wordProbAux continuous
  → wordProbNN continuous → wordProb continuous. -/

private lemma continuous_apply_singleton_enn (b : Fin k) :
    Continuous (fun μ : ProbabilityMeasure (Fin k) =>
      ((μ : Measure (Fin k)) (Set.singleton b))) := by
  classical
  let f : C(Fin k, ℝ≥0) :=
    { toFun := fun x => if x = b then 1 else 0
      continuous_toFun := continuous_of_discreteTopology }
  have hcont :
      Continuous (fun μ : ProbabilityMeasure (Fin k) =>
        ∫⁻ x, f x ∂(μ : Measure (Fin k))) :=
    ProbabilityMeasure.continuous_lintegral_continuousMap (X := Fin k) (f := f)
  have hEq :
      (fun μ : ProbabilityMeasure (Fin k) => ∫⁻ x, f x ∂(μ : Measure (Fin k))) =
        fun μ : ProbabilityMeasure (Fin k) =>
          ((μ : Measure (Fin k)) (Set.singleton b)) := by
    funext μ
    have hs : MeasurableSet (Set.singleton b) := by simp
    have hf :
        (fun x : Fin k => (f x : ℝ≥0∞)) = (Set.singleton b).indicator (1 : Fin k → ℝ≥0∞) := by
      funext x
      by_cases hxb : x = b
      · subst hxb
        have hx : x ∈ (Set.singleton x : Set (Fin k)) := rfl
        simp [f, Set.indicator, hx]
      · simp [f, hxb, Set.indicator, show x ∉ Set.singleton b from hxb]
    simp [hf, lintegral_indicator_one hs]
  simpa [hEq] using hcont

private lemma continuous_apply_singleton (b : Fin k) :
    Continuous (fun μ : ProbabilityMeasure (Fin k) => μ (Set.singleton b)) := by
  classical
  have henn := continuous_apply_singleton_enn (k := k) b
  have hnn :
      Continuous (fun μ : ProbabilityMeasure (Fin k) =>
        ((μ : Measure (Fin k)) (Set.singleton b)).toNNReal) := by
    refine continuous_iff_continuousAt.2 ?_
    intro μ
    exact (ENNReal.tendsto_toNNReal (by simp)).comp (henn.tendsto μ)
  simpa [ProbabilityMeasure.coeFn_def] using hnn

private lemma continuous_initProb (a : Fin k) :
    Continuous (fun θ : MarkovParam k => initProb (k := k) θ a) := by
  have hθ : Continuous (fun θ : MarkovParam k => θ.init) := by
    simpa [MarkovParam.toProd, Function.comp_def] using
      (continuous_fst.comp (MarkovParam.continuous_toProd (k := k)))
  exact (continuous_apply_singleton (k := k) a).comp hθ

private lemma continuous_stepProb (a b : Fin k) :
    Continuous (fun θ : MarkovParam k => stepProb (k := k) θ a b) := by
  have hθ : Continuous (fun θ : MarkovParam k => θ.trans a) := by
    have : Continuous (fun θ : MarkovParam k => (MarkovParam.toProd (k := k) θ).2 a) :=
      (continuous_apply a).comp (continuous_snd.comp (MarkovParam.continuous_toProd (k := k)))
    simpa [MarkovParam.toProd] using this
  exact (continuous_apply_singleton (k := k) b).comp hθ

/-- Public Borel-side continuity of the initial-state mass of a `MarkovParam`. -/
theorem continuous_initProb_borel (a : Fin k) :
    Continuous (fun θ : MarkovParam k => initProb (k := k) θ a) :=
  continuous_initProb (k := k) a

/-- Public Borel-side continuity of the one-step transition mass of a
`MarkovParam`. -/
theorem continuous_stepProb_borel (a b : Fin k) :
    Continuous (fun θ : MarkovParam k => stepProb (k := k) θ a b) :=
  continuous_stepProb (k := k) a b

private lemma continuous_wordProbAux (a : Fin k) :
    ∀ xs : List (Fin k), Continuous (fun θ : MarkovParam k => wordProbAux (k := k) θ a xs) := by
  intro xs
  induction xs generalizing a with
  | nil => simpa [wordProbAux] using continuous_const
  | cons b xs ih =>
    simpa [wordProbAux, Pi.mul_def] using (continuous_stepProb (k := k) a b).mul (ih (a := b))

theorem continuous_wordProbNN :
    ∀ xs : List (Fin k), Continuous (fun θ : MarkovParam k => wordProbNN (k := k) θ xs) := by
  intro xs
  cases xs with
  | nil => simpa [wordProbNN] using continuous_const
  | cons a xs =>
    simpa [wordProbNN, Pi.mul_def] using
      (continuous_initProb (k := k) a).mul (continuous_wordProbAux (k := k) (a := a) xs)

theorem continuous_wordProb :
    ∀ xs : List (Fin k), Continuous (fun θ : MarkovParam k => wordProb (k := k) θ xs) := by
  intro xs
  exact ENNReal.continuous_coe.comp (continuous_wordProbNN (k := k) xs)

/-- wordProb is measurable w.r.t. the Borel σ-algebra (from continuity). -/
theorem measurable_wordProb_borel (xs : List (Fin k)) :
    @Measurable _ _ MarkovParam.borelMS _ (fun θ : MarkovParam k => wordProb (k := k) θ xs) := by
  letI : MeasurableSpace (MarkovParam k) := MarkovParam.borelMS
  haveI : BorelSpace (MarkovParam k) := ⟨rfl⟩
  exact (continuous_wordProb (k := k) xs).measurable

/-- The initial-state mass of a `MarkovParam` is Borel measurable. -/
theorem measurable_initProb_borel (a : Fin k) :
    @Measurable _ _ MarkovParam.borelMS _ (fun θ : MarkovParam k => initProb (k := k) θ a) := by
  letI : MeasurableSpace (MarkovParam k) := MarkovParam.borelMS
  haveI : BorelSpace (MarkovParam k) := ⟨rfl⟩
  exact (continuous_initProb_borel (k := k) a).measurable

/-- The one-step transition mass of a `MarkovParam` is Borel measurable. -/
theorem measurable_stepProb_borel (a b : Fin k) :
    @Measurable _ _ MarkovParam.borelMS _ (fun θ : MarkovParam k => stepProb (k := k) θ a b) := by
  letI : MeasurableSpace (MarkovParam k) := MarkovParam.borelMS
  haveI : BorelSpace (MarkovParam k) := ⟨rfl⟩
  exact (continuous_stepProb_borel (k := k) a b).measurable

/-! ## σ-algebra compatibility

The active HardBase defines `MeasurableSpace (MarkovParam k) := markovParamMeasurableSpace k`
(generated by wordProb evaluations). The Borel σ-algebra is finer. We record the inclusion
so that Borel-measurable measures can be used with the active infrastructure. -/

theorem wordProbGenerated_le_borel :
    markovParamMeasurableSpace k ≤ MarkovParam.borelMS (k := k) := by
  -- markovParamMeasurableSpace is the sup of comapMS for each wordProb · xs.
  -- Each comapMS (wordProb · xs) ≤ borel because wordProb · xs is continuous → Borel measurable.
  apply iSup_le
  intro xs s hs
  rcases hs with ⟨t, ht, rfl⟩
  exact (measurable_wordProb_borel (k := k) xs) ht

/-! ## Layer 3: Constraint sets and closedness

For each word xs, the set of probability measures π on MarkovParam k satisfying
∫ wordProb θ xs dπ = μ(xs) is closed. The level-n constraint set (all words of length ≤ n)
is a finite intersection of closed sets in the compact ProbabilityMeasure (MarkovParam k). -/

-- Abbreviation for the Borel-σ ProbabilityMeasure on MarkovParam k.
-- This is the space we optimize over; it is compact by Prokhorov.
abbrev ProbMarkov (k : ℕ) := @ProbabilityMeasure (MarkovParam k) MarkovParam.borelMS

-- Integration of wordProb against a Borel probability measure on MarkovParam k.
def momentMapWord (xs : List (Fin k)) (π : ProbMarkov k) : ℝ≥0∞ :=
  @MeasureTheory.lintegral (MarkovParam k) MarkovParam.borelMS
    (π : @Measure (MarkovParam k) MarkovParam.borelMS)
    (fun θ => wordProb (k := k) θ xs)

/-! ## Layer 4: wordProb additivity + reduction lemma

wordProb satisfies the same tree-additivity as prefix measures:
  wordProb θ xs = Σ_a wordProb θ (xs ++ [a])
This lets us reduce length-≤-n constraints to length-=n constraints. -/

theorem stepProb_sum_enn (θ : MarkovParam k) (a : Fin k) :
    ∑ b : Fin k, (stepProb (k := k) θ a b : ℝ≥0∞) = 1 := by
  have h := probabilityMeasure_sum_singletons_enn (θ.trans a)
  rw [show (∑ b : Fin k, (stepProb (k := k) θ a b : ℝ≥0∞)) =
    ∑ b : Fin k, ((θ.trans a : Measure (Fin k)) ({b} : Set (Fin k))) from by
    congr 1; funext b; exact probabilityMeasure_coe_singleton (θ.trans a) b]
  exact h

theorem initProb_sum_enn (θ : MarkovParam k) :
    ∑ a : Fin k, (initProb (k := k) θ a : ℝ≥0∞) = 1 := by
  have h := probabilityMeasure_sum_singletons_enn θ.init
  rw [show (∑ a : Fin k, (initProb (k := k) θ a : ℝ≥0∞)) =
    ∑ a : Fin k, ((θ.init : Measure (Fin k)) ({a} : Set (Fin k))) from by
    congr 1; funext a; exact probabilityMeasure_coe_singleton θ.init a]
  exact h

-- wordProbAux additivity: tail probability sums over next states
theorem wordProbAux_append_sum (θ : MarkovParam k) (a : Fin k) :
    ∀ xs : List (Fin k),
      (wordProbAux (k := k) θ a xs : ℝ≥0∞) =
      ∑ b : Fin k, (wordProbAux (k := k) θ a (xs ++ [b]) : ℝ≥0∞) := by
  intro xs
  induction xs generalizing a with
  | nil =>
    simp only [wordProbAux, List.nil_append, mul_one, ENNReal.coe_one]
    exact (stepProb_sum_enn (k := k) θ a).symm
  | cons c xs ih =>
    simp only [wordProbAux, List.cons_append, ENNReal.coe_mul]
    rw [ih (a := c), Finset.mul_sum]

-- wordProb additivity: the main tree-sum identity
theorem wordProb_append_sum (θ : MarkovParam k) (xs : List (Fin k)) :
    wordProb (k := k) θ xs = ∑ a : Fin k, wordProb (k := k) θ (xs ++ [a]) := by
  simp only [wordProb]
  cases xs with
  | nil =>
    simp only [wordProbNN, List.nil_append, wordProbAux, ENNReal.coe_one, ENNReal.coe_mul]
    conv_lhs => rw [show (1 : ℝ≥0∞) = ∑ a : Fin k, (initProb (k := k) θ a : ℝ≥0∞) from
      (initProb_sum_enn (k := k) θ).symm]
    congr 1; funext a
    simp [mul_one]
  | cons b ys =>
    simp only [wordProbNN, List.cons_append, ENNReal.coe_mul]
    rw [wordProbAux_append_sum (k := k) θ b ys, Finset.mul_sum]

end MarkovDeFinettiHard

end Mettapedia.Logic
