import Mettapedia.Logic.PLNFirstOrder.FuzzyMeasureCore
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Choquet Quantifier Semantics

Choquet-style quantitative semantics for `[0,1]`-valued fuzzy profiles over
arbitrary domains equipped with a capacity.

The quantitative core is the threshold-capacity integral

`∫_0^1 ν({u | t ≤ f u}) dt`.

This file keeps the theorem surface intentionally compact:

- the Choquet integrand and score
- bounds in `[0,1]`
- monotonicity
- crisp-indicator reduction
- constant-profile cases
- Chapter-11 style truth predicates based on the Choquet score
-/

namespace Mettapedia.Logic.PLNFirstOrder

open scoped unitInterval
open MeasureTheory

namespace FuzzyCapacity

variable {U : Type*} [MeasurableSpace U]

/-- Real threshold cut used by the Choquet-style threshold integral. -/
def choquetLevelCut (x : ℝ) (f : FuzzyProfile U) : Set U :=
  {u | x ≤ (f u : ℝ)}

/-- The real-valued Choquet integrand `x ↦ ν({u | x ≤ f u})`. -/
def choquetIntegrand (ν : FuzzyCapacity U) (f : FuzzyProfile U) (x : ℝ) : ℝ :=
  ν (choquetLevelCut x f)

/-- The Choquet integrand is antitone in the threshold. -/
theorem choquetIntegrand_antitone
    (ν : FuzzyCapacity U) (f : FuzzyProfile U) :
    Antitone (choquetIntegrand ν f) := by
  intro x y hxy
  unfold choquetIntegrand choquetLevelCut
  exact ν.mono (by
    intro u hu
    exact le_trans hxy hu)

/-- The Choquet integrand is interval-integrable on `[0,1]`. -/
theorem choquetIntegrand_intervalIntegrable
    (ν : FuzzyCapacity U) (f : FuzzyProfile U) :
    IntervalIntegrable (choquetIntegrand ν f) volume (0 : ℝ) 1 :=
  (choquetIntegrand_antitone ν f).intervalIntegrable

/-- The real Choquet score on `[0,1]`. -/
noncomputable def choquetIntegralReal
    (ν : FuzzyCapacity U) (f : FuzzyProfile U) : ℝ :=
  ∫ x in (0 : ℝ)..1, choquetIntegrand ν f x

theorem choquetIntegralReal_nonneg
    (ν : FuzzyCapacity U) (f : FuzzyProfile U) :
    0 ≤ choquetIntegralReal ν f := by
  unfold choquetIntegralReal
  refine intervalIntegral.integral_nonneg ?_ ?_
  · norm_num
  · intro x _
    exact FuzzyCapacity.cap_nonneg ν (choquetLevelCut x f)

theorem choquetIntegralReal_le_one
    (ν : FuzzyCapacity U) (f : FuzzyProfile U) :
    choquetIntegralReal ν f ≤ 1 := by
  unfold choquetIntegralReal
  have hfi : IntervalIntegrable (choquetIntegrand ν f) volume (0 : ℝ) 1 :=
    choquetIntegrand_intervalIntegrable ν f
  have hconst : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (0 : ℝ) 1 :=
    intervalIntegrable_const
  have hle :=
    intervalIntegral.integral_mono
      (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ))
      (f := choquetIntegrand ν f) (g := fun _ : ℝ => (1 : ℝ))
      (by norm_num) hfi hconst (by
        intro x
        exact FuzzyCapacity.cap_le_one ν (choquetLevelCut x f))
  simpa using hle.trans_eq (by simp)

/-- Bundled Choquet score in the unit interval. -/
noncomputable def choquetIntegral
    (ν : FuzzyCapacity U) (f : FuzzyProfile U) : I :=
  ⟨choquetIntegralReal ν f, ⟨choquetIntegralReal_nonneg ν f, choquetIntegralReal_le_one ν f⟩⟩

/-- Pointwise monotonicity of the real Choquet score. -/
theorem choquetIntegralReal_mono
    (ν : FuzzyCapacity U) (f g : FuzzyProfile U)
    (hfg : ∀ u, f u ≤ g u) :
    choquetIntegralReal ν f ≤ choquetIntegralReal ν g := by
  unfold choquetIntegralReal
  have hfi : IntervalIntegrable (choquetIntegrand ν f) volume (0 : ℝ) 1 :=
    choquetIntegrand_intervalIntegrable ν f
  have hgi : IntervalIntegrable (choquetIntegrand ν g) volume (0 : ℝ) 1 :=
    choquetIntegrand_intervalIntegrable ν g
  refine intervalIntegral.integral_mono
      (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ))
      (f := choquetIntegrand ν f) (g := choquetIntegrand ν g)
      (by norm_num) hfi hgi ?_
  intro x
  unfold choquetIntegrand choquetLevelCut
  exact ν.mono (by
    intro u hu
    exact le_trans hu (show (f u : ℝ) ≤ (g u : ℝ) from hfg u))

/-- Pointwise monotonicity of the bundled Choquet score. -/
theorem choquetIntegral_mono
    (ν : FuzzyCapacity U) (f g : FuzzyProfile U)
    (hfg : ∀ u, f u ≤ g u) :
    choquetIntegral ν f ≤ choquetIntegral ν g :=
  choquetIntegralReal_mono ν f g hfg

section LevelCutLemmas

variable {U : Type*}

/-- On the open-right unit interval, the Choquet level cut of a crisp indicator is
exactly its support. -/
theorem choquetLevelCut_crispIndicator_of_mem_Ioc
    (A : Set U) {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    choquetLevelCut x (FuzzyProfile.crispIndicator A) = A := by
  ext u
  by_cases hu : u ∈ A
  · simp [choquetLevelCut, FuzzyProfile.crispIndicator, hu, hx.2]
  · have hx0 : ¬ x ≤ (0 : ℝ) := by linarith [hx.1]
    simp [choquetLevelCut, FuzzyProfile.crispIndicator, hu, hx0]

/-- On the open-right unit interval, the Choquet level cut of the constant-zero
profile is empty. -/
theorem choquetLevelCut_constantZero_of_mem_Ioc
    {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    choquetLevelCut x (FuzzyProfile.const (U := U) (0 : I)) = ∅ := by
  ext u
  have hx0 : ¬ x ≤ (0 : ℝ) := by linarith [hx.1]
  simp [choquetLevelCut, FuzzyProfile.const, hx0]

/-- On the open-right unit interval, the Choquet level cut of the constant-one
profile is the whole domain. -/
theorem choquetLevelCut_constantOne_of_mem_Ioc
    {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    choquetLevelCut x (FuzzyProfile.const (U := U) (1 : I)) = Set.univ := by
  ext u
  simp [choquetLevelCut, FuzzyProfile.const, hx.2]

end LevelCutLemmas

/-- Crisp indicators reduce the Choquet score exactly to the underlying capacity. -/
theorem choquetIntegral_crispIndicator
    (ν : FuzzyCapacity U) (A : Set U) :
    choquetIntegral ν (FuzzyProfile.crispIndicator A) = ν A := by
  apply Subtype.ext
  unfold choquetIntegral
  change choquetIntegralReal ν (FuzzyProfile.crispIndicator A) = (ν A : ℝ)
  unfold choquetIntegralReal
  calc
    ∫ x in (0 : ℝ)..1, choquetIntegrand ν (FuzzyProfile.crispIndicator A) x
      = ∫ x in (0 : ℝ)..1, (ν A : ℝ) := by
          apply intervalIntegral.integral_congr_ae
          exact Filter.Eventually.of_forall (fun x hx =>
            by
              have hx' : x ∈ Set.Ioc (0 : ℝ) 1 := by
                simpa [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hx
              simp [choquetIntegrand, choquetLevelCut_crispIndicator_of_mem_Ioc (U := U) A hx'])
    _ = (ν A : ℝ) := by simp

/-- Constant-zero Choquet score is bottom. -/
theorem choquetIntegral_constantZero
    (ν : FuzzyCapacity U) :
    choquetIntegral ν (FuzzyProfile.const (U := U) (0 : I)) = 0 := by
  apply Subtype.ext
  unfold choquetIntegral
  change choquetIntegralReal ν (FuzzyProfile.const (U := U) (0 : I)) = 0
  unfold choquetIntegralReal
  calc
    ∫ x in (0 : ℝ)..1, choquetIntegrand ν (FuzzyProfile.const (U := U) (0 : I)) x
      = ∫ x in (0 : ℝ)..1, (0 : ℝ) := by
          apply intervalIntegral.integral_congr_ae
          exact Filter.Eventually.of_forall (fun x hx =>
            by
              have hx' : x ∈ Set.Ioc (0 : ℝ) 1 := by
                simpa [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hx
              simp [choquetIntegrand, choquetLevelCut_constantZero_of_mem_Ioc (U := U) hx', ν.cap_empty])
    _ = 0 := by simp

/-- Constant-one Choquet score is top for normalized capacities. -/
theorem choquetIntegral_constantOne
    (ν : FuzzyCapacity U) (hν : IsNormalized ν) :
    choquetIntegral ν (FuzzyProfile.const (U := U) (1 : I)) = 1 := by
  apply Subtype.ext
  unfold choquetIntegral
  change choquetIntegralReal ν (FuzzyProfile.const (U := U) (1 : I)) = 1
  unfold choquetIntegralReal
  calc
    ∫ x in (0 : ℝ)..1, choquetIntegrand ν (FuzzyProfile.const (U := U) (1 : I)) x
      = ∫ x in (0 : ℝ)..1, (1 : ℝ) := by
          apply intervalIntegral.integral_congr_ae
          exact Filter.Eventually.of_forall (fun x hx =>
            by
              have hx' : x ∈ Set.Ioc (0 : ℝ) 1 := by
                simpa [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hx
              simpa [choquetIntegrand, choquetLevelCut_constantOne_of_mem_Ioc (U := U) hx'] using hν)
    _ = 1 := by simp

end FuzzyCapacity

variable {U : Type*} [MeasurableSpace U]

/-- The bundled Choquet score exposed at the public quantifier layer. -/
noncomputable def choquetScoreInf
    (ν : FuzzyCapacity U) (f : FuzzyProfile U) : I :=
  FuzzyCapacity.choquetIntegral ν f

/-- Generic interval truth predicate based on the Choquet score. -/
def choquetIntervalHoldsInf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U) (f : FuzzyProfile U) : Prop :=
  p.LPC ≤ (choquetScoreInf ν f : ℝ) ∧ (choquetScoreInf ν f : ℝ) ≤ p.UPC

/-- Choquet-style universal truth predicate. -/
def choquetForAllHoldsInf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U) (f : FuzzyProfile U) : Prop :=
  p.PCL ≤ (choquetScoreInf ν f : ℝ)

/-- Choquet-style existential truth predicate, dualized through complement. -/
def choquetThereExistsHoldsInf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U) (f : FuzzyProfile U) : Prop :=
  p.PCL ≤ 1 - (choquetScoreInf ν (FuzzyProfile.compl f) : ℝ)

theorem choquetScoreInf_mono
    (ν : FuzzyCapacity U) (f g : FuzzyProfile U)
    (hfg : ∀ u, f u ≤ g u) :
    choquetScoreInf ν f ≤ choquetScoreInf ν g :=
  FuzzyCapacity.choquetIntegral_mono ν f g hfg

theorem choquetIntervalHoldsInf_iff_of_eq
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (f g : FuzzyProfile U)
    (hfg : choquetScoreInf ν f = choquetScoreInf ν g) :
    choquetIntervalHoldsInf p ν f ↔ choquetIntervalHoldsInf p ν g := by
  unfold choquetIntervalHoldsInf
  simp [hfg]

theorem choquetForAllHoldsInf_mono_of_pointwise
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (f g : FuzzyProfile U)
    (hfg : ∀ u, f u ≤ g u)
    (hf : choquetForAllHoldsInf p ν f) :
    choquetForAllHoldsInf p ν g := by
  unfold choquetForAllHoldsInf at *
  exact le_trans hf (choquetScoreInf_mono ν f g hfg)

theorem choquetThereExistsHoldsInf_iff_compl
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U) (f : FuzzyProfile U) :
    choquetThereExistsHoldsInf p ν f ↔
      p.PCL ≤ 1 - (choquetScoreInf ν (FuzzyProfile.compl f) : ℝ) :=
  Iff.rfl

theorem choquetScoreInf_constantZero_eq_zero
    (ν : FuzzyCapacity U) :
    choquetScoreInf ν (FuzzyProfile.const (U := U) (0 : I)) = 0 :=
  FuzzyCapacity.choquetIntegral_constantZero ν

theorem choquetScoreInf_constantOne_eq_one
    (ν : FuzzyCapacity U) (hν : FuzzyCapacity.IsNormalized ν) :
    choquetScoreInf ν (FuzzyProfile.const (U := U) (1 : I)) = 1 :=
  FuzzyCapacity.choquetIntegral_constantOne ν hν

end Mettapedia.Logic.PLNFirstOrder
