/-
Counterexample: the unrestricted all-sources Kleisli mediator property is FALSE.

The counting measure on `ℕ → Bool` (viewed as a Kleisli morphism from PUnit)
commutes with all finitary permutations (bijection invariance of counting measure),
but admits no mediator through `iidSequenceKleisliHomTheta`:

- For every θ ∈ [0,1] and every singleton {ω₀}, `iid(θ)({ω₀}) = 0`
  (geometric decay θ·(1−θ)^(n−1) → 0 for interior θ; factor vanishes at endpoints).
- Therefore `∫ iid(θ)({ω₀}) dμ(θ) = 0` for any mixing measure μ.
- But `count({ω₀}) = 1`, so no factorization `bind μ iid = count` is possible.
-/

import Mettapedia.CategoryTheory.DeFinettiKleisliGirySkeleton
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Analysis.SpecificLimits.Basic

namespace Mettapedia.CategoryTheory

open CategoryTheory MeasureTheory Filter
open scoped ENNReal

-- ============================================================
-- Section 1: Counterexample sequence and basic tools
-- ============================================================

/-- The mixed sequence: true at position 0, false everywhere else. -/
private def mixedSeq : GlobalBinarySeq := fun n => n == 0

/-- Any singleton is contained in its prefix event at any horizon. -/
private lemma singleton_subset_seqPrefixEvent (ω : GlobalBinarySeq) (n : ℕ) :
    {ω} ⊆ seqPrefixEvent n (fun i : Fin n => ω i) := by
  intro ω' hω'; simp only [Set.mem_singleton_iff] at hω'; intro i; simp [hω']

-- ============================================================
-- Section 2: Prefix count computation for mixedSeq
-- ============================================================

private lemma mixedSeq_prefix_countTrue (n : ℕ) (hn : 1 ≤ n) :
    Mettapedia.Logic.Exchangeability.countTrue (fun i : Fin n => mixedSeq i) = 1 := by
  simp only [Mettapedia.Logic.Exchangeability.countTrue, mixedSeq]
  have : (Finset.univ.filter (fun i : Fin n => ((i : ℕ) == 0) = true)) =
      ({⟨0, by omega⟩} : Finset (Fin n)) := by ext i; simp [Fin.ext_iff, beq_iff_eq]
  rw [this]; simp

private lemma mixedSeq_prefix_countFalse (n : ℕ) (hn : 1 ≤ n) :
    Mettapedia.Logic.Exchangeability.countFalse (fun i : Fin n => mixedSeq i) = n - 1 := by
  have hpart := Mettapedia.Logic.Exchangeability.count_partition (fun i : Fin n => mixedSeq i)
  have hct := mixedSeq_prefix_countTrue n hn; omega

-- ============================================================
-- Section 3: iidSequenceKernelTheta singleton = 0
-- ============================================================

/-- Prefix bound: for any θ and n ≥ 2, iid(θ)({mixedSeq}) ≤ θ·(1-θ)^(n-1). -/
private lemma iid_mixedSeq_le_prefix_bound (θ : LatentTheta) (n : ℕ) (hn : 2 ≤ n) :
    iidSequenceKernelTheta θ ({mixedSeq} : Set GlobalBinarySeq) ≤
      ENNReal.ofReal ((θ : ℝ) * (1 - (θ : ℝ)) ^ (n - 1)) := by
  calc iidSequenceKernelTheta θ ({mixedSeq} : Set GlobalBinarySeq)
      ≤ iidSequenceKernelTheta θ (seqPrefixEvent n (fun i : Fin n => mixedSeq i)) :=
          measure_mono (singleton_subset_seqPrefixEvent mixedSeq n)
    _ = (iidPrefixKernel n θ) ({fun i : Fin n => mixedSeq i} : Set (Fin n → Bool)) :=
          iidSequenceKernelTheta_prefix_apply_unconditional θ n _
    _ = ENNReal.ofReal (Mettapedia.Logic.DeFinetti.bernoulliProductPMF (θ : ℝ)
          (fun i : Fin n => mixedSeq i)) := by
          simp [iidPrefixKernel,
            Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.kernel,
            Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.weight]
    _ = ENNReal.ofReal ((θ : ℝ) * (1 - (θ : ℝ)) ^ (n - 1)) := by
          congr 1
          rw [Mettapedia.Logic.DeFinetti.bernoulliProductPMF_eq_power,
              mixedSeq_prefix_countTrue n (by omega), mixedSeq_prefix_countFalse n (by omega)]
          ring

/-- For θ = 0 or θ = 1, the bound at n=2 is immediately 0. -/
private lemma iid_mixedSeq_eq_zero_endpoint (θ : LatentTheta)
    (h : (θ : ℝ) = 0 ∨ (θ : ℝ) = 1) :
    iidSequenceKernelTheta θ ({mixedSeq} : Set GlobalBinarySeq) = 0 := by
  have hbound := iid_mixedSeq_le_prefix_bound θ 2 (by omega)
  simp only [show 2 - 1 = 1 from rfl, pow_one] at hbound
  apply le_antisymm _ zero_le
  calc iidSequenceKernelTheta θ ({mixedSeq} : Set GlobalBinarySeq)
      ≤ ENNReal.ofReal ((θ : ℝ) * (1 - (θ : ℝ))) := hbound
    _ = 0 := by rcases h with h | h <;> simp [h]

/-- For 0 < θ < 1, the geometric decay θ·(1-θ)^(n-1) → 0 forces the singleton
measure to vanish. -/
private lemma iid_mixedSeq_eq_zero_interior (θ : LatentTheta)
    (h0 : 0 < (θ : ℝ)) (h1 : (θ : ℝ) < 1) :
    iidSequenceKernelTheta θ ({mixedSeq} : Set GlobalBinarySeq) = 0 := by
  apply le_antisymm _ zero_le
  have hle : ∀ n : ℕ, iidSequenceKernelTheta θ ({mixedSeq} : Set GlobalBinarySeq) ≤
      ENNReal.ofReal ((θ : ℝ) * (1 - (θ : ℝ)) ^ n) := by
    intro n
    have := iid_mixedSeq_le_prefix_bound θ (n + 2) (by omega)
    simp only [show n + 2 - 1 = n + 1 from by omega] at this
    calc iidSequenceKernelTheta θ ({mixedSeq} : Set GlobalBinarySeq)
        ≤ ENNReal.ofReal ((θ : ℝ) * (1 - (θ : ℝ)) ^ (n + 1)) := this
      _ ≤ ENNReal.ofReal ((θ : ℝ) * (1 - (θ : ℝ)) ^ n) := by
            apply ENNReal.ofReal_le_ofReal
            apply mul_le_mul_of_nonneg_left _ (le_of_lt h0)
            exact pow_le_pow_of_le_one (by linarith) (by linarith) (Nat.le_succ n)
  have htend : Tendsto (fun n => ENNReal.ofReal ((θ : ℝ) * (1 - (θ : ℝ)) ^ n))
      atTop (nhds 0) := by
    rw [← ENNReal.ofReal_zero]
    apply (ENNReal.continuous_ofReal.tendsto 0).comp
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : (0:ℝ) ≤ 1 - θ)
      (by linarith : 1 - (θ : ℝ) < 1)).const_mul (θ : ℝ)
    rwa [mul_zero] at this
  exact ge_of_tendsto htend (Eventually.of_forall hle)

/-- Main crux: iidSequenceKernelTheta θ {mixedSeq} = 0 for ALL θ ∈ [0,1]. -/
theorem iidSequenceKernelTheta_singleton_mixedSeq_eq_zero (θ : LatentTheta) :
    iidSequenceKernelTheta θ ({mixedSeq} : Set GlobalBinarySeq) = 0 := by
  by_cases h0 : (θ : ℝ) = 0
  · exact iid_mixedSeq_eq_zero_endpoint θ (Or.inl h0)
  · by_cases h1 : (θ : ℝ) = 1
    · exact iid_mixedSeq_eq_zero_endpoint θ (Or.inr h1)
    · exact iid_mixedSeq_eq_zero_interior θ
        (lt_of_le_of_ne θ.2.1 (Ne.symm h0))
        (lt_of_le_of_ne θ.2.2 h1)

-- ============================================================
-- Section 4: bind μ iid on singleton = 0
-- ============================================================

/-- For any measure μ on LatentTheta: bind μ iid ({mixedSeq}) = 0. -/
theorem bind_iid_singleton_mixedSeq_eq_zero (μ : Measure LatentTheta) :
    (μ.bind (fun θ => iidSequenceKernelTheta θ)) ({mixedSeq} : Set GlobalBinarySeq) = 0 := by
  rw [Measure.bind_apply (MeasurableSet.singleton _)
    (ProbabilityTheory.Kernel.measurable iidSequenceKernelTheta).aemeasurable]
  simp [iidSequenceKernelTheta_singleton_mixedSeq_eq_zero]

-- ============================================================
-- Section 5: Counting measure invariant under permutation
-- ============================================================

/-- Counting measure is invariant under permutation of sequences. -/
private lemma count_map_finSuppPermuteSeq (τ : FinSuppPermNat) :
    (Measure.count : Measure GlobalBinarySeq).map (finSuppPermuteSeq τ) = Measure.count := by
  ext s hs
  rw [Measure.map_apply (measurable_finSuppPermuteSeq τ) hs]
  have hpre : finSuppPermuteSeq τ ⁻¹' s = (finSuppPermuteSeq τ⁻¹) '' s := by
    ext ω; constructor
    · intro h
      exact ⟨finSuppPermuteSeq τ ω, h, by
        rw [← finSuppPermuteSeq_mul]
        simp [show τ⁻¹ * τ = 1 from inv_mul_cancel τ, finSuppPermuteSeq_one]⟩
    · rintro ⟨ω', hω', hωω'⟩
      show finSuppPermuteSeq τ ω ∈ s
      rw [show ω = finSuppPermuteSeq τ⁻¹ ω' from hωω'.symm, ← finSuppPermuteSeq_mul,
        show τ * τ⁻¹ = 1 from mul_inv_cancel τ, finSuppPermuteSeq_one]; exact hω'
  rw [hpre]
  exact Measure.count_injective_image
    (fun a b h => by
      have := congrArg (finSuppPermuteSeq τ) h
      rwa [← finSuppPermuteSeq_mul, ← finSuppPermuteSeq_mul,
        show τ * τ⁻¹ = 1 from mul_inv_cancel τ,
        finSuppPermuteSeq_one, finSuppPermuteSeq_one] at this) s

-- ============================================================
-- Section 6: Counting-measure Kleisli morphism
-- ============================================================

/-- The counting-measure kernel from PUnit to GlobalBinarySeq. -/
private noncomputable def countKernel : ProbabilityTheory.Kernel PUnit GlobalBinarySeq where
  toFun := fun _ => Measure.count
  measurable' := measurable_const

/-- The counting-measure Kleisli morphism from PUnit to Bool^ℕ. -/
private noncomputable def countKleisliHom :=
  kernelToKleisliHom
    (A := (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of PUnit) : KleisliGiry))
    (B := KleisliBinarySeqObj) countKernel

/-- The counting-measure morphism commutes with all finitary permutations. -/
private lemma countKleisliHom_commutes :
    ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp countKleisliHom (finSuppPermKleisliHom τ) =
        countKleisliHom := by
  intro τ
  apply kleisliHom_ext; intro a
  show Measure.bind (countKernel a) (fun x => Measure.dirac (finSuppPermuteSeq τ x)) =
    countKernel a
  change Measure.bind Measure.count (fun x => Measure.dirac (finSuppPermuteSeq τ x)) =
    Measure.count
  rw [Measure.bind_dirac_eq_map Measure.count (measurable_finSuppPermuteSeq τ)]
  exact count_map_finSuppPermuteSeq τ

-- ============================================================
-- Section 7: The main theorem
-- ============================================================

/-- The unrestricted all-sources Kleisli mediator property is FALSE:
the counting measure on `ℕ → Bool` (from `PUnit`) commutes with all
permutations but has no mediator through `iidSequenceKleisliHomTheta`,
because every singleton has iid-measure 0 for all θ while counting
measure assigns mass 1 to every singleton. -/
theorem not_allSourcesKleisli_unrestricted :
    ¬ KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted := by
  intro huniv
  -- Instantiate with A = PUnit, κhom = counting measure
  obtain ⟨m, hm, _⟩ :=
    huniv (CategoryTheory.Kleisli.mk MeasCat.Giry (MeasCat.of PUnit))
      countKleisliHom countKleisliHom_commutes
  -- hm : comp m iidSequenceKleisliHomTheta = countKleisliHom
  -- Extract measure-level equality at PUnit.unit
  have hmeq : (CategoryTheory.CategoryStruct.comp m iidSequenceKleisliHomTheta).1.1 PUnit.unit =
    countKleisliHom.1.1 PUnit.unit :=
    kleisliHom_congr_fun hm PUnit.unit
  -- LHS: the composed measure is bind (m PUnit.unit) iid
  -- bind _ iid on {mixedSeq} = 0
  have hlhs : Measure.bind (m.1.1 PUnit.unit) (fun θ => iidSequenceKernelTheta θ)
    ({mixedSeq} : Set GlobalBinarySeq) = 0 :=
    bind_iid_singleton_mixedSeq_eq_zero (m.1.1 PUnit.unit)
  -- RHS: the count measure on {mixedSeq} = 1
  have hrhs : (Measure.count : Measure GlobalBinarySeq) ({mixedSeq}) = 1 :=
    Measure.count_singleton _
  -- Cast hmeq to Measure GlobalBinarySeq equality, then evaluate on {mixedSeq}
  have hmeq' : (Measure.bind (m.1.1 PUnit.unit) (fun θ => iidSequenceKernelTheta θ) :
    Measure GlobalBinarySeq) = (Measure.count : Measure GlobalBinarySeq) := hmeq
  have h01 : (0 : ENNReal) = 1 := by
    have h := congr_fun (congr_arg DFunLike.coe hmeq') ({mixedSeq} : Set GlobalBinarySeq)
    rw [hlhs] at h; rw [hrhs] at h; exact h
  exact absurd h01 (by norm_num)

/-- The unrestricted strengthening is also false: it implies
`KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted` which is
refuted by the counting-measure counterexample above. -/
theorem not_defaultAllSourcesKernel_to_allSourcesKleisli_unrestricted_strengthening
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hunivDefault :
      ∀ (Y' : Type) [MeasurableSpace Y'],
        KernelLatentThetaUniversalMediator (Y := Y') (Ω := GlobalBinarySeq) coordProcess) :
    ¬ DefaultAllSourcesKernel_to_allSourcesKleisli_unrestricted_strengthening :=
  fun hstrength => not_allSourcesKleisli_unrestricted (hstrength hglobal hunivDefault)

/-- Assumption-free negation: the unrestricted strengthening hypothesis is false,
using the unconditional latent-Dirac witness and default all-sources mediator
internally. No external hypotheses required. -/
theorem not_defaultAllSourcesKernel_to_allSourcesKleisli_unrestricted_strengthening' :
    ¬ DefaultAllSourcesKernel_to_allSourcesKleisli_unrestricted_strengthening :=
  not_defaultAllSourcesKernel_to_allSourcesKleisli_unrestricted_strengthening
    (iidSequenceKernelTheta_globalFinitaryInvariance_of_latentDirac
      iidSequenceKernelTheta_represents_latentDirac_unconditional)
    (fun Y' _ => kernelLatentThetaUniversalMediator_default_typeFamily Y')

end Mettapedia.CategoryTheory
