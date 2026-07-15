import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.DepthPathology
import Mathlib.Data.NNReal.Basic

/-!
# Heterogeneous-depth block relaxation

This file assembles finitely many block-tridiagonal path relaxations whose
path depths, within-block couplings, and slow-mode amplitudes may differ.  The
global operator is block diagonal across the family index.  Each block retains
the exact mode rate
`couplingEigenvalue * cos (pi / segments)`, while the global modal spectral
radius is the finite supremum of the absolute block rates.

Consequently the global modal family is stable exactly when every block rate
has modulus below one.  Each individual block is bounded by the global radius,
and any unit-coupling block transfers its inverse-depth-squared path gap bound
directly to the global spectral gap.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

/-- A finite family of path blocks sharing a channel width but allowed to have
different depths, coupling operators, eigenvalues, and amplitudes. -/
structure HeterogeneousDepthBlockFamily (Block : Type*) (width : ℕ) where
  segments : Block → ℕ
  segments_pos : ∀ i, 0 < segments i
  coupling : Block → Module.End ℝ (PathBlock width)
  couplingEigenvalue : Block → ℝ
  amplitude : Block → PathBlock width
  coupling_eigen : ∀ i,
    coupling i (amplitude i) = couplingEigenvalue i • amplitude i

/-- A state containing one path-valued vector block per family member. -/
abbrev HeterogeneousDepthState (Block : Type*) (width : ℕ) :=
  Block → ℕ → PathBlock width

/-- One block-diagonal Jacobi step, using each block's own path depth and
coupling operator. -/
noncomputable def HeterogeneousDepthBlockFamily.step
    {Block : Type*} {width : ℕ}
    (family : HeterogeneousDepthBlockFamily Block width)
    (state : HeterogeneousDepthState Block width) :
    HeterogeneousDepthState Block width :=
  fun i => blockPathJacobiStep (family.coupling i) (family.segments i) (state i)

/-- Repeated block-diagonal heterogeneous relaxation. -/
noncomputable def HeterogeneousDepthBlockFamily.iterate
    {Block : Type*} {width : ℕ}
    (family : HeterogeneousDepthBlockFamily Block width)
    (state : HeterogeneousDepthState Block width) :
    ℕ → HeterogeneousDepthState Block width
  | 0 => state
  | t + 1 => family.step (family.iterate state t)

theorem HeterogeneousDepthBlockFamily.iterate_apply
    {Block : Type*} {width : ℕ}
    (family : HeterogeneousDepthBlockFamily Block width)
    (state : HeterogeneousDepthState Block width) (t : ℕ) (i : Block) (n : ℕ) :
    family.iterate state t i n =
      blockPathJacobiIterate (family.coupling i) (family.segments i)
        (state i) t n := by
  induction t generalizing n with
  | zero => rfl
  | succ t ih =>
      simp [HeterogeneousDepthBlockFamily.iterate,
        HeterogeneousDepthBlockFamily.step, blockPathJacobiIterate,
        blockPathJacobiStep, ih]

/-- Family state formed from every block's first sine mode. -/
noncomputable def HeterogeneousDepthBlockFamily.slowModeState
    {Block : Type*} {width : ℕ}
    (family : HeterogeneousDepthBlockFamily Block width) :
    HeterogeneousDepthState Block width :=
  fun i => blockPathSlowMode (family.segments i) (family.amplitude i)

/-- Exact slow-mode rate of one heterogeneous block. -/
noncomputable def HeterogeneousDepthBlockFamily.modeRate
    {Block : Type*} {width : ℕ}
    (family : HeterogeneousDepthBlockFamily Block width) (i : Block) : ℝ :=
  blockPathRelaxationRate (family.couplingEigenvalue i) (family.segments i)

/-- Every block evolves at its own exact depth-dependent rate inside the
global block-diagonal iteration. -/
theorem HeterogeneousDepthBlockFamily.slowMode_iterate_exact
    {Block : Type*} {width : ℕ}
    (family : HeterogeneousDepthBlockFamily Block width)
    (t : ℕ) (i : Block) (n : ℕ) (hn : n ≤ family.segments i) :
    family.iterate family.slowModeState t i n =
      family.modeRate i ^ t • family.slowModeState i n := by
  rw [family.iterate_apply]
  exact blockPathSlowMode_iterate_exact
    (family.coupling i) (family.couplingEigenvalue i) (family.amplitude i)
    (family.coupling_eigen i) (family.segments i) (family.segments_pos i) t n hn

/-- Finite modal spectral radius of the heterogeneous block family. -/
noncomputable def HeterogeneousDepthBlockFamily.modalSpectralRadius
    {Block : Type*} {width : ℕ} [Fintype Block]
    (family : HeterogeneousDepthBlockFamily Block width) : ℝ :=
  ((Finset.univ.sup fun i : Block =>
    (⟨|family.modeRate i|, abs_nonneg _⟩ : NNReal)) : NNReal)

theorem HeterogeneousDepthBlockFamily.modeRate_abs_le_modalSpectralRadius
    {Block : Type*} {width : ℕ} [Fintype Block] [DecidableEq Block]
    (family : HeterogeneousDepthBlockFamily Block width) (i : Block) :
    |family.modeRate i| ≤ family.modalSpectralRadius := by
  have h := Finset.le_sup
    (s := Finset.univ)
    (f := fun j : Block => (⟨|family.modeRate j|, abs_nonneg _⟩ : NNReal))
    (Finset.mem_univ i)
  exact_mod_cast h

/-- The global radius lies below one exactly when every heterogeneous block
mode lies below one. -/
theorem HeterogeneousDepthBlockFamily.modalSpectralRadius_lt_one_iff
    {Block : Type*} {width : ℕ} [Fintype Block] [DecidableEq Block]
    (family : HeterogeneousDepthBlockFamily Block width) :
    family.modalSpectralRadius < 1 ↔ ∀ i, |family.modeRate i| < 1 := by
  constructor
  · intro hradius i
    exact lt_of_le_of_lt (family.modeRate_abs_le_modalSpectralRadius i) hradius
  · intro hall
    have hnn :
        (Finset.univ.sup fun i : Block =>
          (⟨|family.modeRate i|, abs_nonneg _⟩ : NNReal)) < 1 :=
      (Finset.sup_lt_iff (by norm_num)).2 (by
        intro i _hi
        exact_mod_cast hall i)
    exact_mod_cast hnn

/-- The global radius controls every exact block multiplier at every
iteration depth. -/
theorem HeterogeneousDepthBlockFamily.modeRate_pow_le_modalSpectralRadius_pow
    {Block : Type*} {width : ℕ} [Fintype Block] [DecidableEq Block]
    (family : HeterogeneousDepthBlockFamily Block width) (i : Block) (t : ℕ) :
    |family.modeRate i| ^ t ≤ family.modalSpectralRadius ^ t := by
  exact pow_le_pow_left₀ (abs_nonneg _)
    (family.modeRate_abs_le_modalSpectralRadius i) t

/-- Below the global spectral threshold, every block's exact modal coefficient
converges to zero. -/
theorem HeterogeneousDepthBlockFamily.modeRate_pow_tendsto_zero
    {Block : Type*} {width : ℕ} [Fintype Block] [DecidableEq Block]
    (family : HeterogeneousDepthBlockFamily Block width)
    (hradius : family.modalSpectralRadius < 1) (i : Block) :
    Filter.Tendsto (fun t : ℕ => family.modeRate i ^ t)
      Filter.atTop (nhds 0) := by
  exact tendsto_pow_atTop_nhds_zero_of_abs_lt_one
    ((family.modalSpectralRadius_lt_one_iff).mp hradius i)

/-- A unit-coupling block at any selected depth bounds the global spectral
gap by that path's inverse-depth-squared gap. -/
theorem HeterogeneousDepthBlockFamily.modalSpectralGap_le_depth_bound
    {Block : Type*} {width : ℕ} [Fintype Block] [DecidableEq Block]
    (family : HeterogeneousDepthBlockFamily Block width) (i : Block)
    (hunit : family.couplingEigenvalue i = 1) :
    1 - family.modalSpectralRadius ≤
      (Real.pi / (family.segments i : ℝ)) ^ 2 / 2 := by
  have habs := family.modeRate_abs_le_modalSpectralRadius i
  have hrate : pathRelaxationRate (family.segments i) ≤
      family.modalSpectralRadius := by
    calc
      pathRelaxationRate (family.segments i) ≤
          |family.modeRate i| := by
        rw [HeterogeneousDepthBlockFamily.modeRate,
          blockPathRelaxationRate, hunit, one_mul]
        exact le_abs_self _
      _ ≤ family.modalSpectralRadius := habs
  have hgap := (pathRelaxationRate_gap_bound (family.segments i)).2
  linarith

/-! ## Two-block heterogeneous-depth fixture -/

noncomputable def heterogeneousDepthFixture :
    HeterogeneousDepthBlockFamily (Fin 2) 1 where
  segments := fun i => if i.val = 0 then 2 else 3
  segments_pos := by
    intro i
    fin_cases i <;> norm_num
  coupling := fun _ => LinearMap.id
  couplingEigenvalue := fun _ => 1
  amplitude := fun _ _ => 1
  coupling_eigen := by
    intro i
    ext j
    simp

theorem heterogeneousDepthFixture_modeRates :
    heterogeneousDepthFixture.modeRate 0 = 0 ∧
      heterogeneousDepthFixture.modeRate 1 = 1 / 2 := by
  constructor
  · norm_num [HeterogeneousDepthBlockFamily.modeRate,
      heterogeneousDepthFixture, blockPathRelaxationRate,
      pathRelaxationRate, Real.cos_pi_div_two]
  · norm_num [HeterogeneousDepthBlockFamily.modeRate,
      heterogeneousDepthFixture, blockPathRelaxationRate,
      pathRelaxationRate, Real.cos_pi_div_three]

/-- The depth-three block, rather than the depth-two block, determines the
global modal spectral radius. -/
theorem heterogeneousDepthFixture_modalSpectralRadius :
    heterogeneousDepthFixture.modalSpectralRadius = 1 / 2 := by
  apply le_antisymm
  · have hsup :
        (Finset.univ.sup fun i : Fin 2 =>
          (⟨|heterogeneousDepthFixture.modeRate i|, abs_nonneg _⟩ : NNReal)) ≤
            (⟨1 / 2, by norm_num⟩ : NNReal) :=
      (Finset.sup_le_iff).2 (by
        intro i _hi
        fin_cases i <;>
          norm_num [HeterogeneousDepthBlockFamily.modeRate,
            heterogeneousDepthFixture, blockPathRelaxationRate,
            pathRelaxationRate, Real.cos_pi_div_two,
            Real.cos_pi_div_three])
    exact_mod_cast hsup
  · have h :=
      heterogeneousDepthFixture.modeRate_abs_le_modalSpectralRadius (i := 1)
    rw [heterogeneousDepthFixture_modeRates.2, abs_of_nonneg (by norm_num)] at h
    exact h

theorem heterogeneousDepthFixture_stable_positive_example :
    heterogeneousDepthFixture.modalSpectralRadius < 1 := by
  rw [heterogeneousDepthFixture_modalSpectralRadius]
  norm_num

/-- Heterogeneous depths genuinely produce different block rates, so the
family cannot be represented by a single depth-independent exact rate. -/
theorem heterogeneousDepthFixture_rates_differ_negative_example :
    heterogeneousDepthFixture.modeRate 0 ≠
      heterogeneousDepthFixture.modeRate 1 := by
  rw [heterogeneousDepthFixture_modeRates.1,
    heterogeneousDepthFixture_modeRates.2]
  norm_num

/-- Crown: the fixture has exact per-block rates `0` and `1/2`, global radius
`1/2`, and a stable heterogeneous modal family. -/
theorem heterogeneousDepthFixture_spectral_radius_and_depth :
    heterogeneousDepthFixture.modeRate 0 = 0 ∧
      heterogeneousDepthFixture.modeRate 1 = 1 / 2 ∧
      heterogeneousDepthFixture.modalSpectralRadius = 1 / 2 ∧
      heterogeneousDepthFixture.modalSpectralRadius < 1 :=
  ⟨heterogeneousDepthFixture_modeRates.1,
    heterogeneousDepthFixture_modeRates.2,
    heterogeneousDepthFixture_modalSpectralRadius,
    heterogeneousDepthFixture_stable_positive_example⟩

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
