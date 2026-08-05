import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.ProspectiveInterference
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.TypedRegisters

/-!
# Hybrid monotone refinement and checker inheritance

The stretch rung combines two independent guarantees.  First, a fractional
gradient step on the exact scalar depth-two predictive-coding energy is safe
for fractions in `[0,2]`; every finite iterate is no worse than its seed.  The
same step has an exact geometric error formula around the unique equilibrium.

Second, the checker induces a zero/one constraint objective on refinement
actions.  Every action exposed by a workspace ranking has zero constraint
cost, and ranked acceptance remains exactly checker acceptance.  Thus learned
scores may order refinements while neither the energy refinement nor the
decoder changes the accepted language.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier

open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
open Mettapedia.GSLT.LanguageDef.AtomicRefinement
open Mettapedia.GSLT.LanguageDef.RefinementInterface
open Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

/-! ## Safe scalar predictive-coding refinement -/

/-- Exact equilibrium of the scalar depth-two predictive-coding energy. -/
noncomputable def pcDepth2Equilibrium
    (input target gain₀ gain₁ precision₀ precision₁ : ℝ) : ℝ :=
  (precision₀ * gain₀ * input + precision₁ * gain₁ * target) /
    (precision₀ + precision₁ * gain₁ ^ 2)

/-- The depth-two gradient is smoothness times displacement from equilibrium. -/
theorem pcDepth2Gradient_eq_smoothness_mul_error
    (input target gain₀ gain₁ precision₀ precision₁ latent : ℝ)
    (hprecision₀ : 0 < precision₀) (hprecision₁ : 0 < precision₁) :
    pcDepth2Gradient input target gain₀ gain₁ precision₀ precision₁ latent =
      pcDepth2Smoothness gain₁ precision₀ precision₁ *
        (latent - pcDepth2Equilibrium input target gain₀ gain₁
          precision₀ precision₁) := by
  have hden : precision₀ + precision₁ * gain₁ ^ 2 ≠ 0 := by
    have : 0 < precision₀ + precision₁ * gain₁ ^ 2 := by
      nlinarith [sq_nonneg gain₁, mul_nonneg (le_of_lt hprecision₁) (sq_nonneg gain₁)]
    exact ne_of_gt this
  unfold pcDepth2Gradient pcDepth2Smoothness pcDepth2Equilibrium
  field_simp [hden]
  ring

/-- A step specified as a fraction of the inverse smoothness. -/
noncomputable def pcDepth2FractionalRefine
    (fraction input target gain₀ gain₁ precision₀ precision₁ latent : ℝ) : ℝ :=
  latent -
    (fraction / pcDepth2Smoothness gain₁ precision₀ precision₁) *
      pcDepth2Gradient input target gain₀ gain₁ precision₀ precision₁ latent

/-- Any ordinary step in `[0, 2/L]` is energy non-increasing. -/
theorem pcDepth2_safeStep_energy_nonincreasing
    (input target gain₀ gain₁ precision₀ precision₁ latent step : ℝ)
    (hprecision₀ : 0 < precision₀) (hprecision₁ : 0 < precision₁)
    (hstep₀ : 0 ≤ step)
    (hstepMax : step ≤ 2 / pcDepth2Smoothness gain₁ precision₀ precision₁) :
    pcDepth2Energy input target gain₀ gain₁ precision₀ precision₁
        (latent - step *
          pcDepth2Gradient input target gain₀ gain₁ precision₀ precision₁ latent) ≤
      pcDepth2Energy input target gain₀ gain₁ precision₀ precision₁ latent := by
  have hL := pcDepth2Smoothness_pos gain₁ precision₀ precision₁
    hprecision₀ hprecision₁
  have haccept : armijoCondition
      (pcDepth2Energy input target gain₀ gain₁ precision₀ precision₁)
      latent
      (pcDepth2Gradient input target gain₀ gain₁ precision₀ precision₁ latent)
      0 step := by
    apply armijoCondition_of_descentUpperBound
      (pcDepth2Energy input target gain₀ gain₁ precision₀ precision₁)
      latent
      (pcDepth2Gradient input target gain₀ gain₁ precision₀ precision₁ latent)
      (pcDepth2Smoothness gain₁ precision₀ precision₁) 0 step
      hL hstep₀
    · simpa using hstepMax
    · exact pcDepth2_hasDescentUpperBoundAt
        input target gain₀ gain₁ precision₀ precision₁ latent
  exact armijoCondition_energy_nonincreasing
    (pcDepth2Energy input target gain₀ gain₁ precision₀ precision₁)
    latent
    (pcDepth2Gradient input target gain₀ gain₁ precision₀ precision₁ latent)
    0 step (by norm_num) hstep₀ haccept

/-- Fractions in `[0,2]` satisfy the safe-step energy guarantee. -/
theorem pcDepth2FractionalRefine_energy_nonincreasing
    (fraction input target gain₀ gain₁ precision₀ precision₁ latent : ℝ)
    (hprecision₀ : 0 < precision₀) (hprecision₁ : 0 < precision₁)
    (hfraction₀ : 0 ≤ fraction) (hfraction₂ : fraction ≤ 2) :
    pcDepth2Energy input target gain₀ gain₁ precision₀ precision₁
        (pcDepth2FractionalRefine fraction input target gain₀ gain₁
          precision₀ precision₁ latent) ≤
      pcDepth2Energy input target gain₀ gain₁ precision₀ precision₁ latent := by
  unfold pcDepth2FractionalRefine
  apply pcDepth2_safeStep_energy_nonincreasing
    input target gain₀ gain₁ precision₀ precision₁ latent
    (fraction / pcDepth2Smoothness gain₁ precision₀ precision₁)
    hprecision₀ hprecision₁
  · exact div_nonneg hfraction₀ (le_of_lt
      (pcDepth2Smoothness_pos gain₁ precision₀ precision₁
        hprecision₀ hprecision₁))
  · exact (div_le_div_iff_of_pos_right
      (pcDepth2Smoothness_pos gain₁ precision₀ precision₁
        hprecision₀ hprecision₁)).2 hfraction₂

/-- Every finite sequence of the same safe fractional refinement has energy no
greater than its seed. -/
theorem pcDepth2FractionalRefine_iterate_energy_le
    (fraction input target gain₀ gain₁ precision₀ precision₁ : ℝ)
    (hprecision₀ : 0 < precision₀) (hprecision₁ : 0 < precision₁)
    (hfraction₀ : 0 ≤ fraction) (hfraction₂ : fraction ≤ 2)
    (steps : ℕ) (seed : ℝ) :
    pcDepth2Energy input target gain₀ gain₁ precision₀ precision₁
        (Nat.iterate
          (pcDepth2FractionalRefine fraction input target gain₀ gain₁
            precision₀ precision₁) steps seed) ≤
      pcDepth2Energy input target gain₀ gain₁ precision₀ precision₁ seed := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans
        (pcDepth2FractionalRefine_energy_nonincreasing
          fraction input target gain₀ gain₁ precision₀ precision₁
          (Nat.iterate
            (pcDepth2FractionalRefine fraction input target gain₀ gain₁
              precision₀ precision₁) steps seed)
          hprecision₀ hprecision₁ hfraction₀ hfraction₂)
        ih

/-- One fractional step contracts equilibrium error by exactly `1-fraction`. -/
theorem pcDepth2FractionalRefine_error_exact
    (fraction input target gain₀ gain₁ precision₀ precision₁ latent : ℝ)
    (hprecision₀ : 0 < precision₀) (hprecision₁ : 0 < precision₁) :
    pcDepth2FractionalRefine fraction input target gain₀ gain₁
        precision₀ precision₁ latent -
        pcDepth2Equilibrium input target gain₀ gain₁ precision₀ precision₁ =
      (1 - fraction) *
        (latent - pcDepth2Equilibrium input target gain₀ gain₁
          precision₀ precision₁) := by
  have hL : pcDepth2Smoothness gain₁ precision₀ precision₁ ≠ 0 :=
    ne_of_gt (pcDepth2Smoothness_pos gain₁ precision₀ precision₁
      hprecision₀ hprecision₁)
  rw [pcDepth2FractionalRefine,
    pcDepth2Gradient_eq_smoothness_mul_error
      input target gain₀ gain₁ precision₀ precision₁ latent
      hprecision₀ hprecision₁]
  field_simp [hL]
  ring

/-- Exact geometric contraction over every finite iteration count. -/
theorem pcDepth2FractionalRefine_iterate_error_exact
    (fraction input target gain₀ gain₁ precision₀ precision₁ : ℝ)
    (hprecision₀ : 0 < precision₀) (hprecision₁ : 0 < precision₁)
    (steps : ℕ) (seed : ℝ) :
    Nat.iterate
        (pcDepth2FractionalRefine fraction input target gain₀ gain₁
          precision₀ precision₁) steps seed -
        pcDepth2Equilibrium input target gain₀ gain₁ precision₀ precision₁ =
      (1 - fraction) ^ steps *
        (seed - pcDepth2Equilibrium input target gain₀ gain₁
          precision₀ precision₁) := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [Function.iterate_succ_apply']
      rw [pcDepth2FractionalRefine_error_exact
        fraction input target gain₀ gain₁ precision₀ precision₁
        (Nat.iterate
          (pcDepth2FractionalRefine fraction input target gain₀ gain₁
            precision₀ precision₁) steps seed)
        hprecision₀ hprecision₁]
      rw [ih, pow_succ']
      ring

/-- Absolute geometric contraction formula. -/
theorem pcDepth2FractionalRefine_iterate_abs_error_exact
    (fraction input target gain₀ gain₁ precision₀ precision₁ : ℝ)
    (hprecision₀ : 0 < precision₀) (hprecision₁ : 0 < precision₁)
    (steps : ℕ) (seed : ℝ) :
    |Nat.iterate
        (pcDepth2FractionalRefine fraction input target gain₀ gain₁
          precision₀ precision₁) steps seed -
        pcDepth2Equilibrium input target gain₀ gain₁ precision₀ precision₁| =
      |1 - fraction| ^ steps *
        |seed - pcDepth2Equilibrium input target gain₀ gain₁
          precision₀ precision₁| := by
  rw [pcDepth2FractionalRefine_iterate_error_exact
    fraction input target gain₀ gain₁ precision₀ precision₁
    hprecision₀ hprecision₁ steps seed, abs_mul, abs_pow]

/-! ## Checker-derived constraint objective -/

/-- Zero for checker-listed legal actions and one otherwise. -/
noncomputable def checkerConstraintObjective
    (root : AtomicRoot) (state : root.State)
    (action : RefineAction root.Hole root.Head) : ℝ := by
  classical
  exact if action ∈ root.legalActions state then 0 else 1

/-- Every action surfaced by a workspace ranking has zero checker constraint
cost, for arbitrary learned scores and recurrence depth. -/
theorem ranking_checkerConstraintObjective_zero
    {root : AtomicRoot} (decoder : LegalActionWorkspaceDecoder root)
    (state : root.State) (action : RefineAction root.Hole root.Head)
    (hlisted : action ∈ decoder.ranking state) :
    checkerConstraintObjective root state action = 0 := by
  classical
  have hlegal : action ∈ root.legalActions state :=
    (decoder.legalActions_perm_ranking state).mem_iff.mpr hlisted
  simp [checkerConstraintObjective, hlegal]

/-- Checker authority is inherited unchanged by the hybrid decoder. -/
theorem hybrid_rankedAccepts_iff_checkerAccepts
    {root : AtomicRoot} (decoder : LegalActionWorkspaceDecoder root)
    (laws : AtomicRootLaws root)
    {budget : ℕ} {trace : List (RefineAction root.Hole root.Head)}
    {program : root.Program} :
    root.asRefinementInterface.RankedAccepts decoder.ranking budget trace program ↔
      root.asRefinementInterface.Accepts budget trace program :=
  decoder.rankedAccepts_iff_accepts laws

/-- Combined stretch crown: safe refinement never worsens the scalar PC
energy, and learned ranking leaves checker acceptance exactly unchanged. -/
theorem hybrid_monotone_refinement_and_legality_crown
    (fraction input target gain₀ gain₁ precision₀ precision₁ : ℝ)
    (hprecision₀ : 0 < precision₀) (hprecision₁ : 0 < precision₁)
    (hfraction₀ : 0 ≤ fraction) (hfraction₂ : fraction ≤ 2)
    (steps : ℕ) (seed : ℝ)
    {root : AtomicRoot} (decoder : LegalActionWorkspaceDecoder root)
    (laws : AtomicRootLaws root)
    {budget : ℕ} {trace : List (RefineAction root.Hole root.Head)}
    {program : root.Program} :
    pcDepth2Energy input target gain₀ gain₁ precision₀ precision₁
        (Nat.iterate
          (pcDepth2FractionalRefine fraction input target gain₀ gain₁
            precision₀ precision₁) steps seed) ≤
        pcDepth2Energy input target gain₀ gain₁ precision₀ precision₁ seed ∧
      (root.asRefinementInterface.RankedAccepts
          decoder.ranking budget trace program ↔
        root.asRefinementInterface.Accepts budget trace program) := by
  exact ⟨pcDepth2FractionalRefine_iterate_energy_le
      fraction input target gain₀ gain₁ precision₀ precision₁
      hprecision₀ hprecision₁ hfraction₀ hfraction₂ steps seed,
    decoder.rankedAccepts_iff_accepts laws⟩

/-- Strong checker-instantiated crown.  In one statement, finite refinement
never worsens the PC energy, every surfaced action has zero checker-derived
constraint cost, and the checker accepts exactly the same traces with or
without learned ranking. -/
theorem hybrid_refinement_constraint_and_legality_crown
    (fraction input target gain₀ gain₁ precision₀ precision₁ : ℝ)
    (hprecision₀ : 0 < precision₀) (hprecision₁ : 0 < precision₁)
    (hfraction₀ : 0 ≤ fraction) (hfraction₂ : fraction ≤ 2)
    (steps : ℕ) (seed : ℝ)
    {root : AtomicRoot} (decoder : LegalActionWorkspaceDecoder root)
    (laws : AtomicRootLaws root) (state : root.State)
    (action : RefineAction root.Hole root.Head)
    (hlisted : action ∈ decoder.ranking state)
    {budget : ℕ} {trace : List (RefineAction root.Hole root.Head)}
    {program : root.Program} :
    pcDepth2Energy input target gain₀ gain₁ precision₀ precision₁
        (Nat.iterate
          (pcDepth2FractionalRefine fraction input target gain₀ gain₁
            precision₀ precision₁) steps seed) ≤
        pcDepth2Energy input target gain₀ gain₁ precision₀ precision₁ seed ∧
      checkerConstraintObjective root state action = 0 ∧
      (root.asRefinementInterface.RankedAccepts
          decoder.ranking budget trace program ↔
        root.asRefinementInterface.Accepts budget trace program) := by
  exact ⟨pcDepth2FractionalRefine_iterate_energy_le
      fraction input target gain₀ gain₁ precision₀ precision₁
      hprecision₀ hprecision₁ hfraction₀ hfraction₂ steps seed,
    ranking_checkerConstraintObjective_zero decoder state action hlisted,
    decoder.rankedAccepts_iff_accepts laws⟩

/-- Positive fixture: half-fraction refinement contracts absolute error by
exactly `2^{-steps}`. -/
theorem halfFraction_refinement_geometric
    (input target gain₀ gain₁ precision₀ precision₁ : ℝ)
    (hprecision₀ : 0 < precision₀) (hprecision₁ : 0 < precision₁)
    (steps : ℕ) (seed : ℝ) :
    |Nat.iterate
        (pcDepth2FractionalRefine (1 / 2) input target gain₀ gain₁
          precision₀ precision₁) steps seed -
        pcDepth2Equilibrium input target gain₀ gain₁ precision₀ precision₁| =
      (1 / 2 : ℝ) ^ steps *
        |seed - pcDepth2Equilibrium input target gain₀ gain₁
          precision₀ precision₁| := by
  rw [pcDepth2FractionalRefine_iterate_abs_error_exact
    (1 / 2) input target gain₀ gain₁ precision₀ precision₁
    hprecision₀ hprecision₁ steps seed]
  norm_num

/-- Negative boundary: fraction two is energy-safe but has unit-magnitude
error factor, so non-increase alone does not imply strict contraction. -/
theorem doubleFraction_not_strictly_contractive :
    |1 - (2 : ℝ)| = 1 := by
  norm_num

#print axioms hybrid_monotone_refinement_and_legality_crown
#print axioms hybrid_refinement_constraint_and_legality_crown
#print axioms ranking_checkerConstraintObjective_zero

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier
