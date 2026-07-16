import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
import Mettapedia.PLN.Bridges.PredictiveCoding.GaussianRevisionBridge
import Mettapedia.PLN.WorldModel.BinaryWorldModel
import Mettapedia.PLN.WorldModel.WorldModelCalculus

/-!
# Predictive-coding bridge to binary world models

This file connects the scalar linear-Gaussian predictive-coding bridge to the
`BinaryWorldModel` query surface.

The bridge is local: two unit-strength scalar Gaussian observations become
binary evidence for one world-model query, and the derived query strength
matches the existing PLN weighted-revision bridge.

Non-goals:

* This is not a theorem that predictive-coding equilibrium is global PLN
  revision.
* This is not a nonlinear predictive-coding theorem.
* This is not a Bayesian-network factorization theorem.
* This does not identify an entire predictive-coding chain state with a PLN
  posterior.
-/

namespace Mettapedia.PLN.Bridges.PredictiveCoding

open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.PLN.TruthValues.PLNTruthTower
open Mettapedia.PLN.TruthValues.PLNWeightTV
open scoped ENNReal

/-! ## Binary world-model surface -/

/-- Query labels for the predictive-coding world-model bridge.

The `Nat` fields are observation keys. Finite-index safety remains in the PC
theorems that produce these labels. -/
inductive PCWMQuery where
  | gaussianLink (depth : Nat) (node : Nat) : PCWMQuery
  deriving DecidableEq, Repr

/-- The extensional binary-evidence profile used for the local bridge. -/
abbrev PCWMState := PCWMQuery → BinaryEvidence

noncomputable instance instEvidenceTypePCWMState : EvidenceType PCWMState where

noncomputable instance instBinaryWorldModelPCWMState :
    BinaryWorldModel PCWMState PCWMQuery where
  evidence W q := W q
  evidence_add _ _ _ := rfl
  evidence_zero _ := rfl

/-- Encode a unit-strength scalar Gaussian source as binary evidence. -/
noncomputable def pcGaussianEvidenceOfSource (source : GaussianSource) : BinaryEvidence where
  pos := ENNReal.ofReal source.mean * ENNReal.ofReal source.precision
  neg := (1 - ENNReal.ofReal source.mean) * ENNReal.ofReal source.precision

/-- A point source for one PC-WM query. -/
noncomputable def pcGaussianSourceState
    (q : PCWMQuery) (source : GaussianSource) : PCWMState :=
  fun r => if r = q then pcGaussianEvidenceOfSource source else 0

/-- The revised state carrying two independent Gaussian observations for one query. -/
noncomputable def pcGaussianPairState
    (q : PCWMQuery) (source₁ source₂ : GaussianSource) : PCWMState :=
  pcGaussianSourceState q source₁ + pcGaussianSourceState q source₂

/-- Source context containing exactly the two Gaussian observation states. -/
noncomputable def pcGaussianSourceContext
    (q : PCWMQuery) (source₁ source₂ : GaussianSource) : Set PCWMState :=
  {W | W = pcGaussianSourceState q source₁ ∨ W = pcGaussianSourceState q source₂}

/-- Existing PLN weighted-revision strength for two PC Gaussian sources. -/
noncomputable def pcPLNRevisionStrength
    (source₁ source₂ : GaussianSource) : ℝ :=
  (revisionWTV
    (wtvOfPrecision source₁.mean source₁.precision
      source₁.mean_nonneg source₁.mean_le_one (le_of_lt source₁.precision_pos))
    (wtvOfPrecision source₂.mean source₂.precision
      source₂.mean_nonneg source₂.mean_le_one (le_of_lt source₂.precision_pos))).strength

/-- Existing real binary-count revision strength for two PC Gaussian sources. -/
noncomputable def pcBinaryCountsRevisionStrength
    (source₁ source₂ : GaussianSource) : ℝ :=
  ((binaryCountsOfStrengthWeight source₁.mean source₁.precision
      source₁.mean_nonneg source₁.mean_le_one (le_of_lt source₁.precision_pos)).add
    (binaryCountsOfStrengthWeight source₂.mean source₂.precision
      source₂.mean_nonneg source₂.mean_le_one (le_of_lt source₂.precision_pos))).strength

/-- Binary-world-model query strength for the revised Gaussian source pair. -/
noncomputable def pcWMQueryStrength
    (q : PCWMQuery) (source₁ source₂ : GaussianSource) : ℝ≥0∞ :=
  BinaryWorldModel.queryStrength (State := PCWMState) (Query := PCWMQuery)
    (pcGaussianPairState q source₁ source₂) q

/-- Real projection of the binary-world-model query strength. -/
noncomputable def pcWMQueryStrengthReal
    (q : PCWMQuery) (source₁ source₂ : GaussianSource) : ℝ :=
  (pcWMQueryStrength q source₁ source₂).toReal

private theorem pcGaussianEvidenceOfSource_total (source : GaussianSource) :
    (pcGaussianEvidenceOfSource source).total =
      ENNReal.ofReal source.precision := by
  unfold pcGaussianEvidenceOfSource BinaryEvidence.total
  rw [← add_mul]
  have hmean_le : ENNReal.ofReal source.mean ≤ 1 := by
    simpa using ENNReal.ofReal_le_one.mpr source.mean_le_one
  rw [add_tsub_cancel_of_le hmean_le, one_mul]

private theorem pcGaussianEvidenceOfSource_toStrength (source : GaussianSource) :
    BinaryEvidence.toStrength (pcGaussianEvidenceOfSource source) =
      ENNReal.ofReal source.mean := by
  unfold pcGaussianEvidenceOfSource
  have hmean_le : ENNReal.ofReal source.mean ≤ 1 := by
    simpa using ENNReal.ofReal_le_one.mpr source.mean_le_one
  exact BinaryEvidence.toStrength_of_scaled
    (ENNReal.ofReal source.mean) (ENNReal.ofReal source.precision)
    hmean_le (ne_of_gt (ENNReal.ofReal_pos.mpr source.precision_pos))
    ENNReal.ofReal_ne_top

private theorem pcGaussianPair_total (source₁ source₂ : GaussianSource) :
    (pcGaussianEvidenceOfSource source₁ + pcGaussianEvidenceOfSource source₂).total =
      ENNReal.ofReal source₁.precision + ENNReal.ofReal source₂.precision := by
  rw [BinaryEvidence.total, BinaryEvidence.hplus_def]
  calc
    (pcGaussianEvidenceOfSource source₁).pos + (pcGaussianEvidenceOfSource source₂).pos +
        ((pcGaussianEvidenceOfSource source₁).neg + (pcGaussianEvidenceOfSource source₂).neg)
        =
      ((pcGaussianEvidenceOfSource source₁).pos + (pcGaussianEvidenceOfSource source₁).neg) +
        ((pcGaussianEvidenceOfSource source₂).pos + (pcGaussianEvidenceOfSource source₂).neg) := by
        ac_rfl
    _ = ENNReal.ofReal source₁.precision + ENNReal.ofReal source₂.precision := by
        rw [← BinaryEvidence.total, ← BinaryEvidence.total,
          pcGaussianEvidenceOfSource_total source₁, pcGaussianEvidenceOfSource_total source₂]

private theorem pcGaussianPair_total_ne_zero (source₁ source₂ : GaussianSource) :
    (pcGaussianEvidenceOfSource source₁ + pcGaussianEvidenceOfSource source₂).total ≠ 0 := by
  rw [pcGaussianPair_total]
  intro hzero
  have h₁zero : ENNReal.ofReal source₁.precision = 0 :=
    (add_eq_zero.mp hzero).1
  exact (ne_of_gt (ENNReal.ofReal_pos.mpr source₁.precision_pos)) h₁zero

private theorem pcGaussianPair_total_toReal (source₁ source₂ : GaussianSource) :
    ((pcGaussianEvidenceOfSource source₁ + pcGaussianEvidenceOfSource source₂).total).toReal =
      source₁.precision + source₂.precision := by
  rw [pcGaussianPair_total]
  have h₁ : ENNReal.ofReal source₁.precision ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have h₂ : ENNReal.ofReal source₂.precision ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have h := ENNReal.toReal_add h₁ h₂
  simpa [ENNReal.toReal_ofReal (le_of_lt source₁.precision_pos),
    ENNReal.toReal_ofReal (le_of_lt source₂.precision_pos)] using h

private theorem pcGaussianPair_pos_toReal (source₁ source₂ : GaussianSource) :
    ((pcGaussianEvidenceOfSource source₁ + pcGaussianEvidenceOfSource source₂).pos).toReal =
      source₁.mean * source₁.precision + source₂.mean * source₂.precision := by
  rw [BinaryEvidence.hplus_def]
  have h₁ :
      ENNReal.ofReal source₁.mean * ENNReal.ofReal source₁.precision ≠
        (⊤ : ℝ≥0∞) :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have h₂ :
      ENNReal.ofReal source₂.mean * ENNReal.ofReal source₂.precision ≠
        (⊤ : ℝ≥0∞) :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have h := ENNReal.toReal_add h₁ h₂
  simpa [pcGaussianEvidenceOfSource, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal source₁.mean_nonneg,
    ENNReal.toReal_ofReal (le_of_lt source₁.precision_pos),
    ENNReal.toReal_ofReal source₂.mean_nonneg,
    ENNReal.toReal_ofReal (le_of_lt source₂.precision_pos)] using h

private theorem pcGaussianPair_toStrengthReal_eq_gaussianFusion
    (source₁ source₂ : GaussianSource) :
    (BinaryEvidence.toStrength
      (pcGaussianEvidenceOfSource source₁ + pcGaussianEvidenceOfSource source₂)).toReal =
      gaussianFusion source₁.mean source₂.mean source₁.precision source₂.precision := by
  have htotal0 := pcGaussianPair_total_ne_zero source₁ source₂
  unfold BinaryEvidence.toStrength
  rw [if_neg htotal0, ENNReal.toReal_div]
  rw [pcGaussianPair_pos_toReal source₁ source₂,
    pcGaussianPair_total_toReal source₁ source₂]
  unfold gaussianFusion
  ring

private theorem pcWMQueryStrengthReal_eq_gaussianFusion
    (q : PCWMQuery) (source₁ source₂ : GaussianSource) :
    pcWMQueryStrengthReal q source₁ source₂ =
      gaussianFusion source₁.mean source₂.mean source₁.precision source₂.precision := by
  unfold pcWMQueryStrengthReal pcWMQueryStrength BinaryWorldModel.queryStrength
  change (BinaryEvidence.toStrength ((pcGaussianPairState q source₁ source₂) q)).toReal =
    gaussianFusion source₁.mean source₂.mean source₁.precision source₂.precision
  simp [pcGaussianPairState, pcGaussianSourceState,
    pcGaussianPair_toStrengthReal_eq_gaussianFusion]

/-! ## Phase-2A review signatures -/

/-- Target 1: local scalar PC Gaussian revision agrees with the existing PLN
weighted revision and the existing binary-count revision corollary. -/
theorem pcGaussianSources_plnRevisionStrength_eq_binaryCountsRevisionStrength
    (source₁ source₂ : GaussianSource) :
    pcPLNRevisionStrength source₁ source₂ =
      pcBinaryCountsRevisionStrength source₁ source₂ := by
  unfold pcPLNRevisionStrength pcBinaryCountsRevisionStrength
  rw [← gaussianFusion_eq_plnRevisionWTV source₁ source₂]
  rw [← gaussianFusion_eq_binaryCounts_revision_strength source₁ source₂]

/-- Target 2a: world-model query extraction transports source revision to
additive binary evidence at the query. -/
theorem pcWM_query_revise_gaussian_sources
    (q : PCWMQuery) (source₁ source₂ : GaussianSource) :
    ⊢q[pcGaussianSourceContext q source₁ source₂]
      pcGaussianPairState q source₁ source₂ ⇓ q ↦
        (pcGaussianEvidenceOfSource source₁ + pcGaussianEvidenceOfSource source₂) := by
  classical
  let Γ := pcGaussianSourceContext q source₁ source₂
  let W₁ := pcGaussianSourceState q source₁
  let W₂ := pcGaussianSourceState q source₂
  have h₁ : ⊢q[Γ] W₁ ⇓ q ↦ pcGaussianEvidenceOfSource source₁ := by
    refine ⟨WMJudgmentCtx.base W₁ (by simp [Γ, W₁, pcGaussianSourceContext]), ?_⟩
    change pcGaussianEvidenceOfSource source₁ = W₁ q
    simp [W₁, pcGaussianSourceState]
  have h₂ : ⊢q[Γ] W₂ ⇓ q ↦ pcGaussianEvidenceOfSource source₂ := by
    refine ⟨WMJudgmentCtx.base W₂ (by simp [Γ, W₂, pcGaussianSourceContext]), ?_⟩
    change pcGaussianEvidenceOfSource source₂ = W₂ q
    simp [W₂, pcGaussianSourceState]
  have hrev :=
    WMJudgmentCtx.query_revise (State := PCWMState) (Query := PCWMQuery)
      (Γ := Γ) h₁ h₂
  simpa [Γ, W₁, W₂, pcGaussianPairState] using hrev

/-- Target 2b: the binary-world-model query-strength view matches existing PLN
weighted revision for the same local Gaussian source pair. -/
theorem pcWM_queryStrengthReal_eq_plnRevisionStrength
    (q : PCWMQuery) (source₁ source₂ : GaussianSource) :
    pcWMQueryStrengthReal q source₁ source₂ =
      pcPLNRevisionStrength source₁ source₂ := by
  rw [pcWMQueryStrengthReal_eq_gaussianFusion]
  unfold pcPLNRevisionStrength
  exact gaussianFusion_eq_plnRevisionWTV source₁ source₂

/-- Target 3: the equilibrium/error facts remain imported PC facts.  This
bundles the PC normal-equation, error-recursion, and localization surfaces
without turning them into PLN revision claims. -/
theorem pc_imported_equilibrium_error_localization_side
    {depth : Nat} (links : Fin depth → PCLink) (x y : ℝ) (z : PCState depth)
    (heq : pcEquilibrium links x y z)
    (i : Fin depth) (hi : i.val + 1 < depth)
    {d : Nat} (R : LocalBackwardRelaxation d) (ε₀ : ErrorState d)
    (hInit : ∀ j : Fin (d + 1), j ≠ Fin.last d → ε₀ j = 0)
    (t : Nat) (j : Fin (d + 1)) (hfar : distanceFromOutput j > t) :
    (z ∈ clampedStateSet x y ∧ pcNormalEquations links z) ∧
      pcResidualForce links z i =
        (links ⟨i.val + 1, hi⟩).gain *
          pcResidualForce links z ⟨i.val + 1, hi⟩ ∧
      (Nat.iterate R.step t ε₀) j = 0 := by
  exact ⟨(pcEquilibrium_iff_normalEquations links x y z).mp heq,
    equilibriumError_satisfies_backpropRecursion links x y z i hi heq,
    error_localization R ε₀ hInit t j hfar⟩

/-! ## Depth-2 review examples -/

/-- Unit-interval depth-2 equilibrium candidate for the positive example. -/
noncomputable def unitIntervalDepth2EquilibriumState : PCState 2 :=
  fun i => (i.val : ℝ) / 2

/-- Unit-interval off-equilibrium state for the negative example. -/
noncomputable def unitIntervalDepth2OffEquilibriumState : PCState 2 :=
  fun i => if i.val = 2 then 1 else 0

noncomputable def unitIntervalDepth2Query : PCWMQuery :=
  PCWMQuery.gaussianLink 2 1

noncomputable def unitIntervalDepth2IncomingSource : GaussianSource where
  mean := 0
  precision := 1
  mean_nonneg := by norm_num
  mean_le_one := by norm_num
  precision_pos := by norm_num

noncomputable def unitIntervalDepth2OutgoingSource : GaussianSource where
  mean := 1
  precision := 1
  mean_nonneg := by norm_num
  mean_le_one := by norm_num
  precision_pos := by norm_num

noncomputable def unitIntervalDepth2EndpointRevisionStrength : ℝ :=
  pcWMQueryStrengthReal unitIntervalDepth2Query
    unitIntervalDepth2IncomingSource unitIntervalDepth2OutgoingSource

private theorem unitIntervalDepth2PLNRevisionStrength_eq_half :
    pcPLNRevisionStrength unitIntervalDepth2IncomingSource unitIntervalDepth2OutgoingSource =
      (1 / 2 : ℝ) := by
  have h :=
    gaussianFusion_eq_plnRevisionWTV unitIntervalDepth2IncomingSource
      unitIntervalDepth2OutgoingSource
  unfold pcPLNRevisionStrength
  norm_num [gaussianFusion, unitIntervalDepth2IncomingSource,
    unitIntervalDepth2OutgoingSource] at h
  simpa [unitIntervalDepth2IncomingSource, unitIntervalDepth2OutgoingSource] using h.symm

private theorem unitIntervalDepth2EndpointRevisionStrength_eq_half :
    unitIntervalDepth2EndpointRevisionStrength = (1 / 2 : ℝ) := by
  unfold unitIntervalDepth2EndpointRevisionStrength
  rw [pcWM_queryStrengthReal_eq_plnRevisionStrength]
  exact unitIntervalDepth2PLNRevisionStrength_eq_half

private theorem unitIntervalDepth2EquilibriumState_is_equilibrium :
    pcEquilibrium unitDepth2Links 0 1 unitIntervalDepth2EquilibriumState := by
  rw [pcEquilibrium_iff_normalEquations]
  constructor
  · constructor <;> norm_num [clampedStateSet, unitIntervalDepth2EquilibriumState]
  · intro i
    fin_cases i <;>
      norm_num [pcLocalNormalEquationAt, unitDepth2Links, unitIntervalDepth2EquilibriumState,
        pcResidual]

private theorem unitIntervalDepth2OffEquilibriumState_not_equilibrium :
    ¬ pcEquilibrium unitDepth2Links 0 1 unitIntervalDepth2OffEquilibriumState := by
  intro heq
  have hnorm : pcNormalEquations unitDepth2Links unitIntervalDepth2OffEquilibriumState :=
    (pcEquilibrium_iff_normalEquations unitDepth2Links 0 1
      unitIntervalDepth2OffEquilibriumState).mp heq |>.2
  have h := hnorm (⟨1, by norm_num⟩ : Fin 3)
  norm_num [pcLocalNormalEquationAt, unitDepth2Links,
    unitIntervalDepth2OffEquilibriumState, pcResidual] at h

/-- Positive example: the unit depth-2 chain has a unit-interval equilibrium
whose interior value matches the local WM-PLN revision strength. -/
theorem pcWM_depth2Unit_positive_example :
    pcEquilibrium unitDepth2Links 0 1 unitIntervalDepth2EquilibriumState ∧
      unitIntervalDepth2EquilibriumState 1 =
        unitIntervalDepth2EndpointRevisionStrength ∧
      unitIntervalDepth2EndpointRevisionStrength = (1 / 2 : ℝ) := by
  refine ⟨unitIntervalDepth2EquilibriumState_is_equilibrium, ?_,
    unitIntervalDepth2EndpointRevisionStrength_eq_half⟩
  rw [unitIntervalDepth2EndpointRevisionStrength_eq_half]
  norm_num [unitIntervalDepth2EquilibriumState]

/-- Negative example: the same local per-link WM-PLN revision is still present
for an off-equilibrium state, so local evidence revision does not imply global
clamped-chain equilibrium. -/
theorem pcWM_depth2OffEquilibrium_negative_example :
    pcWMQueryStrengthReal unitIntervalDepth2Query
        unitIntervalDepth2IncomingSource unitIntervalDepth2OutgoingSource =
      pcPLNRevisionStrength
        unitIntervalDepth2IncomingSource unitIntervalDepth2OutgoingSource ∧
      ¬ pcEquilibrium unitDepth2Links 0 1 unitIntervalDepth2OffEquilibriumState ∧
      unitIntervalDepth2OffEquilibriumState 1 ≠
        unitIntervalDepth2EndpointRevisionStrength := by
  refine ⟨?_, unitIntervalDepth2OffEquilibriumState_not_equilibrium, ?_⟩
  · exact pcWM_queryStrengthReal_eq_plnRevisionStrength unitIntervalDepth2Query
      unitIntervalDepth2IncomingSource unitIntervalDepth2OutgoingSource
  · rw [unitIntervalDepth2EndpointRevisionStrength_eq_half]
    norm_num [unitIntervalDepth2OffEquilibriumState]

end Mettapedia.PLN.Bridges.PredictiveCoding
