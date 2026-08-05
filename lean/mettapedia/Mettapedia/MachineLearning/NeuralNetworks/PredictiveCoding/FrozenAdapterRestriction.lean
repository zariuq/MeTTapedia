import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.HeterogeneousDepthBlocks

/-!
# Frozen adapters as restrictions of a coupled path

This module replaces the former metadata-only adapter wrapper.  A backbone of
`B` segments and an adapter of `A` segments first form one path of length
`B + A`.  The attachment is therefore an actual Jacobi edge, not metadata.
Freezing is then an embed--apply--project restriction of that full operator.

The main result characterizes the restricted first-mode multiplier uniquely.
For an adapter with at least one interior vertex, it is exactly
`cos (pi / A)`, independently of `B`.  That independence is proved from the
restriction; it is not stored in a definition.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

/-! ## A1: the genuinely coupled full path -/

/-- One Jacobi step on the joined backbone--adapter path.  The backbone depth
and adapter depth both determine the full operator through their sum. -/
noncomputable def coupledBackboneAdapterStep {width : ℕ}
    (coupling : Module.End ℝ (PathBlock width))
    (backboneSegments adapterSegments : ℕ)
    (state : ℕ → PathBlock width) : ℕ → PathBlock width :=
  blockPathJacobiStep coupling (backboneSegments + adapterSegments) state

/-- A state supported on the first adapter-side neighbor of the attachment. -/
noncomputable def adapterNeighborImpulse (backboneSegments : ℕ) :
    ℕ → PathBlock 1 :=
  fun n _ => if n = backboneSegments + 1 then 1 else 0

theorem adapterNeighborImpulse_zero_on_backbone
    (backboneSegments n : ℕ) (hn : n ≤ backboneSegments) :
    adapterNeighborImpulse backboneSegments n = 0 := by
  funext i
  have hne : n ≠ backboneSegments + 1 := by omega
  simp [adapterNeighborImpulse, hne]

/-- The adapter impulse changes the next backbone update at the attachment.
This is the concrete cross-block term that the former wrapper never had. -/
theorem coupledBackboneAdapterStep_reads_across_attachment
    (backboneSegments adapterSegments : ℕ)
    (hbackbone : 0 < backboneSegments) (hadapter : 0 < adapterSegments) :
    coupledBackboneAdapterStep (LinearMap.id : Module.End ℝ (PathBlock 1))
        backboneSegments adapterSegments
        (adapterNeighborImpulse backboneSegments) backboneSegments 0 =
      1 / 2 := by
  have hne0 : backboneSegments ≠ 0 := Nat.ne_of_gt hbackbone
  have hinterior : ¬ backboneSegments + adapterSegments ≤ backboneSegments := by
    omega
  have hleft : backboneSegments - 1 ≠ backboneSegments + 1 := by omega
  simp [coupledBackboneAdapterStep, blockPathJacobiStep, hne0, hinterior,
    adapterNeighborImpulse, hleft]

/-- A step is block diagonal across the attachment if an adapter-supported
state cannot affect the attachment coordinate on the backbone side. -/
def BlockDiagonalAcrossAttachment {width : ℕ}
    (step : (ℕ → PathBlock width) → ℕ → PathBlock width)
    (backboneSegments : ℕ) : Prop :=
  ∀ state, (∀ n, n ≤ backboneSegments → state n = 0) →
    step state backboneSegments = 0

/-- Anti-vacuity crown for A1: the full joined-path operator is not block
diagonal across the backbone--adapter attachment. -/
theorem coupledBackboneAdapterStep_not_blockDiagonal
    (backboneSegments adapterSegments : ℕ)
    (hbackbone : 0 < backboneSegments) (hadapter : 0 < adapterSegments) :
    ¬ BlockDiagonalAcrossAttachment
        (coupledBackboneAdapterStep
          (LinearMap.id : Module.End ℝ (PathBlock 1))
          backboneSegments adapterSegments)
        backboneSegments := by
  intro hdiagonal
  have hzero := hdiagonal (adapterNeighborImpulse backboneSegments)
    (adapterNeighborImpulse_zero_on_backbone backboneSegments)
  have hcoordinate := congrFun hzero 0
  rw [coupledBackboneAdapterStep_reads_across_attachment
    backboneSegments adapterSegments hbackbone hadapter] at hcoordinate
  norm_num at hcoordinate

/-- The full joined path inherits the exact vector-valued sine eigenmode from
the block path theorem.  Unlike the restricted result below, its rate depends
on the total depth `B + A`. -/
theorem coupledBackboneAdapter_slowMode_eigenrelation {width : ℕ}
    (coupling : Module.End ℝ (PathBlock width))
    (couplingEigenvalue : ℝ) (amplitude : PathBlock width)
    (heigen : coupling amplitude = couplingEigenvalue • amplitude)
    (backboneSegments adapterSegments n : ℕ)
    (hsegments : 0 < backboneSegments + adapterSegments)
    (hn : n ≤ backboneSegments + adapterSegments) :
    coupledBackboneAdapterStep coupling backboneSegments adapterSegments
        (blockPathSlowMode (backboneSegments + adapterSegments) amplitude) n =
      blockPathRelaxationRate couplingEigenvalue
          (backboneSegments + adapterSegments) •
        blockPathSlowMode (backboneSegments + adapterSegments) amplitude n := by
  exact blockPathSlowMode_eigenrelation coupling couplingEigenvalue amplitude
    heigen (backboneSegments + adapterSegments) n hsegments hn

/-! ## A2: freezing as an operator restriction -/

/-- Embed an adapter state after the backbone attachment.  Coordinates before
the attachment are clamped to zero. -/
noncomputable def embedAdapterState {width : ℕ}
    (backboneSegments : ℕ) (adapterState : ℕ → PathBlock width) :
    ℕ → PathBlock width :=
  fun n => if backboneSegments ≤ n then
    adapterState (n - backboneSegments)
  else 0

/-- Enforce the frozen attachment value on the adapter-side boundary before
embedding into the full path. -/
noncomputable def clampAdapterBoundary {width : ℕ}
    (adapterState : ℕ → PathBlock width) : ℕ → PathBlock width :=
  fun n => if n = 0 then 0 else adapterState n

theorem clampAdapterBoundary_eq_self {width : ℕ}
    (adapterState : ℕ → PathBlock width) (hboundary : adapterState 0 = 0) :
    clampAdapterBoundary adapterState = adapterState := by
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [clampAdapterBoundary, hboundary]
  · simp [clampAdapterBoundary, hn]

/-- Restrict any full-path step to the adapter subspace: embed a state, apply
the supplied full operator, project after the attachment, and delete the
clamped attachment row.  This operation contains no claim about its rate. -/
noncomputable def restrictPathStepToAdapter {width : ℕ}
    (backboneSegments : ℕ)
    (fullStep : (ℕ → PathBlock width) → ℕ → PathBlock width)
    (adapterState : ℕ → PathBlock width) : ℕ → PathBlock width :=
  fun n => if n = 0 then 0 else
    fullStep
      (embedAdapterState backboneSegments (clampAdapterBoundary adapterState))
      (backboneSegments + n)

/-- Freezing applies the generic restriction operation to the genuinely
coupled operator from A1. -/
noncomputable def frozenAdapterRestriction {width : ℕ}
    (coupling : Module.End ℝ (PathBlock width))
    (backboneSegments adapterSegments : ℕ)
    (adapterState : ℕ → PathBlock width) : ℕ → PathBlock width :=
  restrictPathStepToAdapter backboneSegments
    (coupledBackboneAdapterStep coupling backboneSegments adapterSegments)
    adapterState

/-- The derived restriction is extensionally the standalone adapter Jacobi
step applied after mechanically clamping its attachment boundary.  This is
the substantive decoupling calculation: no adapter-only rate appears in the
definition of `restrictPathStepToAdapter`. -/
theorem frozenAdapterRestriction_eq_blockPathJacobiStep_clamped {width : ℕ}
    (coupling : Module.End ℝ (PathBlock width))
    (backboneSegments adapterSegments : ℕ)
    (adapterState : ℕ → PathBlock width) :
    frozenAdapterRestriction coupling backboneSegments adapterSegments
        adapterState =
      blockPathJacobiStep coupling adapterSegments
        (clampAdapterBoundary adapterState) := by
  funext n
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [frozenAdapterRestriction, restrictPathStepToAdapter,
      blockPathJacobiStep]
  by_cases hboundary : adapterSegments ≤ n
  · have hfullBoundary :
        backboneSegments + adapterSegments ≤ backboneSegments + n :=
      Nat.add_le_add_left hboundary backboneSegments
    simp [frozenAdapterRestriction, restrictPathStepToAdapter,
      coupledBackboneAdapterStep, blockPathJacobiStep, hn0, hboundary,
      hfullBoundary]
  · have hnlt : n < adapterSegments := Nat.lt_of_not_ge hboundary
    have hfull0 : backboneSegments + n ≠ 0 := by omega
    have hfullInterior :
        ¬ backboneSegments + adapterSegments ≤ backboneSegments + n := by
      omega
    have hleftLe : backboneSegments ≤ backboneSegments + n - 1 := by omega
    have hrightLe : backboneSegments ≤ backboneSegments + n + 1 := by omega
    have hleftSub :
        backboneSegments + n - 1 - backboneSegments = n - 1 := by omega
    have hrightSub :
        backboneSegments + n + 1 - backboneSegments = n + 1 := by omega
    simp [frozenAdapterRestriction, restrictPathStepToAdapter,
      coupledBackboneAdapterStep, blockPathJacobiStep, hn0, hboundary,
      hfullInterior, embedAdapterState, hleftLe, hrightLe,
      hleftSub, hrightSub]

/-- On the actual adapter error subspace, whose attachment coordinate is
zero, the frozen restriction is exactly the standalone adapter step. -/
theorem frozenAdapterRestriction_eq_blockPathJacobiStep_of_boundary_clamped
    {width : ℕ}
    (coupling : Module.End ℝ (PathBlock width))
    (backboneSegments adapterSegments : ℕ)
    (adapterState : ℕ → PathBlock width)
    (hboundary : adapterState 0 = 0) :
    frozenAdapterRestriction coupling backboneSegments adapterSegments
        adapterState =
      blockPathJacobiStep coupling adapterSegments adapterState := by
  rw [frozenAdapterRestriction_eq_blockPathJacobiStep_clamped,
    clampAdapterBoundary_eq_self adapterState hboundary]

/-! ## A3: exact restricted rate and spectral gap -/

/-- A proposed multiplier is an exact first-mode rate of the restricted
operator when it scales the adapter sine mode at every adapter coordinate. -/
noncomputable def unitPathBlockAmplitude : PathBlock 1 := fun _ => 1

def IsFrozenAdapterSlowModeRate
    (backboneSegments adapterSegments : ℕ) (rate : ℝ) : Prop :=
  ∀ n, n ≤ adapterSegments →
    frozenAdapterRestriction
        (LinearMap.id : Module.End ℝ (PathBlock 1))
        backboneSegments adapterSegments
        (blockPathSlowMode adapterSegments unitPathBlockAmplitude) n =
      rate • blockPathSlowMode adapterSegments unitPathBlockAmplitude n

theorem pathSlowMode_one_pos
    (segments : ℕ) (hsegments : 1 < segments) :
    0 < pathSlowMode segments 1 := by
  have hsegmentsReal : (1 : ℝ) < segments := by exact_mod_cast hsegments
  have hden : (0 : ℝ) < segments := by linarith
  have hanglePos : 0 < Real.pi / (segments : ℝ) :=
    div_pos Real.pi_pos hden
  have hangleLt : Real.pi / (segments : ℝ) < Real.pi := by
    rw [div_lt_iff₀ hden]
    nlinarith [Real.pi_pos]
  simpa [pathSlowMode] using
    Real.sin_pos_of_pos_of_lt_pi hanglePos hangleLt

/-- A3 crown: after restriction of the coupled `B + A` operator, the only
possible first-mode multiplier is the adapter-only rate `cos (pi / A)`.
This adds the unique rate identification; it is not a projection of the
pre-existing path bound. -/
theorem isFrozenAdapterSlowModeRate_iff
    (backboneSegments adapterSegments : ℕ)
    (hadapter : 1 < adapterSegments) (rate : ℝ) :
    IsFrozenAdapterSlowModeRate backboneSegments adapterSegments rate ↔
      rate = pathRelaxationRate adapterSegments := by
  constructor
  · intro hrate
    have hcandidate := hrate 1 (Nat.one_le_iff_ne_zero.mpr (by omega))
    rw [frozenAdapterRestriction_eq_blockPathJacobiStep_of_boundary_clamped
      (hboundary := by
        simp [blockPathSlowMode, pathSlowMode])] at hcandidate
    have hactual := blockPathSlowMode_eigenrelation
      (LinearMap.id : Module.End ℝ (PathBlock 1)) 1 unitPathBlockAmplitude
      (by simp) adapterSegments 1 (by omega)
      (Nat.one_le_iff_ne_zero.mpr (by omega))
    have hsame :
        rate • blockPathSlowMode adapterSegments unitPathBlockAmplitude 1 =
          pathRelaxationRate adapterSegments •
            blockPathSlowMode adapterSegments unitPathBlockAmplitude 1 := by
      rw [← hcandidate, hactual]
      simp [blockPathRelaxationRate]
    have hcoordinate := congrFun hsame 0
    have hmodePos := pathSlowMode_one_pos adapterSegments hadapter
    simp [blockPathSlowMode, unitPathBlockAmplitude] at hcoordinate
    rcases hcoordinate with hequal | hmodeZero
    · exact hequal
    · exact (ne_of_gt hmodePos hmodeZero).elim
  · rintro rfl n hn
    rw [frozenAdapterRestriction_eq_blockPathJacobiStep_of_boundary_clamped
      (hboundary := by
        simp [blockPathSlowMode, pathSlowMode])]
    simpa [blockPathRelaxationRate] using
      (blockPathSlowMode_eigenrelation
        (LinearMap.id : Module.End ℝ (PathBlock 1)) 1 unitPathBlockAmplitude
        (by simp) adapterSegments n (by omega) hn)

/-- Exact gap form of A3.  The premise names the actual restricted operator's
mode relation, so the adapter-only gap is a derived conclusion. -/
theorem frozenAdapterRestriction_gap_eq_adapter_gap
    (backboneSegments adapterSegments : ℕ)
    (hadapter : 1 < adapterSegments) (rate : ℝ)
    (hrate : IsFrozenAdapterSlowModeRate
      backboneSegments adapterSegments rate) :
    1 - rate = 1 - pathRelaxationRate adapterSegments := by
  rw [(isFrozenAdapterSlowModeRate_iff backboneSegments adapterSegments
    hadapter rate).mp hrate]

/-- The earned inverse-depth-squared gap bound for the restricted operator. -/
theorem frozenAdapterRestriction_gap_bound
    (backboneSegments adapterSegments : ℕ)
    (hadapter : 1 < adapterSegments) (rate : ℝ)
    (hrate : IsFrozenAdapterSlowModeRate
      backboneSegments adapterSegments rate) :
    0 ≤ 1 - rate ∧
      1 - rate ≤ (Real.pi / (adapterSegments : ℝ)) ^ 2 / 2 := by
  rw [(isFrozenAdapterSlowModeRate_iff backboneSegments adapterSegments
    hadapter rate).mp hrate]
  exact pathRelaxationRate_gap_bound adapterSegments

/-! ## A4: the partial-freezing boundary -/

/-- When both paths remain active, they form a heterogeneous two-block modal
family.  Index `0` is the backbone and index `1` is the adapter. -/
noncomputable def activeBackboneAdapterFamily
    (backboneSegments adapterSegments : ℕ)
    (hbackbone : 0 < backboneSegments) (hadapter : 0 < adapterSegments) :
    HeterogeneousDepthBlockFamily (Fin 2) 1 where
  segments := fun i => if i.val = 0 then backboneSegments else adapterSegments
  segments_pos := by
    intro i
    fin_cases i
    · simpa using hbackbone
    · simpa using hadapter
  coupling := fun _ => LinearMap.id
  couplingEigenvalue := fun _ => 1
  amplitude := fun _ => unitPathBlockAmplitude
  coupling_eigen := by simp

theorem activeBackboneAdapterFamily_segments
    (backboneSegments adapterSegments : ℕ)
    (hbackbone : 0 < backboneSegments) (hadapter : 0 < adapterSegments) :
    (activeBackboneAdapterFamily backboneSegments adapterSegments
        hbackbone hadapter).segments 0 = backboneSegments ∧
      (activeBackboneAdapterFamily backboneSegments adapterSegments
        hbackbone hadapter).segments 1 = adapterSegments := by
  simp [activeBackboneAdapterFamily]

theorem activeBackboneAdapterFamily_modeRates
    (backboneSegments adapterSegments : ℕ)
    (hbackbone : 0 < backboneSegments) (hadapter : 0 < adapterSegments) :
    (activeBackboneAdapterFamily backboneSegments adapterSegments
        hbackbone hadapter).modeRate 0 =
        pathRelaxationRate backboneSegments ∧
      (activeBackboneAdapterFamily backboneSegments adapterSegments
        hbackbone hadapter).modeRate 1 =
        pathRelaxationRate adapterSegments := by
  constructor <;>
    simp [HeterogeneousDepthBlockFamily.modeRate,
      activeBackboneAdapterFamily, blockPathRelaxationRate]

/-- With the backbone active at unit coupling, its depth bounds the global
modal gap.  This is the precise sense in which partial freezing re-imports
`B`; unlike A3, no restriction deletes the backbone block. -/
theorem activeBackboneAdapter_backbone_gap_bound
    (backboneSegments adapterSegments : ℕ)
    (hbackbone : 0 < backboneSegments) (hadapter : 0 < adapterSegments) :
    1 - (activeBackboneAdapterFamily backboneSegments adapterSegments
        hbackbone hadapter).modalSpectralRadius ≤
      (Real.pi / (backboneSegments : ℝ)) ^ 2 / 2 := by
  simpa [activeBackboneAdapterFamily] using
    ((activeBackboneAdapterFamily backboneSegments adapterSegments
      hbackbone hadapter).modalSpectralGap_le_depth_bound (i := 0) rfl)

/-- A3 positive fixture: a depth-three adapter has exact frozen rate `1/2`
even behind a depth-one-hundred backbone. -/
theorem depthHundred_backbone_depthThree_adapter_frozen_rate :
    IsFrozenAdapterSlowModeRate 100 3 (1 / 2) := by
  rw [isFrozenAdapterSlowModeRate_iff 100 3 (by norm_num)]
  norm_num [pathRelaxationRate, Real.cos_pi_div_three]

/-- Negative fixture for confusing the full and frozen operators: before
restriction, the joined depth-four path has a nonzero rate, whereas the
depth-two frozen adapter rate is zero. -/
theorem joinedDepthFour_rate_ne_depthTwo_frozen_rate :
    blockPathRelaxationRate 1 (2 + 2) ≠ pathRelaxationRate 2 := by
  rw [show blockPathRelaxationRate 1 (2 + 2) = Real.sqrt 2 / 2 by
      norm_num [blockPathRelaxationRate, pathRelaxationRate,
        Real.cos_pi_div_four],
    pathRelaxationRate_two_segments_positive_example]
  positivity

/-- Exact active-system fixture: with a depth-three backbone and depth-two
adapter, the active backbone raises the modal radius to `1/2`. -/
theorem activeBackboneThree_adapterTwo_modalSpectralRadius :
    (activeBackboneAdapterFamily 3 2 (by norm_num) (by norm_num)).modalSpectralRadius =
      1 / 2 := by
  apply le_antisymm
  · have hsup :
        (Finset.univ.sup fun i : Fin 2 =>
          (⟨|(activeBackboneAdapterFamily 3 2 (by norm_num) (by norm_num)).modeRate i|,
            abs_nonneg _⟩ : NNReal)) ≤
          (⟨1 / 2, by norm_num⟩ : NNReal) :=
      (Finset.sup_le_iff).2 (by
        intro i _hi
        fin_cases i <;>
          norm_num [HeterogeneousDepthBlockFamily.modeRate,
            activeBackboneAdapterFamily, blockPathRelaxationRate,
            pathRelaxationRate, Real.cos_pi_div_two,
            Real.cos_pi_div_three])
    exact_mod_cast hsup
  · have h :=
      (activeBackboneAdapterFamily 3 2 (by norm_num) (by norm_num))
        |>.modeRate_abs_le_modalSpectralRadius (i := 0)
    norm_num [HeterogeneousDepthBlockFamily.modeRate,
      activeBackboneAdapterFamily, blockPathRelaxationRate,
      pathRelaxationRate, Real.cos_pi_div_three] at h ⊢
    exact h

/-- A4 boundary fixture: ideal freezing leaves the depth-two adapter with
rate zero, while activating the unit-coupled depth-three backbone produces
global modal radius `1/2`. -/
theorem partialFreezing_reimports_backbone_negative :
    IsFrozenAdapterSlowModeRate 3 2 0 ∧
      HeterogeneousDepthBlockFamily.modalSpectralRadius
          (activeBackboneAdapterFamily 3 2 (by norm_num) (by norm_num)) =
        1 / 2 := by
  constructor
  · rw [isFrozenAdapterSlowModeRate_iff 3 2 (by norm_num)]
    exact pathRelaxationRate_two_segments_positive_example.symm
  · exact activeBackboneThree_adapterTwo_modalSpectralRadius

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
