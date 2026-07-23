import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.SpectralPolynomialAcceleration

/-!
# Safeguarded acceptance for composite settling blocks

An accelerated settling block may contain an internally expansive sweep even
when its complete endpoint is contractive.  A per-sweep monotonicity test
therefore rejects some certified blocks before their corrective sweep runs.

This module makes the composite block the atomic proposal.  Its endpoint is
accepted only when the declared energy is no larger than the current energy
plus tolerance; otherwise execution falls back to a baseline step.  If both
candidate maps contract toward the same target, the selected map retains a
geometric target-error bound with the worse of their two factors.  This is a
targeted convergence certificate, not a claim that the state-dependent
selector is pairwise contractive between arbitrary initial states.

The endpoint fixture uses the existing `[1,9]` two-rate polynomial: its first
high-curvature sweep expands error by a factor of two, while the complete
block contracts it by `4/7` and is accepted by the safeguard.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace SafeguardedCompositeBlock

open AmortizedInitialization
open SpectralPolynomialAcceleration

noncomputable section

variable {State : Type*}

/-- Whether a complete candidate block meets the endpoint energy gate. -/
def EndpointAccepted
    (energy : State → ℝ) (tolerance : ℝ)
    (current candidate : State) : Prop :=
  energy candidate ≤ energy current + tolerance

/-- Propose the complete accelerated block; restart from the declared
baseline step when its endpoint fails the energy gate. -/
noncomputable def safeguardedBlock
    (energy : State → ℝ) (tolerance : ℝ)
    (baseline accelerated : State → State) (state : State) : State := by
  classical
  exact if EndpointAccepted energy tolerance state (accelerated state) then
      accelerated state
    else
      baseline state

@[simp] theorem safeguardedBlock_eq_accelerated
    (energy : State → ℝ) (tolerance : ℝ)
    (baseline accelerated : State → State) (state : State)
    (accepted : EndpointAccepted energy tolerance state (accelerated state)) :
    safeguardedBlock energy tolerance baseline accelerated state =
      accelerated state := by
  classical
  simp [safeguardedBlock, accepted]

@[simp] theorem safeguardedBlock_eq_baseline
    (energy : State → ℝ) (tolerance : ℝ)
    (baseline accelerated : State → State) (state : State)
    (rejected :
      ¬ EndpointAccepted energy tolerance state (accelerated state)) :
    safeguardedBlock energy tolerance baseline accelerated state =
      baseline state := by
  classical
  simp [safeguardedBlock, rejected]

/-- Endpoint monotonicity is unconditional when the baseline step satisfies
the same gate: the accelerated endpoint passes, or the baseline is used. -/
theorem safeguardedBlock_energy_le
    (energy : State → ℝ) (tolerance : ℝ)
    (baseline accelerated : State → State) (state : State)
    (baselineAccepted :
      energy (baseline state) ≤ energy state + tolerance) :
    energy (safeguardedBlock energy tolerance baseline accelerated state) ≤
      energy state + tolerance := by
  classical
  by_cases accepted :
      EndpointAccepted energy tolerance state (accelerated state)
  · rw [safeguardedBlock_eq_accelerated _ _ _ _ _ accepted]
    exact accepted
  · rw [safeguardedBlock_eq_baseline _ _ _ _ _ accepted]
    exact baselineAccepted

variable [NormedAddCommGroup State]

/-- One-map convergence toward a declared common target.  This weaker
notion is stable under state-dependent selection even when global pairwise
contraction of the selector is unavailable. -/
structure TargetContractionCertificate
    (solver : State → State) (target : State) where
  factor : ℝ
  factor_nonneg : 0 ≤ factor
  factor_lt_one : factor < 1
  fixesTarget : solver target = target
  contractsToTarget : ∀ state,
    ‖solver state - target‖ ≤ factor * ‖state - target‖

/-- A global contraction with a fixed point supplies a target contraction. -/
def TargetContractionCertificate.ofContraction
    {solver : State → State} (certificate : ContractionCertificate solver)
    (target : State) (fixed : IsFixedPoint solver target) :
    TargetContractionCertificate solver target where
  factor := certificate.factor
  factor_nonneg := certificate.factor_nonneg
  factor_lt_one := certificate.factor_lt_one
  fixesTarget := fixed
  contractsToTarget := fun state => by
    have hfixed : solver target = target := fixed
    simpa only [hfixed] using certificate.contracts state target

/-- Selecting between two maps that contract toward the same target keeps the
worse target-contraction factor. -/
noncomputable def safeguardedTargetCertificate
    (energy : State → ℝ) (tolerance : ℝ)
    {baseline accelerated : State → State} {target : State}
    (baselineCertificate :
      TargetContractionCertificate baseline target)
    (acceleratedCertificate :
      TargetContractionCertificate accelerated target) :
    TargetContractionCertificate
      (safeguardedBlock energy tolerance baseline accelerated) target where
  factor := max baselineCertificate.factor acceleratedCertificate.factor
  factor_nonneg :=
    le_trans baselineCertificate.factor_nonneg
      (le_max_left _ _)
  factor_lt_one :=
    max_lt baselineCertificate.factor_lt_one
      acceleratedCertificate.factor_lt_one
  fixesTarget := by
    classical
    have hbaseline : baseline target = target :=
      baselineCertificate.fixesTarget
    have hacclerated : accelerated target = target :=
      acceleratedCertificate.fixesTarget
    unfold safeguardedBlock
    rw [hbaseline, hacclerated]
    split <;> rfl
  contractsToTarget := fun state => by
    by_cases accepted :
        EndpointAccepted energy tolerance state (accelerated state)
    · rw [safeguardedBlock_eq_accelerated _ _ _ _ _ accepted]
      calc
        ‖accelerated state - target‖ ≤
            acceleratedCertificate.factor * ‖state - target‖ :=
          acceleratedCertificate.contractsToTarget state
        _ ≤ max baselineCertificate.factor acceleratedCertificate.factor *
              ‖state - target‖ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
    · rw [safeguardedBlock_eq_baseline _ _ _ _ _ accepted]
      calc
        ‖baseline state - target‖ ≤
            baselineCertificate.factor * ‖state - target‖ :=
          baselineCertificate.contractsToTarget state
        _ ≤ max baselineCertificate.factor acceleratedCertificate.factor *
              ‖state - target‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

/-- Repeated safeguarded composite blocks converge geometrically to their
common target under the target-contraction certificate. -/
theorem TargetContractionCertificate.iterate_to_target_le
    {solver : State → State} {target initial : State}
    (certificate : TargetContractionCertificate solver target)
    (steps : ℕ) :
    ‖solver^[steps] initial - target‖ ≤
      certificate.factor ^ steps * ‖initial - target‖ := by
  induction steps with
  | zero => simp
  | succ steps inductionHypothesis =>
      rw [Function.iterate_succ_apply', pow_succ]
      calc
        ‖solver (solver^[steps] initial) - target‖ ≤
            certificate.factor * ‖solver^[steps] initial - target‖ :=
          certificate.contractsToTarget _
        _ ≤ certificate.factor *
              (certificate.factor ^ steps * ‖initial - target‖) :=
          mul_le_mul_of_nonneg_left inductionHypothesis
            certificate.factor_nonneg
        _ = certificate.factor ^ steps * certificate.factor *
              ‖initial - target‖ := by ring

/-! ## The internally expansive `[1,9]` block -/

/-- Scalar quadratic energy for the high-curvature endpoint mode. -/
noncomputable def highModeEnergy (state : ℝ) : ℝ :=
  (9 / 2) * state ^ 2

/-- First sweep of the registered `[1,9]` schedule on curvature nine. -/
noncomputable def highModeFirstSweep (state : ℝ) : ℝ :=
  (1 - firstRate 1 9 * 9) * state

/-- Complete two-sweep block on the same mode. -/
noncomputable def highModeCompositeBlock (state : ℝ) : ℝ :=
  twoRateFactor 1 9 9 * state

/-- The first internal sweep strictly raises energy away from the target. -/
theorem highMode_firstSweep_energy_expands
    {state : ℝ} (hstate : state ≠ 0) :
    highModeEnergy state < highModeEnergy (highModeFirstSweep state) := by
  have hsquare : 0 < state ^ 2 := sq_pos_of_ne_zero hstate
  norm_num [highModeEnergy, highModeFirstSweep, firstRate]
  nlinarith

/-- The complete two-sweep endpoint lowers or preserves energy. -/
theorem highMode_composite_energy_le (state : ℝ) :
    highModeEnergy (highModeCompositeBlock state) ≤ highModeEnergy state := by
  have hsquare : 0 ≤ state ^ 2 := sq_nonneg state
  norm_num [highModeEnergy, highModeCompositeBlock, twoRateFactor,
    firstRate, secondRate]
  nlinarith

/-- Block-level safeguarding admits the certified two-sweep endpoint despite
the internally expansive first sweep. -/
theorem highMode_safeguard_accepts_composite :
    safeguardedBlock highModeEnergy 0 (fun _state : ℝ => 0)
        highModeCompositeBlock =
      highModeCompositeBlock := by
  funext state
  rw [safeguardedBlock_eq_accelerated]
  simpa [EndpointAccepted] using highMode_composite_energy_le state

/-- Negative fixture: an expansive complete proposal is rejected and the
baseline step is selected. -/
theorem expansiveEndpoint_restarts_to_baseline :
    safeguardedBlock (fun state : ℝ => state ^ 2) 0
        (fun state => state / 2) (fun state => 2 * state) 1 =
      (1 / 2 : ℝ) := by
  have rejected :
      ¬ EndpointAccepted (fun state : ℝ => state ^ 2) 0 1 (2 * 1) := by
    norm_num [EndpointAccepted]
  rw [safeguardedBlock_eq_baseline _ _ _ _ _ rejected]

#print axioms safeguardedBlock_energy_le
#print axioms TargetContractionCertificate.ofContraction
#print axioms safeguardedTargetCertificate
#print axioms TargetContractionCertificate.iterate_to_target_le
#print axioms highMode_firstSweep_energy_expands
#print axioms highMode_composite_energy_le
#print axioms highMode_safeguard_accepts_composite
#print axioms expansiveEndpoint_restarts_to_baseline

end

end SafeguardedCompositeBlock

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
