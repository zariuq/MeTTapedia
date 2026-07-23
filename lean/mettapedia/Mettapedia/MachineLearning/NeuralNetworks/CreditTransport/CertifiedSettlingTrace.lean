import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.WorkNormalizedTruncation

/-!
# Proof-carrying traces for finite predictive settling

The scalar fields emitted by a solver do not certify themselves.  This module
separates a mathematical context that owns contraction, fixed-point, and
readout-sensitivity facts from a per-sweep observation whose derived fields can
be reconstructed mechanically.  The resulting theorem turns a reconstructible
row into raw-credit alignment and finite task descent without identifying the
row with an optimizer displacement.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace CertifiedSettlingTrace

open scoped InnerProductSpace
open AmortizedInitialization
open AmortizedCreditReadout
open DirectionalTaskDescent
open WorkNormalizedTruncation

variable {State Credit : Type*}
  [NormedAddCommGroup State]
  [NormedAddCommGroup Credit] [InnerProductSpace ℝ Credit]

/-- Mathematical assumptions shared by all rows of one settling trace.  These
are proved or source-bound separately; recording their numeric values in a row
does not establish them. -/
structure CertificateContext
    (solver : State → State) (readout : State → Credit) where
  contraction : ContractionCertificate solver
  target : State
  targetFixed : IsFixedPoint solver target
  exactCredit : Credit
  readoutSensitivity : ℝ
  readoutSensitivity_nonneg : 0 ≤ readoutSensitivity
  readoutLipschitz :
    CreditReadoutLipschitzAt readout target readoutSensitivity
  equilibriumMismatch : ℝ
  equilibriumMismatch_nonneg : 0 ≤ equilibriumMismatch
  equilibriumMismatch_bound :
    ‖readout target - exactCredit‖ ≤ equilibriumMismatch
  step : ℝ
  step_pos : 0 < step
  curvature : ℝ
  fixedCost : ℕ
  sweepCost : ℕ
  referenceDepth : ℕ

/-- One artifact row.  State and credit values may be represented externally
by content-addressed tensors; the scalar fields are the quantities that a
checker reconstructs from them. -/
structure SweepObservation (State Credit : Type*) where
  depth : ℕ
  state : State
  energy : ℝ
  finiteCredit : Credit
  solverResidual : ℝ
  finiteCreditNorm : ℝ
  certifiedErrorRadius : ℝ
  alignmentLowerBound : ℝ
  taskDecreaseLowerBound : ℝ
  cumulativeWork : ℕ
  elapsedNanoseconds : ℕ
  referenceCredit : Credit
  referenceCreditGap : ℝ

/-- Every derived field in one row agrees with the declared solver, readout,
certificate context, and longer fixed-depth reference. -/
structure Reconstructible
    {solver : State → State} {readout : State → Credit}
    (context : CertificateContext solver readout)
    (observation : SweepObservation State Credit) : Prop where
  depth_lt_reference : observation.depth < context.referenceDepth
  finiteCredit_eq : observation.finiteCredit = readout observation.state
  solverResidual_eq :
    observation.solverResidual = ‖observation.state - solver observation.state‖
  finiteCreditNorm_eq :
    observation.finiteCreditNorm = ‖observation.finiteCredit‖
  certifiedErrorRadius_eq :
    observation.certifiedErrorRadius =
      context.readoutSensitivity *
          (observation.solverResidual /
            (1 - context.contraction.factor)) +
        context.equilibriumMismatch
  alignmentLowerBound_eq :
    observation.alignmentLowerBound =
      observation.finiteCreditNorm *
        (observation.finiteCreditNorm - observation.certifiedErrorRadius)
  taskDecreaseLowerBound_eq :
    observation.taskDecreaseLowerBound =
      directionalDecreaseLower context.step observation.alignmentLowerBound
        context.curvature
  cumulativeWork_eq :
    observation.cumulativeWork =
      settlingWork context.fixedCost context.sweepCost observation.depth
  referenceCreditGap_eq :
    observation.referenceCreditGap =
      ‖observation.finiteCredit - observation.referenceCredit‖

omit [InnerProductSpace ℝ Credit] in
/-- A reconstructible row carries a sound raw-credit error radius. -/
theorem Reconstructible.creditError_le
    {solver : State → State} {readout : State → Credit}
    {context : CertificateContext solver readout}
    {observation : SweepObservation State Credit}
    (reconstructible : Reconstructible context observation) :
    ‖observation.finiteCredit - context.exactCredit‖ ≤
      observation.certifiedErrorRadius := by
  have hbase := creditError_le_residual_plus_equilibriumMismatch
    context.contraction context.target observation.state context.targetFixed
    readout context.exactCredit context.readoutSensitivity
    context.readoutSensitivity_nonneg context.readoutLipschitz
  calc
    ‖observation.finiteCredit - context.exactCredit‖ =
        ‖readout observation.state - context.exactCredit‖ := by
      rw [reconstructible.finiteCredit_eq]
    _ ≤ context.readoutSensitivity *
          (‖observation.state - solver observation.state‖ /
            (1 - context.contraction.factor)) +
          ‖readout context.target - context.exactCredit‖ := hbase
    _ ≤ context.readoutSensitivity *
          (observation.solverResidual /
            (1 - context.contraction.factor)) +
          context.equilibriumMismatch := by
      rw [reconstructible.solverResidual_eq]
      simpa [add_comm] using
        add_le_add_right context.equilibriumMismatch_bound
          (context.readoutSensitivity *
            (‖observation.state - solver observation.state‖ /
              (1 - context.contraction.factor)))
    _ = observation.certifiedErrorRadius :=
      reconstructible.certifiedErrorRadius_eq.symm

/-- The row's observable radius-to-norm gate certifies positive alignment. -/
theorem Reconstructible.positiveAlignment
    {solver : State → State} {readout : State → Credit}
    {context : CertificateContext solver readout}
    {observation : SweepObservation State Credit}
    (reconstructible : Reconstructible context observation)
    (hrelative :
      observation.certifiedErrorRadius < observation.finiteCreditNorm) :
    0 < ⟪context.exactCredit, observation.finiteCredit⟫_ℝ := by
  apply finiteCredit_positiveAlignment context.exactCredit
    observation.finiteCredit observation.certifiedErrorRadius
    reconstructible.creditError_le
  simpa [reconstructible.finiteCreditNorm_eq] using hrelative

/-- A positive reconstructed task margin licenses a finite raw-credit task
step under the separately supplied directional upper model. -/
theorem Reconstructible.strictTaskDescent
    {solver : State → State} {readout : State → Credit}
    {context : CertificateContext solver readout}
    {observation : SweepObservation State Credit}
    {loss : Credit → ℝ} {parameter : Credit}
    (reconstructible : Reconstructible context observation)
    (certificate : HasDirectionalTaskUpperModelAt loss parameter
      context.exactCredit observation.finiteCredit context.curvature)
    (hmargin : 0 < observation.taskDecreaseLowerBound) :
    loss (parameter - context.step • observation.finiteCredit) <
      loss parameter := by
  have hmarginReconstructed :
      0 < directionalDecreaseLower context.step
        observation.alignmentLowerBound context.curvature := by
    rw [← reconstructible.taskDecreaseLowerBound_eq]
    exact hmargin
  have hmarginFormula :
      0 < context.step * observation.alignmentLowerBound -
        context.step ^ 2 * context.curvature / 2 := by
    simpa [directionalDecreaseLower] using hmarginReconstructed
  have htrustObserved :
      context.step * context.curvature / 2 <
        observation.alignmentLowerBound := by
    nlinarith [context.step_pos]
  have htrust :
      context.step * context.curvature / 2 <
        ‖observation.finiteCredit‖ *
          (‖observation.finiteCredit‖ - observation.certifiedErrorRadius) := by
    rw [← reconstructible.finiteCreditNorm_eq,
      ← reconstructible.alignmentLowerBound_eq]
    exact htrustObserved
  exact finiteCredit_strictTaskDescent certificate
    reconstructible.creditError_le context.step_pos htrust

/-- Energy values must be nonincreasing in observation order. -/
def NonincreasingEnergy : List ℝ → Prop
  | [] => True
  | [_] => True
  | first :: second :: rest =>
      second ≤ first ∧ NonincreasingEnergy (second :: rest)

/-- A complete trace requires contiguous one-based depths and monotone energy.
Each row is checked separately against one shared certificate context. -/
structure Trace
    {solver : State → State} {readout : State → Credit}
    (context : CertificateContext solver readout) where
  initialEnergy : ℝ
  sweeps : List (SweepObservation State Credit)
  depths_contiguous :
    sweeps.map SweepObservation.depth =
      (List.range sweeps.length).map Nat.succ
  energies_nonincreasing :
    NonincreasingEnergy (initialEnergy :: sweeps.map SweepObservation.energy)
  reconstructible : ∀ observation ∈ sweeps,
    Reconstructible context observation

/-! ## Exact positive and negative fixtures -/

noncomputable def shiftedReadout (state : ℝ) : ℝ := state + 2

theorem shiftedReadout_lipschitzAt_zero :
    CreditReadoutLipschitzAt shiftedReadout 0 1 := by
  intro state
  simp [shiftedReadout, Real.norm_eq_abs]

noncomputable def positiveContext :
    CertificateContext halfSolver shiftedReadout where
  contraction := halfSolverCertificate
  target := 0
  targetFixed := halfSolver_zero_fixed
  exactCredit := 2
  readoutSensitivity := 1
  readoutSensitivity_nonneg := by norm_num
  readoutLipschitz := shiftedReadout_lipschitzAt_zero
  equilibriumMismatch := 0
  equilibriumMismatch_nonneg := by norm_num
  equilibriumMismatch_bound := by norm_num [shiftedReadout]
  step := 1 / 4
  step_pos := by norm_num
  curvature := 1
  fixedCost := 10
  sweepCost := 3
  referenceDepth := 2

noncomputable def positiveObservation : SweepObservation ℝ ℝ where
  depth := 1
  state := 1 / 2
  energy := 1
  finiteCredit := 5 / 2
  solverResidual := 1 / 4
  finiteCreditNorm := 5 / 2
  certifiedErrorRadius := 1 / 2
  alignmentLowerBound := 5
  taskDecreaseLowerBound := 39 / 32
  cumulativeWork := 13
  elapsedNanoseconds := 100
  referenceCredit := 9 / 4
  referenceCreditGap := 1 / 4

theorem positiveObservation_reconstructible :
    Reconstructible positiveContext positiveObservation := by
  constructor <;>
    norm_num [positiveContext, positiveObservation, shiftedReadout,
      halfSolver, halfSolverCertificate, directionalDecreaseLower,
      settlingWork, Real.norm_eq_abs]

theorem positiveObservation_alignment :
    0 < ⟪positiveContext.exactCredit,
      positiveObservation.finiteCredit⟫_ℝ := by
  apply positiveObservation_reconstructible.positiveAlignment
  norm_num [positiveContext, positiveObservation]

noncomputable def understatedErrorObservation : SweepObservation ℝ ℝ :=
  { positiveObservation with certifiedErrorRadius := 0 }

/-- A row cannot obtain a certificate by merely reporting a smaller radius. -/
theorem understatedErrorObservation_not_reconstructible :
    ¬ Reconstructible positiveContext understatedErrorObservation := by
  intro claimed
  have equality := claimed.certifiedErrorRadius_eq
  norm_num [positiveContext, understatedErrorObservation, positiveObservation,
    halfSolverCertificate] at equality

noncomputable def risingEnergyObservation : SweepObservation ℝ ℝ :=
  { positiveObservation with depth := 2, energy := 2 }

/-- An increasing accepted-energy trace is rejected independently of its
per-row scalar formulas. -/
theorem risingEnergyTrace_not_monotone :
    ¬ NonincreasingEnergy
      [2, positiveObservation.energy, risingEnergyObservation.energy] := by
  norm_num [NonincreasingEnergy, positiveObservation,
    risingEnergyObservation]

#print axioms Reconstructible.creditError_le
#print axioms Reconstructible.positiveAlignment
#print axioms Reconstructible.strictTaskDescent
#print axioms positiveObservation_reconstructible
#print axioms positiveObservation_alignment
#print axioms understatedErrorObservation_not_reconstructible
#print axioms risingEnergyTrace_not_monotone

end CertifiedSettlingTrace

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
