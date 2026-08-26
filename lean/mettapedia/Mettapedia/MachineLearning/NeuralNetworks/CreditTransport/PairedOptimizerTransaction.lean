import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RealizedDisplacementAdmission

/-!
# Paired realized BP/PC optimizer transactions

The generic rollback construction in `RealizedDisplacementAdmission` is useful
when rejection means a no-op.  The action-memory treatment has a different
contract: BP and PC trials are both computed from one immutable full snapshot;
an admitted PC trial is committed, while every ordinary PC rejection commits
the paired BP trial.  A no-op is reserved for an explicit skip or failure of
the BP transaction itself.

The optimizer consumes the complete parameter-and-state snapshot.  This is
essential for momentum, adaptive moments, and parameter-dependent decoupled
regularization.  Admission compares the two *realized displacements*, never
the proposed gradient vectors.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
namespace PairedOptimizerTransaction

noncomputable section

open scoped InnerProductSpace
open RealizedDisplacementAdmission

attribute [local instance] Classical.propDecidable

universe uP uS uG

/-! ## Full-snapshot optimizer and exact realized displacement -/

/-- A pure optimizer trial.  Failure is explicit, and the complete current
parameter is part of the optimizer input rather than hidden inside its state. -/
structure FullOptimizerTransform
    (Parameter : Type uP) (OptimizerState : Type uS) (Gradient : Type uG) where
  apply : OptimizerSnapshot Parameter OptimizerState → Gradient →
    Option (OptimizerSnapshot Parameter OptimizerState)

/-- A computational validator related to its logical meaning.  This is the
boundary at which nonfinite parameters or optimizer state must be rejected. -/
structure SnapshotValidator
    (Parameter : Type uP) (OptimizerState : Type uS) where
  Valid : OptimizerSnapshot Parameter OptimizerState → Prop
  accepts : OptimizerSnapshot Parameter OptimizerState → Bool
  accepts_iff : ∀ snapshot, accepts snapshot = true ↔ Valid snapshot

def snapshotDisplacement
    {Parameter : Type uP} {OptimizerState : Type uS} [Sub Parameter]
    (before after : OptimizerSnapshot Parameter OptimizerState) : Parameter :=
  before.parameter - after.parameter

/-- BP and PC candidates are definitionally trials from the same immutable
snapshot. -/
structure PairedCandidates
    (Parameter : Type uP) (OptimizerState : Type uS) where
  before : OptimizerSnapshot Parameter OptimizerState
  bp : OptimizerSnapshot Parameter OptimizerState
  pc : OptimizerSnapshot Parameter OptimizerState

def buildPairedCandidates
    {Parameter : Type uP} {OptimizerState : Type uS} {Gradient : Type uG}
    (optimizer : FullOptimizerTransform Parameter OptimizerState Gradient)
    (bpGradient pcGradient : Gradient)
    (before : OptimizerSnapshot Parameter OptimizerState) :
    Option (PairedCandidates Parameter OptimizerState) := do
  let bp ← optimizer.apply before bpGradient
  let pc ← optimizer.apply before pcGradient
  pure { before, bp, pc }

theorem buildPairedCandidates_uses_same_before
    {Parameter : Type uP} {OptimizerState : Type uS} {Gradient : Type uG}
    (optimizer : FullOptimizerTransform Parameter OptimizerState Gradient)
    (bpGradient pcGradient : Gradient)
    (before bp pc : OptimizerSnapshot Parameter OptimizerState)
    (bpTrial : optimizer.apply before bpGradient = some bp)
    (pcTrial : optimizer.apply before pcGradient = some pc) :
    buildPairedCandidates optimizer bpGradient pcGradient before =
      some { before := before, bp := bp, pc := pc } := by
  simp [buildPairedCandidates, bpTrial, pcTrial]

/-! ## Work charged at every attempted stage -/

structure PairedCostSchedule where
  bpTrial : ℕ
  settling : ℕ
  pcTrial : ℕ
  measurement : ℕ
deriving DecidableEq

structure PairedWorkLedger where
  bpTrial : ℕ
  settling : ℕ
  pcTrial : ℕ
  measurement : ℕ
  rejectedWork : ℕ
deriving DecidableEq

def PairedWorkLedger.total (work : PairedWorkLedger) : ℕ :=
  work.bpTrial + work.settling + work.pcTrial + work.measurement

def zeroWork : PairedWorkLedger := ⟨0, 0, 0, 0, 0⟩

def bpFailureWork (cost : PairedCostSchedule) : PairedWorkLedger :=
  ⟨cost.bpTrial, 0, 0, 0, 0⟩

def solverFailureWork (cost : PairedCostSchedule) : PairedWorkLedger :=
  ⟨cost.bpTrial, cost.settling, 0, 0, cost.settling⟩

def pcTrialFailureWork (cost : PairedCostSchedule) : PairedWorkLedger :=
  ⟨cost.bpTrial, cost.settling, cost.pcTrial, 0,
    cost.settling + cost.pcTrial⟩

def measuredWork (cost : PairedCostSchedule) (rejected : Bool) :
    PairedWorkLedger :=
  ⟨cost.bpTrial, cost.settling, cost.pcTrial, cost.measurement,
    if rejected then cost.settling + cost.pcTrial + cost.measurement else 0⟩

@[simp] theorem measuredWork_total (cost : PairedCostSchedule) (rejected : Bool) :
    (measuredWork cost rejected).total =
      cost.bpTrial + cost.settling + cost.pcTrial + cost.measurement := rfl

theorem rejected_measurement_charges_all_attempted_work
    (cost : PairedCostSchedule) :
    (measuredWork cost true).rejectedWork =
      cost.settling + cost.pcTrial + cost.measurement := rfl

/-! ## Admission of the exact PC candidate against the paired BP candidate -/

/-- The reference displacement is not an input field: it is definitionally
the displacement of the BP candidate built from the same snapshot. -/
structure PairedRealizedAdmission
    (Parameter : Type uP) (OptimizerState : Type uS)
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    (loss : Parameter → ℝ)
    (validSnapshot : OptimizerSnapshot Parameter OptimizerState → Prop)
    (cost : PairedCostSchedule)
    (before bpCandidate pcCandidate :
      OptimizerSnapshot Parameter OptimizerState) where
  bpValid : validSnapshot bpCandidate
  pcValid : validSnapshot pcCandidate
  geometry : DirectionScaleGate Parameter
    (snapshotDisplacement before bpCandidate)
    (snapshotDisplacement before pcCandidate)
  minimumDecrease : ℝ
  minimumDecrease_pos : 0 < minimumDecrease
  observedDecrease :
    minimumDecrease ≤ loss before.parameter - loss pcCandidate.parameter
  chargedWork : PairedWorkLedger
  chargedWork_eq : chargedWork = measuredWork cost false

theorem PairedRealizedAdmission.strictTaskDescent
    {Parameter : Type uP} {OptimizerState : Type uS}
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    {loss : Parameter → ℝ}
    {validSnapshot : OptimizerSnapshot Parameter OptimizerState → Prop}
    {cost : PairedCostSchedule}
    {before bpCandidate pcCandidate :
      OptimizerSnapshot Parameter OptimizerState}
    (admission : PairedRealizedAdmission Parameter OptimizerState loss
      validSnapshot cost before bpCandidate pcCandidate) :
    loss pcCandidate.parameter < loss before.parameter := by
  linarith [admission.minimumDecrease_pos, admission.observedDecrease]

theorem PairedRealizedAdmission.reference_is_paired_bp_displacement
    {Parameter : Type uP} {OptimizerState : Type uS}
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    {loss : Parameter → ℝ}
    {validSnapshot : OptimizerSnapshot Parameter OptimizerState → Prop}
    {cost : PairedCostSchedule}
    {before bpCandidate pcCandidate :
      OptimizerSnapshot Parameter OptimizerState}
    (admission : PairedRealizedAdmission Parameter OptimizerState loss
      validSnapshot cost before bpCandidate pcCandidate) :
    Nonempty (DirectionScaleGate Parameter
      (snapshotDisplacement before bpCandidate)
      (snapshotDisplacement before pcCandidate)) :=
  ⟨admission.geometry⟩

/-! ## Exact branch policy -/

inductive TransactionOutcome where
  | skipped
  | pcCommitted
  | bpFallback
  | transactionFailed
deriving DecidableEq

structure TransactionResult
    (Parameter : Type uP) (OptimizerState : Type uS) where
  snapshot : OptimizerSnapshot Parameter OptimizerState
  outcome : TransactionOutcome
  work : PairedWorkLedger

/-- Complete paired policy.  `pcGradient = none` denotes solver rejection.
The admission callback receives candidates already constructed from `before`.
-/
def pairedTransaction
    {Parameter : Type uP} {OptimizerState : Type uS} {Gradient : Type uG}
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    (optimizer : FullOptimizerTransform Parameter OptimizerState Gradient)
    (loss : Parameter → ℝ)
    (validator : SnapshotValidator Parameter OptimizerState)
    (cost : PairedCostSchedule)
    (skip : Bool)
    (bpGradient : Gradient) (pcGradient : Option Gradient)
    (admission : (before bpCandidate pcCandidate :
        OptimizerSnapshot Parameter OptimizerState) →
      Option (PairedRealizedAdmission Parameter OptimizerState loss
        validator.Valid cost before bpCandidate pcCandidate))
    (before : OptimizerSnapshot Parameter OptimizerState) :
    TransactionResult Parameter OptimizerState :=
  if skip then
    ⟨before, .skipped, zeroWork⟩
  else
    match optimizer.apply before bpGradient with
    | none => ⟨before, .transactionFailed, bpFailureWork cost⟩
    | some bpCandidate =>
        if validator.accepts bpCandidate then
          match pcGradient with
          | none => ⟨bpCandidate, .bpFallback, solverFailureWork cost⟩
          | some proposedPC =>
              match optimizer.apply before proposedPC with
              | none => ⟨bpCandidate, .bpFallback, pcTrialFailureWork cost⟩
              | some pcCandidate =>
                  if validator.accepts pcCandidate then
                    match admission before bpCandidate pcCandidate with
                    | some _ => ⟨pcCandidate, .pcCommitted, measuredWork cost false⟩
                    | none => ⟨bpCandidate, .bpFallback, measuredWork cost true⟩
                  else ⟨bpCandidate, .bpFallback, pcTrialFailureWork cost⟩
        else ⟨before, .transactionFailed, bpFailureWork cost⟩

theorem explicit_skip_is_exact_identity
    {Parameter : Type uP} {OptimizerState : Type uS} {Gradient : Type uG}
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    (optimizer : FullOptimizerTransform Parameter OptimizerState Gradient)
    (loss : Parameter → ℝ)
    (validator : SnapshotValidator Parameter OptimizerState)
    (cost : PairedCostSchedule) (bpGradient : Gradient)
    (pcGradient : Option Gradient)
    (admission : (before bpCandidate pcCandidate :
        OptimizerSnapshot Parameter OptimizerState) →
      Option (PairedRealizedAdmission Parameter OptimizerState loss
        validator.Valid cost before bpCandidate pcCandidate))
    (before : OptimizerSnapshot Parameter OptimizerState) :
    pairedTransaction optimizer loss validator cost true bpGradient pcGradient
      admission before = ⟨before, .skipped, zeroWork⟩ := by
  simp [pairedTransaction]

theorem bp_trial_failure_is_exact_identity
    {Parameter : Type uP} {OptimizerState : Type uS} {Gradient : Type uG}
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    (optimizer : FullOptimizerTransform Parameter OptimizerState Gradient)
    (loss : Parameter → ℝ)
    (validator : SnapshotValidator Parameter OptimizerState)
    (cost : PairedCostSchedule) (bpGradient : Gradient)
    (pcGradient : Option Gradient)
    (admission : (before bpCandidate pcCandidate :
        OptimizerSnapshot Parameter OptimizerState) →
      Option (PairedRealizedAdmission Parameter OptimizerState loss
        validator.Valid cost before bpCandidate pcCandidate))
    (before : OptimizerSnapshot Parameter OptimizerState)
    (failed : optimizer.apply before bpGradient = none) :
    pairedTransaction optimizer loss validator cost false bpGradient pcGradient
      admission before = ⟨before, .transactionFailed, bpFailureWork cost⟩ := by
  simp [pairedTransaction, failed]

theorem bp_validation_failure_is_exact_identity
    {Parameter : Type uP} {OptimizerState : Type uS} {Gradient : Type uG}
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    (optimizer : FullOptimizerTransform Parameter OptimizerState Gradient)
    (loss : Parameter → ℝ)
    (validator : SnapshotValidator Parameter OptimizerState)
    (cost : PairedCostSchedule) (bpGradient : Gradient)
    (pcGradient : Option Gradient)
    (admission : (before bpCandidate pcCandidate :
        OptimizerSnapshot Parameter OptimizerState) →
      Option (PairedRealizedAdmission Parameter OptimizerState loss
        validator.Valid cost before bpCandidate pcCandidate))
    (before bpCandidate : OptimizerSnapshot Parameter OptimizerState)
    (bpTrial : optimizer.apply before bpGradient = some bpCandidate)
    (invalid : validator.accepts bpCandidate = false) :
    pairedTransaction optimizer loss validator cost false bpGradient pcGradient
      admission before = ⟨before, .transactionFailed, bpFailureWork cost⟩ := by
  simp [pairedTransaction, bpTrial, invalid]

theorem solver_rejection_commits_exact_bp_candidate
    {Parameter : Type uP} {OptimizerState : Type uS} {Gradient : Type uG}
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    (optimizer : FullOptimizerTransform Parameter OptimizerState Gradient)
    (loss : Parameter → ℝ)
    (validator : SnapshotValidator Parameter OptimizerState)
    (cost : PairedCostSchedule) (bpGradient : Gradient)
    (admission : (before bpCandidate pcCandidate :
        OptimizerSnapshot Parameter OptimizerState) →
      Option (PairedRealizedAdmission Parameter OptimizerState loss
        validator.Valid cost before bpCandidate pcCandidate))
    (before bpCandidate : OptimizerSnapshot Parameter OptimizerState)
    (bpTrial : optimizer.apply before bpGradient = some bpCandidate)
    (bpValid : validator.accepts bpCandidate = true) :
    pairedTransaction optimizer loss validator cost false bpGradient none
      admission before = ⟨bpCandidate, .bpFallback, solverFailureWork cost⟩ := by
  simp [pairedTransaction, bpTrial, bpValid]

theorem pc_trial_failure_commits_exact_bp_candidate
    {Parameter : Type uP} {OptimizerState : Type uS} {Gradient : Type uG}
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    (optimizer : FullOptimizerTransform Parameter OptimizerState Gradient)
    (loss : Parameter → ℝ)
    (validator : SnapshotValidator Parameter OptimizerState)
    (cost : PairedCostSchedule) (bpGradient pcGradient : Gradient)
    (admission : (before bpCandidate pcCandidate :
        OptimizerSnapshot Parameter OptimizerState) →
      Option (PairedRealizedAdmission Parameter OptimizerState loss
        validator.Valid cost before bpCandidate pcCandidate))
    (before bpCandidate : OptimizerSnapshot Parameter OptimizerState)
    (bpTrial : optimizer.apply before bpGradient = some bpCandidate)
    (bpValid : validator.accepts bpCandidate = true)
    (pcFailed : optimizer.apply before pcGradient = none) :
    pairedTransaction optimizer loss validator cost false bpGradient
      (some pcGradient) admission before =
        ⟨bpCandidate, .bpFallback, pcTrialFailureWork cost⟩ := by
  simp [pairedTransaction, bpTrial, bpValid, pcFailed]

theorem pc_validation_failure_commits_exact_bp_candidate
    {Parameter : Type uP} {OptimizerState : Type uS} {Gradient : Type uG}
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    (optimizer : FullOptimizerTransform Parameter OptimizerState Gradient)
    (loss : Parameter → ℝ)
    (validator : SnapshotValidator Parameter OptimizerState)
    (cost : PairedCostSchedule) (bpGradient pcGradient : Gradient)
    (admission : (before bpCandidate pcCandidate :
        OptimizerSnapshot Parameter OptimizerState) →
      Option (PairedRealizedAdmission Parameter OptimizerState loss
        validator.Valid cost before bpCandidate pcCandidate))
    (before bpCandidate pcCandidate :
      OptimizerSnapshot Parameter OptimizerState)
    (bpTrial : optimizer.apply before bpGradient = some bpCandidate)
    (bpValid : validator.accepts bpCandidate = true)
    (pcTrial : optimizer.apply before pcGradient = some pcCandidate)
    (pcInvalid : validator.accepts pcCandidate = false) :
    pairedTransaction optimizer loss validator cost false bpGradient
      (some pcGradient) admission before =
        ⟨bpCandidate, .bpFallback, pcTrialFailureWork cost⟩ := by
  simp [pairedTransaction, bpTrial, bpValid, pcTrial, pcInvalid]

theorem committed_bp_candidate_is_valid
    {Parameter : Type uP} {OptimizerState : Type uS}
    (validator : SnapshotValidator Parameter OptimizerState)
    (bpCandidate : OptimizerSnapshot Parameter OptimizerState)
    (accepted : validator.accepts bpCandidate = true) :
    validator.Valid bpCandidate :=
  (validator.accepts_iff bpCandidate).1 accepted

theorem measurement_rejection_commits_exact_bp_candidate
    {Parameter : Type uP} {OptimizerState : Type uS} {Gradient : Type uG}
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    (optimizer : FullOptimizerTransform Parameter OptimizerState Gradient)
    (loss : Parameter → ℝ)
    (validator : SnapshotValidator Parameter OptimizerState)
    (cost : PairedCostSchedule) (bpGradient pcGradient : Gradient)
    (admission : (before bpCandidate pcCandidate :
        OptimizerSnapshot Parameter OptimizerState) →
      Option (PairedRealizedAdmission Parameter OptimizerState loss
        validator.Valid cost before bpCandidate pcCandidate))
    (before bpCandidate pcCandidate :
      OptimizerSnapshot Parameter OptimizerState)
    (bpTrial : optimizer.apply before bpGradient = some bpCandidate)
    (pcTrial : optimizer.apply before pcGradient = some pcCandidate)
    (bpValid : validator.accepts bpCandidate = true)
    (pcValid : validator.accepts pcCandidate = true)
    (rejected : admission before bpCandidate pcCandidate = none) :
    pairedTransaction optimizer loss validator cost false bpGradient
      (some pcGradient) admission before =
        ⟨bpCandidate, .bpFallback, measuredWork cost true⟩ := by
  simp [pairedTransaction, bpTrial, bpValid, pcTrial, pcValid, rejected]

theorem admission_commits_exact_pc_candidate
    {Parameter : Type uP} {OptimizerState : Type uS} {Gradient : Type uG}
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    (optimizer : FullOptimizerTransform Parameter OptimizerState Gradient)
    (loss : Parameter → ℝ)
    (validator : SnapshotValidator Parameter OptimizerState)
    (cost : PairedCostSchedule) (bpGradient pcGradient : Gradient)
    (admission : (before bpCandidate pcCandidate :
        OptimizerSnapshot Parameter OptimizerState) →
      Option (PairedRealizedAdmission Parameter OptimizerState loss
        validator.Valid cost before bpCandidate pcCandidate))
    (before bpCandidate pcCandidate :
      OptimizerSnapshot Parameter OptimizerState)
    (certificate : PairedRealizedAdmission Parameter OptimizerState loss
      validator.Valid cost before bpCandidate pcCandidate)
    (bpTrial : optimizer.apply before bpGradient = some bpCandidate)
    (pcTrial : optimizer.apply before pcGradient = some pcCandidate)
    (admitted : admission before bpCandidate pcCandidate = some certificate) :
    pairedTransaction optimizer loss validator cost false bpGradient
      (some pcGradient) admission before =
        ⟨pcCandidate, .pcCommitted, measuredWork cost false⟩ := by
  have bpValid : validator.accepts bpCandidate = true :=
    (validator.accepts_iff bpCandidate).2 certificate.bpValid
  have pcValid : validator.accepts pcCandidate = true :=
    (validator.accepts_iff pcCandidate).2 certificate.pcValid
  simp [pairedTransaction, bpTrial, bpValid, pcTrial, pcValid, admitted]

theorem admitted_transaction_has_strict_task_descent
    {Parameter : Type uP} {OptimizerState : Type uS} {Gradient : Type uG}
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    (optimizer : FullOptimizerTransform Parameter OptimizerState Gradient)
    (loss : Parameter → ℝ)
    (validator : SnapshotValidator Parameter OptimizerState)
    (cost : PairedCostSchedule) (bpGradient pcGradient : Gradient)
    (admission : (before bpCandidate pcCandidate :
        OptimizerSnapshot Parameter OptimizerState) →
      Option (PairedRealizedAdmission Parameter OptimizerState loss
        validator.Valid cost before bpCandidate pcCandidate))
    (before bpCandidate pcCandidate :
      OptimizerSnapshot Parameter OptimizerState)
    (certificate : PairedRealizedAdmission Parameter OptimizerState loss
      validator.Valid cost before bpCandidate pcCandidate)
    (bpTrial : optimizer.apply before bpGradient = some bpCandidate)
    (pcTrial : optimizer.apply before pcGradient = some pcCandidate)
    (admitted : admission before bpCandidate pcCandidate = some certificate) :
    loss (pairedTransaction optimizer loss validator cost false bpGradient
      (some pcGradient) admission before).snapshot.parameter < loss before.parameter := by
  rw [admission_commits_exact_pc_candidate optimizer loss validator cost
    bpGradient pcGradient admission before bpCandidate pcCandidate certificate
    bpTrial pcTrial admitted]
  exact certificate.strictTaskDescent

/-! ## Stateful-optimizer negative and positive fixtures -/

abbrev Plane := RealizedDisplacementAdmission.FixturePlane

def statefulDiagonalOptimizer : FullOptimizerTransform Plane Plane Plane where
  apply := fun before gradient =>
    some {
      parameter := before.parameter -
        diagonalRescale (before.optimizerState 0) (before.optimizerState 1) gradient
      optimizerState := before.optimizerState }

def diagonalBefore : OptimizerSnapshot Plane Plane :=
  ⟨plane 0 0, plane 1 2⟩

def diagonalBPCandidate : OptimizerSnapshot Plane Plane :=
  ⟨diagonalBefore.parameter - diagonalRescale 1 2 rawReference,
    diagonalBefore.optimizerState⟩

def diagonalPCCandidate : OptimizerSnapshot Plane Plane :=
  ⟨diagonalBefore.parameter - diagonalRescale 1 2 rawCandidate,
    diagonalBefore.optimizerState⟩

@[simp] theorem diagonal_bp_trial :
    statefulDiagonalOptimizer.apply diagonalBefore rawReference =
      some diagonalBPCandidate := by
  rfl

@[simp] theorem diagonal_pc_trial :
    statefulDiagonalOptimizer.apply diagonalBefore rawCandidate =
      some diagonalPCCandidate := by
  rfl

theorem raw_gate_can_pass_while_paired_realized_direction_fails :
    (∃ gate : DirectionScaleGate Plane rawReference rawCandidate,
      gate.cosineFloor = 1 / 4) ∧
    ⟪snapshotDisplacement diagonalBefore diagonalBPCandidate,
      snapshotDisplacement diagonalBefore diagonalPCCandidate⟫_ℝ < 0 := by
  constructor
  · obtain ⟨gate, floor, _, _⟩ := raw_pair_passes_direction_and_scale
    exact ⟨gate, floor⟩
  · norm_num [statefulDiagonalOptimizer, diagonalBefore, snapshotDisplacement,
      diagonalBPCandidate, diagonalPCCandidate, realizedReference,
      realizedCandidate, rawReference, rawCandidate, diagonalRescale, plane, WithLp.equiv,
      PiLp.inner_apply, Fin.sum_univ_two]

/-- Parameter-dependent decoupled regularization cannot be represented by an
old interface whose input omits the parameter: the same gradient/state input
would have to return two different displacements. -/
theorem parameter_dependent_decay_needs_parameter_input :
    ¬ ∃ oldApply : ℝ → Unit → ℝ,
      oldApply 0 () = (1 : ℝ) ∧ oldApply 0 () = 2 := by
  rintro ⟨oldApply, first, second⟩
  linarith [first, second]

/-- A small stateful optimizer whose displacement includes the stored moment
and whose successor state accumulates the current gradient. -/
def momentumFixtureOptimizer : FullOptimizerTransform ℝ ℝ ℝ where
  apply := fun before gradient => some {
    parameter := before.parameter - (before.optimizerState + gradient)
    optimizerState := before.optimizerState + gradient }

def momentumBefore : OptimizerSnapshot ℝ ℝ := ⟨10, 0⟩

def clonedBPCandidate : OptimizerSnapshot ℝ ℝ := ⟨9, 1⟩
def mutatedByPCCandidate : OptimizerSnapshot ℝ ℝ := ⟨6, 4⟩
def contaminatedBPCandidate : OptimizerSnapshot ℝ ℝ := ⟨1, 5⟩

theorem mutating_pc_trial_before_bp_contaminates_fallback :
    momentumFixtureOptimizer.apply momentumBefore 1 = some clonedBPCandidate ∧
      momentumFixtureOptimizer.apply momentumBefore 4 =
        some mutatedByPCCandidate ∧
      momentumFixtureOptimizer.apply mutatedByPCCandidate 1 =
        some contaminatedBPCandidate ∧
      contaminatedBPCandidate ≠ clonedBPCandidate := by
  norm_num [momentumFixtureOptimizer, momentumBefore, clonedBPCandidate,
    mutatedByPCCandidate, contaminatedBPCandidate]

def nonzeroMomentBefore : OptimizerSnapshot ℝ ℝ := ⟨10, 3⟩
def zeroGradientMomentCandidate : OptimizerSnapshot ℝ ℝ := ⟨7, 3⟩

def momentumFixtureValidator : SnapshotValidator ℝ ℝ where
  Valid snapshot := snapshot = clonedBPCandidate ∨
    snapshot = mutatedByPCCandidate ∨ snapshot = contaminatedBPCandidate ∨
    snapshot = zeroGradientMomentCandidate
  accepts snapshot := decide (snapshot = clonedBPCandidate ∨
    snapshot = mutatedByPCCandidate ∨ snapshot = contaminatedBPCandidate ∨
    snapshot = zeroGradientMomentCandidate)
  accepts_iff snapshot := by simp

def bpOnlyMomentumValidator : SnapshotValidator ℝ ℝ where
  Valid snapshot := snapshot = clonedBPCandidate
  accepts snapshot := decide (snapshot = clonedBPCandidate)
  accepts_iff snapshot := by simp

theorem zero_gradient_can_move_but_explicit_skip_is_identity :
    momentumFixtureOptimizer.apply nonzeroMomentBefore 0 =
        some zeroGradientMomentCandidate ∧
      zeroGradientMomentCandidate.parameter = 7 ∧
      zeroGradientMomentCandidate ≠ nonzeroMomentBefore ∧
      (pairedTransaction momentumFixtureOptimizer (fun x => x ^ 2)
        momentumFixtureValidator
        ⟨1, 2, 3, 4⟩ true 0 (some 0)
        (fun _ _ _ => none) nonzeroMomentBefore).snapshot =
          nonzeroMomentBefore := by
  norm_num [momentumFixtureOptimizer, nonzeroMomentBefore,
    zeroGradientMomentCandidate, momentumFixtureValidator,
    pairedTransaction, zeroWork]

def worseningBPOptimizer : FullOptimizerTransform ℝ Unit ℝ where
  apply := fun before gradient => some
    ⟨before.parameter - gradient, before.optimizerState⟩

def scalarBefore : OptimizerSnapshot ℝ Unit := ⟨0, ()⟩
def scalarCost : PairedCostSchedule := ⟨1, 2, 3, 4⟩
def scalarBPCandidate : OptimizerSnapshot ℝ Unit := ⟨-1, ()⟩

def scalarFixtureValidator : SnapshotValidator ℝ Unit where
  Valid snapshot := snapshot = scalarBPCandidate
  accepts snapshot := decide (snapshot = scalarBPCandidate)
  accepts_iff snapshot := by simp

def scalarBeforeOnlyValidator : SnapshotValidator ℝ Unit where
  Valid snapshot := snapshot = scalarBefore
  accepts snapshot := decide (snapshot = scalarBefore)
  accepts_iff snapshot := by simp

/-- Exact BP fallback does not imply BP descent.  The transaction guarantees
identity with the declared fallback, not a task property absent a separate BP
certificate. -/
theorem exact_bp_fallback_need_not_descend :
    let result := pairedTransaction worseningBPOptimizer (fun x => x ^ 2)
      scalarFixtureValidator
      scalarCost false 1 none (fun _ _ _ => none) scalarBefore
    result.outcome = .bpFallback ∧ result.snapshot.parameter = -1 ∧
      (result.snapshot.parameter ^ 2 : ℝ) > scalarBefore.parameter ^ 2 := by
  norm_num [pairedTransaction, worseningBPOptimizer, scalarBefore, scalarCost,
    scalarBPCandidate, scalarFixtureValidator, solverFailureWork]

theorem rejected_measurement_preserves_bp_optimizer_state_and_charges_work :
    let result := pairedTransaction momentumFixtureOptimizer (fun x => x ^ 2)
      momentumFixtureValidator
      scalarCost false 1 (some 4) (fun _ _ _ => none) momentumBefore
    result.snapshot = clonedBPCandidate ∧ result.snapshot.optimizerState = 1 ∧
      result.work = measuredWork scalarCost true ∧
      result.work.rejectedWork = 9 := by
  norm_num [pairedTransaction, momentumFixtureOptimizer, momentumBefore,
    clonedBPCandidate, mutatedByPCCandidate, momentumFixtureValidator,
    scalarCost, measuredWork]

theorem invalid_bp_candidate_fails_closed_fixture :
    let result := pairedTransaction worseningBPOptimizer (fun x => x ^ 2)
      scalarBeforeOnlyValidator scalarCost false 1 none
      (fun _ _ _ => none) scalarBefore
    result.snapshot = scalarBefore ∧ result.outcome = .transactionFailed := by
  norm_num [pairedTransaction, worseningBPOptimizer, scalarBefore,
    scalarBPCandidate, scalarBeforeOnlyValidator, scalarCost, bpFailureWork]

theorem invalid_pc_candidate_falls_back_to_valid_bp_fixture :
    let result := pairedTransaction momentumFixtureOptimizer (fun x => x ^ 2)
      bpOnlyMomentumValidator scalarCost false 1 (some 4)
      (fun _ _ _ => none) momentumBefore
    result.snapshot = clonedBPCandidate ∧ result.outcome = .bpFallback ∧
      result.work = pcTrialFailureWork scalarCost := by
  norm_num [pairedTransaction, momentumFixtureOptimizer, momentumBefore,
    clonedBPCandidate, mutatedByPCCandidate, bpOnlyMomentumValidator,
    scalarCost, pcTrialFailureWork]

#print axioms buildPairedCandidates_uses_same_before
#print axioms PairedRealizedAdmission.strictTaskDescent
#print axioms explicit_skip_is_exact_identity
#print axioms bp_trial_failure_is_exact_identity
#print axioms bp_validation_failure_is_exact_identity
#print axioms solver_rejection_commits_exact_bp_candidate
#print axioms pc_trial_failure_commits_exact_bp_candidate
#print axioms pc_validation_failure_commits_exact_bp_candidate
#print axioms measurement_rejection_commits_exact_bp_candidate
#print axioms admission_commits_exact_pc_candidate
#print axioms admitted_transaction_has_strict_task_descent
#print axioms raw_gate_can_pass_while_paired_realized_direction_fails
#print axioms parameter_dependent_decay_needs_parameter_input
#print axioms mutating_pc_trial_before_bp_contaminates_fallback
#print axioms zero_gradient_can_move_but_explicit_skip_is_identity
#print axioms exact_bp_fallback_need_not_descend
#print axioms rejected_measurement_preserves_bp_optimizer_state_and_charges_work
#print axioms invalid_bp_candidate_fails_closed_fixture
#print axioms invalid_pc_candidate_falls_back_to_valid_bp_fixture

end
end PairedOptimizerTransaction
end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
