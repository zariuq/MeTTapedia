import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.Predictions
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.TypedRegisters
import Mettapedia.MachineLearning.NeuralNetworks.ForgettingGeometry.InterferenceGram
import Mettapedia.MachineLearning.NeuralNetworks.ForgettingGeometry.MetricDictionary

/-!
# CAROM as a gated workspace decoder

This file formalizes the linear/quadratic CAROM contract used by the workspace
decoder comparison: fixed-address slots, reusable content-addressable
read-transform-gate-write operators, and their simultaneous averaged write.
The defining equation is supplied by the architecture contract; this file does
not invent bibliographic metadata for CAROM.

The structural reduction to `GatedOperatorFamily` is exact.  Convergence is
transported only through an explicit linearization certificate, and the depth
and interference sections record two necessary corrections:

* spectral contraction alone does not imply a finite optimal recurrence depth;
* commutator energy controls sequential order dependence, not the already-exact
  simultaneous operator average.

Nothing here claims that a trained nonlinear decoder has the linear spectrum,
finite-depth optimum, or quadratic Hessians used by the formal model.  Whether
the theorem-predicted diagnostics track OEIS yield remains empirical.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Filter Finset Function Set Topology
open scoped ENNReal NNReal
open Mettapedia.GSLT.LanguageDef.AtomicRefinement
open Mettapedia.GSLT.LanguageDef.RefinementInterface
open Mettapedia.MachineLearning.ContinualLearning
open Mettapedia.MachineLearning.NeuralNetworks.ForgettingGeometry
open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

universe uSlot uOperator uContent uParams

namespace Carom

/-! ## T1: exact reduction to the sealed gated family -/

/-- Structural CAROM mechanisms over fixed-address slots.  Operator `k` reads
slot `i` as `∑ j, attention k i j • workspace j`; its reusable transform then
produces one proposal per fixed slot.  This is structural data, not a claim
about a trained nonlinear attention map. -/
structure Mechanisms
    (Slot : Type uSlot) (Operator : Type uOperator) (Content : Type uContent)
    [Fintype Slot] [NormedAddCommGroup Content] [NormedSpace ℝ Content] where
  attention : Operator → Slot → Slot → ℝ
  transform : Operator → (Slot → Content) → (Slot → Content)
  gate : Operator → Workspace Slot Content → (Slot → Content) → Slot → ℝ

namespace Mechanisms

variable {Slot : Type uSlot} {Operator : Type uOperator}
  {Content : Type uContent}
  [Fintype Slot] [NormedAddCommGroup Content] [NormedSpace ℝ Content]
  (mechanisms : Mechanisms Slot Operator Content)

/-- Structural CAROM content-addressed read at one fixed slot. -/
noncomputable def readAt (operator : Operator)
    (workspace : Workspace Slot Content) (slot : Slot) : Content :=
  ∑ source, mechanisms.attention operator slot source • workspace source

/-- Structural CAROM transformed read, retaining every fixed destination
address. -/
noncomputable def transformedRead (operator : Operator)
    (workspace : Workspace Slot Content) : Slot → Content :=
  mechanisms.transform operator (mechanisms.readAt operator workspace)

/-- Structural gate used by one CAROM operator at one fixed slot. -/
noncomputable def gateAt (operator : Operator)
    (workspace : Workspace Slot Content) (slot : Slot) : ℝ :=
  mechanisms.gate operator workspace
    (mechanisms.transformedRead operator workspace) slot

/-- Structural content proposed by one CAROM operator at one fixed slot. -/
noncomputable def proposalAt (operator : Operator)
    (workspace : Workspace Slot Content) (slot : Slot) : Content :=
  mechanisms.transformedRead operator workspace slot

/-- Exact adapter from the CAROM read-transform-gate-write contract to the
sealed workspace dynamics.  It adds no second update semantics. -/
noncomputable def toGatedOperatorFamily :
    GatedOperatorFamily Slot Operator Content (Slot → Content) (Slot → Content) where
  read := fun operator workspace => mechanisms.readAt operator workspace
  transform := mechanisms.transform
  gate := mechanisms.gate
  write := fun _operator _workspace latent slot => latent slot

@[simp] theorem toGatedOperatorFamily_latent
    (workspace : Workspace Slot Content) (operator : Operator) :
    mechanisms.toGatedOperatorFamily.latent workspace operator =
      mechanisms.transformedRead operator workspace := by
  rfl

@[simp] theorem toGatedOperatorFamily_gateAt
    (workspace : Workspace Slot Content) (operator : Operator) (slot : Slot) :
    mechanisms.toGatedOperatorFamily.gateAt workspace operator slot =
      mechanisms.gateAt operator workspace slot := by
  rfl

@[simp] theorem toGatedOperatorFamily_contentAt
    (workspace : Workspace Slot Content) (operator : Operator) (slot : Slot) :
    mechanisms.toGatedOperatorFamily.contentAt workspace operator slot =
      mechanisms.proposalAt operator workspace slot := by
  rfl

section FiniteOperators

variable [Fintype Operator] [Nonempty Operator]

omit [Nonempty Operator] in
/-- Reduction crown, structural scope: the sealed `GatedOperatorFamily.step`
is exactly CAROM's simultaneous `K`-operator recurrent write equation.  The
factor `operatorAverageScale` is `1 / K`. -/
theorem gated_step_eq_carom_recurrentWrite
    (workspace : Workspace Slot Content) (slot : Slot) :
    mechanisms.toGatedOperatorFamily.step workspace slot =
      workspace slot +
        GatedOperatorFamily.operatorAverageScale (Operator := Operator) •
          ∑ operator, mechanisms.gateAt operator workspace slot •
            (mechanisms.proposalAt operator workspace slot - workspace slot) := by
  rfl

/-- Structural sum of the `K` CAROM gate values at one fixed slot. -/
noncomputable def gateSum
    (workspace : Workspace Slot Content) (slot : Slot) : ℝ :=
  ∑ operator, mechanisms.gateAt operator workspace slot

/-- Structural gain-weighted CAROM target
`(∑ k, gₖᵢ cₖᵢ) / (∑ k, gₖᵢ)`.  It is used only under an explicit nonzero gate
sum; the zero-gate branch is kept separate. -/
noncomputable def gainWeightedTarget
    (workspace : Workspace Slot Content) (slot : Slot) : Content :=
  (mechanisms.gateSum workspace slot)⁻¹ •
    ∑ operator, mechanisms.gateAt operator workspace slot •
      mechanisms.proposalAt operator workspace slot

omit [Nonempty Operator] in
/-- Collapse crown, structural scope: a nonzero `K`-operator average is one
gated interpolation toward the gain-weighted target.  This identity does not
assume linear transforms, contraction, or trained-model calibration. -/
theorem gated_step_eq_singleInterpolation
    (workspace : Workspace Slot Content) (slot : Slot)
    (hgate : mechanisms.gateSum workspace slot ≠ 0) :
    mechanisms.toGatedOperatorFamily.step workspace slot =
      workspace slot +
        mechanisms.toGatedOperatorFamily.aggregateGate workspace slot •
          (mechanisms.gainWeightedTarget workspace slot - workspace slot) := by
  rw [mechanisms.gated_step_eq_carom_recurrentWrite]
  simp only [GatedOperatorFamily.aggregateGate,
    GatedOperatorFamily.operatorAverageScale, gainWeightedTarget, gateSum]
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
  have hcancel :
      (∑ operator, mechanisms.gateAt operator workspace slot) *
          (∑ operator, mechanisms.gateAt operator workspace slot)⁻¹ = 1 :=
    mul_inv_cancel₀ hgate
  have hscaleCancel :
      ((Fintype.card Operator : ℝ)⁻¹ *
          ∑ operator, mechanisms.gateAt operator workspace slot) *
            (∑ operator, mechanisms.gateAt operator workspace slot)⁻¹ =
        (Fintype.card Operator : ℝ)⁻¹ := by
    rw [mul_assoc, hcancel, mul_one]
  simp_rw [mechanisms.toGatedOperatorFamily_gateAt]
  simp only [smul_smul]
  rw [hscaleCancel]
  module

/-- Unit-gate collapse package, structural scope: CAROM's aggregate gain lies
in `[0,1]`, and the nonzero-gate update has the exact single-interpolation
form. -/
theorem unitGates_collapseCrown
    (workspace : Workspace Slot Content) (slot : Slot)
    (hgates : mechanisms.toGatedOperatorFamily.GatesUnitInterval workspace)
    (hgate : mechanisms.gateSum workspace slot ≠ 0) :
    mechanisms.toGatedOperatorFamily.step workspace slot =
        workspace slot +
          mechanisms.toGatedOperatorFamily.aggregateGate workspace slot •
            (mechanisms.gainWeightedTarget workspace slot - workspace slot) ∧
      0 ≤ mechanisms.toGatedOperatorFamily.aggregateGate workspace slot ∧
      mechanisms.toGatedOperatorFamily.aggregateGate workspace slot ≤ 1 := by
  exact ⟨mechanisms.gated_step_eq_singleInterpolation workspace slot hgate,
    mechanisms.toGatedOperatorFamily.aggregateGate_nonneg workspace hgates slot,
    mechanisms.toGatedOperatorFamily.aggregateGate_le_one workspace hgates slot⟩

omit [Nonempty Operator] in
/-- Zero-gate boundary, structural scope: if every CAROM operator is closed at
a slot, the simultaneous recurrent write fixes that address exactly. -/
theorem zeroGates_freeze
    (workspace : Workspace Slot Content) (slot : Slot)
    (hzero : ∀ operator, mechanisms.gateAt operator workspace slot = 0) :
    mechanisms.toGatedOperatorFamily.step workspace slot = workspace slot := by
  apply GatedOperatorFamily.step_eq_of_gates_zero
  simpa using hzero

end FiniteOperators

end Mechanisms

/-! ### Positive and negative T1 fixtures -/

/-- A nondegenerate two-operator, one-fixed-slot CAROM fixture.  Each operator
reads the slot with unit attention, adds an operator-specific content offset,
and uses the supplied gate.  This is an algebra fixture, not a trained model. -/
noncomputable def scalarTwoOperatorFixture (gate : ℝ) :
    Mechanisms (Fin 1) (Fin 2) ℝ where
  attention := fun _operator _slot _source => 1
  transform := fun operator read slot =>
    read slot + if operator = 0 then 1 else 3
  gate := fun _operator _workspace _latent _slot => gate

/-- Positive T1 fixture: two half-gated operators with proposals one and three
move a zero slot to one after the mandatory `1 / K` average. -/
theorem scalarTwoOperator_halfGate_positiveExample :
    (scalarTwoOperatorFixture (1 / 2)).toGatedOperatorFamily.step
        (fun _ => 0) 0 = 1 := by
  norm_num [scalarTwoOperatorFixture, GatedOperatorFamily.step,
    GatedOperatorFamily.operatorAverageScale, Mechanisms.gateAt,
    Mechanisms.proposalAt, Mechanisms.transformedRead, Mechanisms.readAt,
    Mechanisms.toGatedOperatorFamily,
    GatedOperatorFamily.gateAt, GatedOperatorFamily.contentAt,
    GatedOperatorFamily.latent, Fin.sum_univ_two]

/-- Negative T1 boundary: the same nondegenerate operator contents cannot move
the slot when both gates are zero. -/
theorem scalarTwoOperator_zeroGate_negativeExample :
    (scalarTwoOperatorFixture 0).toGatedOperatorFamily.step
        (fun _ => 0) 0 = 0 := by
  apply Mechanisms.zeroGates_freeze
  intro operator
  rfl

/-! ## T2: linear and recall inheritance, with the depth correction -/

/-- A certificate that one structural CAROM family is exactly an affine linear
workspace model.  The equality is substantive: arbitrary CAROM attention,
transforms, and gates are state-dependent and do not automatically possess such
a certificate. -/
structure Linearization
    (Slot : Type uSlot) (Operator : Type uOperator)
    [Fintype Slot] [Nonempty Slot] [Fintype Operator] [Nonempty Operator] where
  mechanisms : Mechanisms Slot Operator ℂ
  model : LinearWorkspaceModel (Workspace Slot ℂ)
  step_eq_model : mechanisms.toGatedOperatorFamily.step = model.step

namespace Linearization

variable {Slot : Type uSlot} {Operator : Type uOperator}
  [Fintype Slot] [Nonempty Slot] [Fintype Operator] [Nonempty Operator]
  (linearization : Linearization Slot Operator)

/-- Linear-scope inheritance: a certified CAROM linearization has a unique
equilibrium under the sealed spectral-radius condition.  No nonlinear trained
CAROM conclusion is asserted. -/
theorem spectralCondition_uniqueEquilibrium
    (hradius : spectralRadius ℂ linearization.model.linearPart < 1) :
    ∃! equilibrium : Workspace Slot ℂ,
      IsFixedPt linearization.mechanisms.toGatedOperatorFamily.step equilibrium := by
  simpa only [linearization.step_eq_model] using
    linearization.model.spectralCondition_uniqueEquilibrium hradius

/-- Linear-scope inheritance: a certified CAROM trajectory converges to the
sealed affine equilibrium under the same spectral condition. -/
theorem tendsto_equilibrium
    (initial : Workspace Slot ℂ)
    (hradius : spectralRadius ℂ linearization.model.linearPart < 1) :
    Tendsto
        (fun depth : ℕ =>
          linearization.mechanisms.toGatedOperatorFamily.step^[depth] initial)
        atTop (𝓝 linearization.model.equilibrium) := by
  simpa only [linearization.step_eq_model] using
    linearization.model.linearWorkspace_tendsto_equilibrium initial hradius

/-- Linear-scope inheritance: the geometric residual envelope transports to a
certified CAROM family without changing its nonnormal transient constant. -/
theorem geometricRate
    (initial : Workspace Slot ℂ) (q : ℝ≥0∞)
    (hradius_q : spectralRadius ℂ linearization.model.linearPart < q)
    (hq_one : q < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ depth : ℕ,
      ‖linearization.mechanisms.toGatedOperatorFamily.step^[depth] initial -
          linearization.model.equilibrium‖ ≤
        C * q.toReal ^ depth * ‖initial - linearization.model.equilibrium‖ := by
  simpa only [linearization.step_eq_model] using
    linearization.model.linearWorkspace_geometricRate initial q hradius_q hq_one

end Linearization

/-- A CAROM legal-action scorer.  Its score consumes the workspace obtained by
iterating the exact T1 family, while the checker-owned legal support remains
the sealed atomic support.  This is architectural, not a performance model. -/
structure LegalActionDecoder
    (root : AtomicRoot) (Slot : Type uSlot) (Operator : Type uOperator)
    (Content : Type uContent)
    [Fintype Slot] [Fintype Operator] [Nonempty Operator]
    [NormedAddCommGroup Content] [NormedSpace ℝ Content] where
  mechanisms : Mechanisms Slot Operator Content
  Params : Type uParams
  parameters : Params
  initialWorkspace : root.State → Workspace Slot Content
  recurrenceDepth : Nat
  score : Params → Workspace Slot Content → root.State →
    RefineAction root.Hole root.Head → ℝ

namespace LegalActionDecoder

variable {root : AtomicRoot} {Slot : Type uSlot} {Operator : Type uOperator}
  {Content : Type uContent}
  [Fintype Slot] [Fintype Operator] [Nonempty Operator]
  [NormedAddCommGroup Content] [NormedSpace ℝ Content]
  (decoder : LegalActionDecoder root Slot Operator Content)

/-- Structural adapter: CAROM may change legal-action scores through arbitrary
operators, gates, and depth, but it cannot change the checker-owned support. -/
noncomputable def toLegalActionWorkspaceDecoder :
    LegalActionWorkspaceDecoder root where
  Params := decoder.Params
  Gates := Unit
  parameters := decoder.parameters
  gates := ()
  recurrenceDepth := decoder.recurrenceDepth
  score := fun parameters _gates depth state action =>
    decoder.score parameters
      (decoder.mechanisms.toGatedOperatorFamily.step^[depth]
        (decoder.initialWorkspace state)) state action

/-- Structural recall-safety crown: for arbitrary CAROM contents, gates,
operators, and recurrence depth, ranked acceptance equals sealed acceptance;
soundness and in-budget recall follow.  No score-accuracy claim is involved. -/
theorem inheritanceCrown
    (laws : AtomicRootLaws root)
    {budget : Nat} {trace : List (RefineAction root.Hole root.Head)}
    {program : root.Program} :
    (root.asRefinementInterface.RankedAccepts
        decoder.toLegalActionWorkspaceDecoder.ranking budget trace program ↔
      root.asRefinementInterface.Accepts budget trace program) ∧
    (root.asRefinementInterface.RankedAccepts
        decoder.toLegalActionWorkspaceDecoder.ranking budget trace program →
      root.wellFormed program) ∧
    (root.budgetOK budget → root.wellFormed program →
      root.programCost program ≤ budget →
      root.asRefinementInterface.RankedAccepts
        decoder.toLegalActionWorkspaceDecoder.ranking budget
        (root.encode program) program) := by
  exact ⟨decoder.toLegalActionWorkspaceDecoder.rankedAccepts_iff_accepts laws,
    decoder.toLegalActionWorkspaceDecoder.rankedAccepts_sound laws,
    decoder.toLegalActionWorkspaceDecoder.wellFormed_rankedAccepts laws⟩

end LegalActionDecoder

/-! ### Contraction does not supply a finite depth optimum -/

/-- Two reusable operators whose proposals are zero and whose gates are one
half.  The exact CAROM average maps the single scalar slot to half its value.
This is a linear countermodel, not a trained decoder. -/
noncomputable def contractiveScalarMechanisms :
    Mechanisms (Fin 1) (Fin 2) ℝ where
  attention := fun _operator _slot _source => 1
  transform := fun _operator _read _slot => 0
  gate := fun _operator _workspace _latent _slot => 1 / 2

/-- Linear countermodel calculation: the two-operator CAROM step is exactly a
half-contraction on its fixed scalar address. -/
theorem contractiveScalar_step_eq_half (workspace : Workspace (Fin 1) ℝ) :
    contractiveScalarMechanisms.toGatedOperatorFamily.step workspace 0 =
      workspace 0 / 2 := by
  norm_num [contractiveScalarMechanisms, Mechanisms.toGatedOperatorFamily,
    GatedOperatorFamily.step, GatedOperatorFamily.operatorAverageScale,
    GatedOperatorFamily.gateAt, GatedOperatorFamily.contentAt,
    GatedOperatorFamily.latent, Fin.sum_univ_two]
  ring

/-- Linear countermodel fixture: unit initial content in the fixed scalar
address. -/
noncomputable def contractiveScalarInitial : Workspace (Fin 1) ℝ :=
  fun _ => 1

/-- Linear countermodel trajectory: the residual after `depth` steps is
exactly `(1/2)^depth`. -/
theorem contractiveScalar_iterate_eq_pow (depth : ℕ) :
    (contractiveScalarMechanisms.toGatedOperatorFamily.step^[depth]
      contractiveScalarInitial) 0 = (1 / 2 : ℝ) ^ depth := by
  induction depth with
  | zero => simp [contractiveScalarInitial]
  | succ depth ih =>
      rw [Function.iterate_succ_apply']
      rw [contractiveScalar_step_eq_half, ih, pow_succ]
      ring

/-- Squared equilibrium residual of the linear CAROM countermodel. -/
noncomputable def contractiveScalarResidualLoss (depth : ℕ) : ℝ :=
  ((contractiveScalarMechanisms.toGatedOperatorFamily.step^[depth]
    contractiveScalarInitial) 0) ^ 2

/-- Linear countermodel: every additional CAROM settling step strictly lowers
the residual loss, so contraction alone supplies no turnover depth. -/
theorem contractiveScalarResidualLoss_strictlyDecreases (depth : ℕ) :
    contractiveScalarResidualLoss (depth + 1) <
      contractiveScalarResidualLoss depth := by
  rw [contractiveScalarResidualLoss, contractiveScalarResidualLoss,
    contractiveScalar_iterate_eq_pow, contractiveScalar_iterate_eq_pow]
  have hpositive : 0 < (1 / 2 : ℝ) ^ depth := pow_pos (by norm_num) depth
  rw [show (1 / 2 : ℝ) ^ (depth + 1) = (1 / 2 : ℝ) ^ depth / 2 by
    rw [pow_succ]
    ring]
  nlinarith [sq_pos_of_pos hpositive]

/-- T2 correction, linear scope: the exact CAROM half-contraction has no
finite global minimizer of equilibrium-residual loss.  Therefore the sealed
shift-chain depth optimum cannot be inherited from spectral contraction alone. -/
theorem contraction_does_not_force_finiteDepthOptimum :
    ¬ ∃ optimalDepth : ℕ, ∀ evaluationDepth : ℕ,
      contractiveScalarResidualLoss optimalDepth ≤
        contractiveScalarResidualLoss evaluationDepth := by
  rintro ⟨optimalDepth, hoptimal⟩
  have hnext := hoptimal (optimalDepth + 1)
  have hstrict := contractiveScalarResidualLoss_strictlyDecreases optimalDepth
  linarith

/-! ## T3: residuals, entropy, and validation loss are distinct -/

/-- Distance from the shift-chain readout to its registered soft target.  This
is the residual whose square is `finiteDepthMismatchLoss`; it is not an
equilibrium residual and is not cross-entropy. -/
noncomputable def targetResidual
    (trainingDepth : ℕ) (target : ℝ) (evaluationDepth : ℕ) : ℝ :=
  |arbitraryDepthTurnoverProbability trainingDepth target evaluationDepth - target|

/-- The sealed finite-depth mismatch is exactly squared target residual. -/
theorem finiteDepthMismatchLoss_eq_targetResidual_sq
    (trainingDepth : ℕ) (target : ℝ) (evaluationDepth : ℕ) :
    finiteDepthMismatchLoss trainingDepth target evaluationDepth =
      targetResidual trainingDepth target evaluationDepth ^ 2 := by
  rw [finiteDepthMismatchLoss, targetResidual, sq_abs]

/-- For a nonuniform interior soft target, target residual vanishes exactly at
the registered depth. -/
theorem targetResidual_eq_zero_iff
    (trainingDepth : ℕ) (target : ℝ) (evaluationDepth : ℕ)
    (htarget : target ∈ Ioo (0 : ℝ) 1) (hnonuniform : target ≠ 1 / 2) :
    targetResidual trainingDepth target evaluationDepth = 0 ↔
      evaluationDepth = trainingDepth := by
  constructor
  · intro hzero
    by_contra hdepth
    rw [targetResidual,
      arbitraryDepthTurnoverProbability_away_from_target
        trainingDepth target evaluationDepth hdepth] at hzero
    exact (abs_ne_zero.mpr (sub_ne_zero.mpr hnonuniform.symm)) hzero
  · intro hdepth
    subst evaluationDepth
    rw [targetResidual,
      arbitraryDepthTurnoverProbability_at_target trainingDepth target htarget,
      sub_self, abs_zero]

/-- Distance from the uniform equilibrium readout.  Unlike target residual,
this measures decisiveness: the registered nonuniform depth maximizes it and
the off-depth equilibrium has value zero. -/
noncomputable def equilibriumReadoutResidual
    (trainingDepth : ℕ) (target : ℝ) (evaluationDepth : ℕ) : ℝ :=
  |arbitraryDepthTurnoverProbability trainingDepth target evaluationDepth - 1 / 2|

/-- Positive example: the registered depth uniquely maximizes distance from
the uniform equilibrium readout in the exact shift-chain fixture. -/
theorem equilibriumReadoutResidual_uniqueMaximum
    (trainingDepth : ℕ) (target : ℝ)
    (htarget : target ∈ Ioo (0 : ℝ) 1) (hnonuniform : target ≠ 1 / 2) :
    ∀ evaluationDepth : ℕ,
      equilibriumReadoutResidual trainingDepth target evaluationDepth ≤
          equilibriumReadoutResidual trainingDepth target trainingDepth ∧
        (equilibriumReadoutResidual trainingDepth target evaluationDepth =
            equilibriumReadoutResidual trainingDepth target trainingDepth ↔
          evaluationDepth = trainingDepth) := by
  intro evaluationDepth
  by_cases hdepth : evaluationDepth = trainingDepth
  · subst evaluationDepth
    exact ⟨le_rfl, by simp⟩
  · rw [equilibriumReadoutResidual, equilibriumReadoutResidual,
      arbitraryDepthTurnoverProbability_away_from_target
        trainingDepth target evaluationDepth hdepth,
      arbitraryDepthTurnoverProbability_at_target trainingDepth target htarget]
    have hpositive : 0 < |target - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hnonuniform)
    constructor
    · norm_num
    · constructor
      · intro heq
        norm_num at heq
        linarith
      · exact fun heq => (hdepth heq).elim

/-- Entropy reads the same shift-chain event in the opposite direction:
the registered nonuniform depth is the unique entropy minimum. -/
theorem turnoverEntropy_uniqueMinimum
    (trainingDepth : ℕ) (target : ℝ)
    (htarget : target ∈ Ioo (0 : ℝ) 1) (hnonuniform : target ≠ 1 / 2) :
    ∀ evaluationDepth : ℕ,
      arbitraryDepthTurnoverEntropy trainingDepth target trainingDepth ≤
          arbitraryDepthTurnoverEntropy trainingDepth target evaluationDepth ∧
        (arbitraryDepthTurnoverEntropy trainingDepth target evaluationDepth =
            arbitraryDepthTurnoverEntropy trainingDepth target trainingDepth ↔
          evaluationDepth = trainingDepth) := by
  intro evaluationDepth
  by_cases hdepth : evaluationDepth = trainingDepth
  · subst evaluationDepth
    exact ⟨le_rfl, by simp⟩
  · rw [arbitraryDepthTurnoverEntropy_at_target trainingDepth target htarget,
      arbitraryDepthTurnoverEntropy_away_from_target
        trainingDepth target evaluationDepth hdepth]
    have hstrict := binEntropy_lt_uniform_of_nonuniform target htarget hnonuniform
    exact ⟨hstrict.le, ⟨fun heq => (ne_of_lt hstrict heq.symm).elim,
      fun heq => (hdepth heq).elim⟩⟩

/-- Hard-positive validation cross-entropy for the same scalar readout.  Its
label is deliberately different from the soft target used to construct the
shift-chain state. -/
noncomputable def hardPositiveCrossEntropy
    (trainingDepth : ℕ) (target : ℝ) (evaluationDepth : ℕ) : ℝ :=
  -Real.log (arbitraryDepthTurnoverProbability trainingDepth target evaluationDepth)

/-- Positive example: when the registered soft target favors the positive
label, hard-positive cross-entropy agrees with target mismatch on the preferred
depth. -/
theorem hardPositiveCrossEntropy_agrees_above_half
    (trainingDepth : ℕ) (target : ℝ) (evaluationDepth : ℕ)
    (htarget : target ∈ Ioo (1 / 2 : ℝ) 1)
    (hdepth : evaluationDepth ≠ trainingDepth) :
    hardPositiveCrossEntropy trainingDepth target trainingDepth <
      hardPositiveCrossEntropy trainingDepth target evaluationDepth := by
  rw [hardPositiveCrossEntropy, hardPositiveCrossEntropy,
    arbitraryDepthTurnoverProbability_at_target trainingDepth target
      ⟨by linarith [htarget.1], htarget.2⟩,
    arbitraryDepthTurnoverProbability_away_from_target
      trainingDepth target evaluationDepth hdepth]
  have hlog := Real.strictMonoOn_log
    (by norm_num : (1 / 2 : ℝ) ∈ Set.Ioi 0)
    (by exact (show (0 : ℝ) < 1 / 2 by norm_num).trans htarget.1)
    htarget.1
  linarith

/-- Negative witness: mismatch selects the registered soft target `1/4`, but
hard-positive validation cross-entropy prefers the off-depth uniform readout.
Thus the CAROM depth claim must name its validation loss. -/
theorem validationCrossEntropy_can_reverse_targetMismatch :
    finiteDepthMismatchLoss 1 (1 / 4 : ℝ) 1 <
        finiteDepthMismatchLoss 1 (1 / 4 : ℝ) 0 ∧
      hardPositiveCrossEntropy 1 (1 / 4 : ℝ) 0 <
        hardPositiveCrossEntropy 1 (1 / 4 : ℝ) 1 := by
  constructor
  · rw [finiteDepthMismatchLoss_at_trainingDepth 1 (1 / 4) (by norm_num),
      finiteDepthMismatchLoss_away_from_trainingDepth 1 (1 / 4) 0 (by norm_num)]
    norm_num
  · rw [hardPositiveCrossEntropy, hardPositiveCrossEntropy,
      arbitraryDepthTurnoverProbability_away_from_target 1 (1 / 4) 0 (by norm_num),
      arbitraryDepthTurnoverProbability_at_target 1 (1 / 4) (by norm_num)]
    have hlog := Real.strictMonoOn_log
      (by norm_num : (1 / 4 : ℝ) ∈ Set.Ioi 0)
      (by norm_num : (1 / 2 : ℝ) ∈ Set.Ioi 0)
      (by norm_num : (1 / 4 : ℝ) < 1 / 2)
    linarith

/-! ## T4: quadratic operator order and interference geometry -/

/-- A finite-dimensional quadratic chart for reusable CAROM operators.  Each
operator label receives a linear curvature operator `K`.  This is the declared
linear-quadratic scope in which order and interference are calculated. -/
structure QuadraticOperatorFamily (Operator : Type uOperator)
    (Index : Type uSlot) where
  K : Operator → Matrix Index Index ℝ

namespace QuadraticOperatorFamily

variable {Operator : Type uOperator} {Index : Type uSlot} [Fintype Index]
  (family : QuadraticOperatorFamily Operator Index)

/-- Degree-two interference energy of two labeled `K` operators. -/
noncomputable def interferenceEnergy (first second : Operator) : ℝ :=
  pairwiseInterferenceEnergy (family.K first) (family.K second)

/-- Sequential linear action in the order “first, then second”. -/
noncomputable def orderedProduct (first second : Operator) :
    Matrix Index Index ℝ :=
  family.K second * family.K first

/-- The centered quadratic task induced by a labeled `K` operator. -/
noncomputable def centeredTask (operator : Operator) : QuadraticTask Index where
  curvature := family.K operator
  optimum := 0

/-- Concrete CAROM mechanisms induced by the labeled `K` operators: attention
reads the same fixed address, the reusable transform applies `K`, and the gate
is supplied independently. -/
noncomputable def toMechanisms [DecidableEq Index]
    (gate : Operator → Workspace Index ℝ → Index → ℝ) :
    Mechanisms Index Operator ℝ where
  attention := fun _operator slot source => if source = slot then 1 else 0
  transform := fun operator read => (family.K operator).mulVec read
  gate := fun operator workspace _latent slot => gate operator workspace slot

/-- Exact InterferenceGram bridge: zero labeled energy is equivalent to
commutation of the corresponding `K` operators. -/
theorem interferenceEnergy_eq_zero_iff_commute (first second : Operator) :
    family.interferenceEnergy first second = 0 ↔
      Commute (family.K first) (family.K second) := by
  exact pairwiseInterferenceEnergy_eq_zero_iff_commute
    (family.K first) (family.K second)

/-- Zero interference energy makes the two ordered `K` products equal. -/
theorem orderedProduct_eq_reverse_of_zeroEnergy
    (first second : Operator)
    (hzero : family.interferenceEnergy first second = 0) :
    family.orderedProduct first second = family.orderedProduct second first := by
  have hcommute :=
    (family.interferenceEnergy_eq_zero_iff_commute first second).1 hzero
  exact hcommute.eq.symm

/-- For centered quadratic read-transform-write operators, zero interference
energy transports to equality of the two sequential update orders. -/
theorem centeredSequentialUpdates_orderIndependent_of_zeroEnergy
    (first second : Operator)
    (hzero : family.interferenceEnergy first second = 0)
    (stepSize : ℝ) (parameter : Index → ℝ) :
    sequentialTwoTaskUpdate (family.centeredTask first) (family.centeredTask second)
        stepSize parameter =
      sequentialTwoTaskUpdate (family.centeredTask second) (family.centeredTask first)
        stepSize parameter := by
  apply centered_sequential_updates_commute
  · rfl
  · rfl
  · exact (family.interferenceEnergy_eq_zero_iff_commute first second).mp hzero |>.eq.symm

end QuadraticOperatorFamily

/-- Two labeled oblique `K` operators, sharing the same `Fin 2` operator index
used by the explicit simultaneous CAROM fixture. -/
noncomputable def obliqueQuadraticOperators :
    QuadraticOperatorFamily (Fin 2) (Fin 2) where
  K operator := if operator = 0 then obliqueFirstTask.curvature
    else obliqueSecondTask.curvature

/-- The actual CAROM mechanism family induced by the oblique `K` fixture, with
constant half gates. -/
noncomputable def obliqueQuadraticMechanisms : Mechanisms (Fin 2) (Fin 2) ℝ :=
  obliqueQuadraticOperators.toMechanisms fun _operator _workspace _slot => 1 / 2

theorem obliqueFirstTask_curvature_eq_axis :
    obliqueFirstTask.curvature = axisRankOneCurvature := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [obliqueFirstTask, axisRankOneCurvature]

theorem obliqueSecondTask_curvature_eq_direction :
    obliqueSecondTask.curvature = directionRankOneCurvature 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [obliqueSecondTask, directionRankOneCurvature]

/-- Negative order fixture: the oblique labeled pair has strictly positive
InterferenceGram energy. -/
theorem obliqueQuadraticOperators_interferenceEnergy_eq_two :
    obliqueQuadraticOperators.interferenceEnergy 0 1 = 2 := by
  change pairwiseInterferenceEnergy obliqueFirstTask.curvature
    obliqueSecondTask.curvature = 2
  rw [obliqueFirstTask_curvature_eq_axis,
    obliqueSecondTask_curvature_eq_direction]
  exact unitOblique_interferenceEnergy_positive_negativeExample

/-- Positive simultaneous fixture: the CAROM family actually induced by the
oblique `K` operators still obeys the exact averaged-write equation.  Positive
`K` interference concerns sequential order; it does not create an error term
in the simultaneous write. -/
theorem positiveInterference_simultaneousAverage_remainsExact
    (workspace : Workspace (Fin 2) ℝ) (slot : Fin 2) :
    obliqueQuadraticOperators.interferenceEnergy 0 1 = 2 ∧
      obliqueQuadraticMechanisms.toGatedOperatorFamily.step workspace slot =
        workspace slot +
          GatedOperatorFamily.operatorAverageScale (Operator := Fin 2) •
            ∑ operator, obliqueQuadraticMechanisms.gateAt operator workspace slot •
              (obliqueQuadraticMechanisms.proposalAt operator workspace slot -
                workspace slot) := by
  exact ⟨obliqueQuadraticOperators_interferenceEnergy_eq_two,
    obliqueQuadraticMechanisms.gated_step_eq_carom_recurrentWrite workspace slot⟩

/-- At the zero parameter, the centered oblique tasks have zero sequential
connection remainder despite positive interference energy. -/
theorem oblique_positiveEnergy_zeroConnectionRemainderAtOrigin :
    0 < pairwiseInterferenceEnergy obliqueFirstTask.curvature
          obliqueSecondTask.curvature ∧
      quadraticConnectionRemainder obliqueFirstTask obliqueSecondTask 1
          (0 : Fin 2 → ℝ) = 0 := by
  constructor
  · rw [obliqueFirstTask_curvature_eq_axis,
      obliqueSecondTask_curvature_eq_direction,
      unitOblique_interferenceEnergy_positive_negativeExample]
    norm_num
  · funext i
    fin_cases i <;>
      simp [quadraticConnectionRemainder, obliqueFirstTask, obliqueSecondTask,
        QuadraticTask.gradient]

/-- Crown correction: InterferenceGram energy and the connection remainder
are different diagnostics.  Positive energy can coexist with zero remainder
at a state, while same-cause reuse has zero energy and nonzero remainder. -/
theorem interferenceEnergy_connectionRemainder_separationCrown :
    (0 < pairwiseInterferenceEnergy obliqueFirstTask.curvature
          obliqueSecondTask.curvature ∧
      quadraticConnectionRemainder obliqueFirstTask obliqueSecondTask 1
          (0 : Fin 2 → ℝ) = 0) ∧
    (pairwiseInterferenceEnergy scalarUnitTask.curvature
          scalarUnitTask.curvature = 0 ∧
      quadraticConnectionRemainder scalarUnitTask scalarUnitTask (1 / 2)
          scalarUnitParameter ≠ 0) := by
  refine ⟨oblique_positiveEnergy_zeroConnectionRemainderAtOrigin, ?_⟩
  constructor
  · exact (pairwiseInterferenceEnergy_eq_zero_iff_commute _ _).2 (Commute.refl _)
  · exact sameCause_connectionRemainder_nonzero_negativeExample

/-! ## T5: within-action settling and across-action recurrence -/

/-- Product state for the two recurrence scales: the checker-owned atomic
construction state and the learned workspace carried between actions. -/
structure TwoScaleState (root : AtomicRoot) (Slot : Type uSlot)
    (Content : Type uContent) where
  rootState : root.State
  workspace : Workspace Slot Content

/-- The inner recurrence: a finite number of exact CAROM settling steps while
the candidate action and atomic state are held fixed. -/
noncomputable def withinActionSettle
    {Slot : Type uSlot} {Operator : Type uOperator} {Content : Type uContent}
    [Fintype Slot] [Fintype Operator] [Nonempty Operator]
    [NormedAddCommGroup Content] [NormedSpace ℝ Content]
    (mechanisms : Mechanisms Slot Operator Content) (depth : ℕ)
    (workspace : Workspace Slot Content) : Workspace Slot Content :=
  mechanisms.toGatedOperatorFamily.step^[depth] workspace

/-- The outer recurrence: perform the declared finite inner settling, then
let the sealed checker alone advance the atomic construction state.  The
settled workspace is carried as the next action's initial workspace. -/
noncomputable def acrossActionStep
    (root : AtomicRoot)
    {Slot : Type uSlot} {Operator : Type uOperator} {Content : Type uContent}
    [Fintype Slot] [Fintype Operator] [Nonempty Operator]
    [NormedAddCommGroup Content] [NormedSpace ℝ Content]
    (mechanisms : Mechanisms Slot Operator Content) (depth : ℕ)
    (state : TwoScaleState root Slot Content)
    (action : RefineAction root.Hole root.Head) :
    Option (TwoScaleState root Slot Content) :=
  (root.refine? state.rootState action.hole action.head).map fun nextRoot =>
    ⟨nextRoot, withinActionSettle mechanisms depth state.workspace⟩

/-- Checker adequacy for every inner depth: projecting one outer CAROM step to
the root state recovers the sealed atomic transition exactly. -/
theorem acrossActionStep_rootProjection
    (root : AtomicRoot)
    {Slot : Type uSlot} {Operator : Type uOperator} {Content : Type uContent}
    [Fintype Slot] [Fintype Operator] [Nonempty Operator]
    [NormedAddCommGroup Content] [NormedSpace ℝ Content]
    (mechanisms : Mechanisms Slot Operator Content) (depth : ℕ)
    (state : TwoScaleState root Slot Content)
    (action : RefineAction root.Hole root.Head) :
    (acrossActionStep root mechanisms depth state action).map
        TwoScaleState.rootState =
      root.refine? state.rootState action.hole action.head := by
  unfold acrossActionStep
  cases root.refine? state.rootState action.hole action.head <;> rfl

/-- A per-action equilibrium read: its workspace is a certified fixed point
of the exact CAROM inner recurrence and can therefore seed the next action. -/
structure PerActionEquilibrium
    (root : AtomicRoot)
    {Slot : Type uSlot} {Operator : Type uOperator} {Content : Type uContent}
    [Fintype Slot] [Fintype Operator] [Nonempty Operator]
    [NormedAddCommGroup Content] [NormedSpace ℝ Content]
    (mechanisms : Mechanisms Slot Operator Content) where
  read : root.State → Workspace Slot Content
  fixed : ∀ state, IsFixedPt mechanisms.toGatedOperatorFamily.step (read state)

/-- The equilibrium outer recurrence: use the certified per-action
equilibrium as the next action's initial workspace, while leaving the atomic
transition unchanged. -/
noncomputable def acrossActionEquilibriumStep
    (root : AtomicRoot)
    {Slot : Type uSlot} {Operator : Type uOperator} {Content : Type uContent}
    [Fintype Slot] [Fintype Operator] [Nonempty Operator]
    [NormedAddCommGroup Content] [NormedSpace ℝ Content]
    {mechanisms : Mechanisms Slot Operator Content}
    (equilibrium : PerActionEquilibrium root mechanisms)
    (state : TwoScaleState root Slot Content)
    (action : RefineAction root.Hole root.Head) :
    Option (TwoScaleState root Slot Content) :=
  (root.refine? state.rootState action.hole action.head).map fun nextRoot =>
    ⟨nextRoot, equilibrium.read state.rootState⟩

/-- Composition crown: when an action starts at its certified equilibrium,
every finite inner depth—including depth one—induces the same outer transition
as the equilibrium-read process.  Away from equilibrium only the workspace,
not the checker automaton, may differ. -/
theorem finiteDepth_eq_equilibriumStep_when_initializedAtEquilibrium
    (root : AtomicRoot)
    {Slot : Type uSlot} {Operator : Type uOperator} {Content : Type uContent}
    [Fintype Slot] [Fintype Operator] [Nonempty Operator]
    [NormedAddCommGroup Content] [NormedSpace ℝ Content]
    {mechanisms : Mechanisms Slot Operator Content}
    (equilibrium : PerActionEquilibrium root mechanisms)
    (depth : ℕ) (rootState : root.State)
    (action : RefineAction root.Hole root.Head) :
    acrossActionStep root mechanisms depth
        ⟨rootState, equilibrium.read rootState⟩ action =
      acrossActionEquilibriumStep root equilibrium
        ⟨rootState, equilibrium.read rootState⟩ action := by
  unfold acrossActionStep acrossActionEquilibriumStep withinActionSettle
  rw [(equilibrium.fixed rootState).iterate depth]

/-- Negative depth boundary: away from equilibrium, zero inner steps and one
inner step are genuinely different in the half-contraction fixture. -/
theorem withinAction_depthZero_ne_depthOne_contractingExample :
    withinActionSettle contractiveScalarMechanisms 0 contractiveScalarInitial ≠
      withinActionSettle contractiveScalarMechanisms 1 contractiveScalarInitial := by
  intro heq
  have hslot := congrFun heq 0
  rw [withinActionSettle, withinActionSettle,
    contractiveScalar_iterate_eq_pow, contractiveScalar_iterate_eq_pow] at hslot
  norm_num at hslot

#print axioms Mechanisms.gated_step_eq_carom_recurrentWrite
#print axioms Mechanisms.gated_step_eq_singleInterpolation
#print axioms Linearization.spectralCondition_uniqueEquilibrium
#print axioms Linearization.tendsto_equilibrium
#print axioms Linearization.geometricRate
#print axioms LegalActionDecoder.inheritanceCrown
#print axioms contraction_does_not_force_finiteDepthOptimum
#print axioms targetResidual_eq_zero_iff
#print axioms equilibriumReadoutResidual_uniqueMaximum
#print axioms turnoverEntropy_uniqueMinimum
#print axioms validationCrossEntropy_can_reverse_targetMismatch
#print axioms QuadraticOperatorFamily.interferenceEnergy_eq_zero_iff_commute
#print axioms QuadraticOperatorFamily.centeredSequentialUpdates_orderIndependent_of_zeroEnergy
#print axioms interferenceEnergy_connectionRemainder_separationCrown
#print axioms acrossActionStep_rootProjection
#print axioms finiteDepth_eq_equilibriumStep_when_initializedAtEquilibrium

end Carom

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
