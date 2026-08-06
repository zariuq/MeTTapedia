import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.MatrixBelief
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.SequentialSelectivity
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.TypedRegisters
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.WeightedEvidenceDynamics

/-!
# Weighted-evidence selective belief-decoder contract

The selective belief arm stores query-indexed weighted evidence registers.
Its retention parameter is registered beside the jump-derived default rather
than hidden inside natural-number counts.  Retention, an input-conditioned
gain schedule, and recurrence depth may affect scores, but the arm only
reorders the sealed legal-action support.  Consequently soundness and recall
are inherited for arbitrary weighted contents, decay schedules, gains,
parameters, and depth.

When the gain is the exact linear-Gaussian information gain, the separately
sealed operator theorem identifies equilibrium with the posterior mean.  The
architectural inheritance theorem is unconditional; the Bayesian conclusion
is explicitly linear-Gaussian.  No trained nonlinear performance claim is
made here.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Mettapedia.GSLT.LanguageDef.AtomicRefinement
open Mettapedia.GSLT.LanguageDef.RefinementInterface
open Mettapedia.GSLT.LanguageDef.PureBetaAtomicRoot
open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
open Mettapedia.PLN.Evidence
open Mettapedia.PLN.Evidence.EvidenceQuantale
open scoped ENNReal

universe uQuery uParams uInput

/-! ## Formal WM-arm specification -/

/-- Typed numerical payload exposed to the sealed legal-action scorer. -/
structure WeightedBeliefPayload (Query : Type uQuery) where
  evidence : Query → WeightedEvidence
  decayRetention : Query → ℝ≥0∞
  derivedDecayDefault : Query → ℝ≥0∞
  gain : Query → ℝ

/-- A selective belief decoder whose primal registers are weighted evidence.
`decayRetention` is the registered operational parameter;
`derivedDecayDefault` is computed from the declared prior/process variances.
`gain input` is a derived moment-coordinate control signal, not stored
evidence. -/
structure WeightedSelectiveBeliefDecoder
    (root : AtomicRoot) (Query : Type uQuery) where
  Params : Type uParams
  Input : Type uInput
  parameters : Params
  currentInput : Input
  recurrenceDepth : Nat
  evidence : Query → WeightedEvidence
  decayRetention : Input → Query → ℝ≥0∞
  decayRetention_le_one : ∀ input query, decayRetention input query ≤ 1
  priorVariance : Input → Query → ℝ
  jumpVariance : Input → Query → ℝ
  priorVariance_pos : ∀ input query, 0 < priorVariance input query
  jumpVariance_nonneg : ∀ input query, 0 ≤ jumpVariance input query
  gain : Input → Query → ℝ
  score : Params → WeightedBeliefPayload Query → Nat →
    root.State → RefineAction root.Hole root.Head → ℝ

namespace WeightedSelectiveBeliefDecoder

variable {root : AtomicRoot} {Query : Type uQuery}
  (arm : WeightedSelectiveBeliefDecoder root Query)

/-- Jump-derived default retained alongside the registered decay parameter. -/
noncomputable def derivedDecayDefault (input : arm.Input) (query : Query) : ℝ≥0∞ :=
  derivedJumpEvidenceRetention
    (arm.priorVariance input query) (arm.jumpVariance input query)

/-- Current registered numerical payload. -/
noncomputable def payload : WeightedBeliefPayload Query where
  evidence := arm.evidence
  decayRetention := arm.decayRetention arm.currentInput
  derivedDecayDefault := arm.derivedDecayDefault arm.currentInput
  gain := arm.gain arm.currentInput

/-- The jump-derived default is an honest retention under the registered
variance conditions. -/
theorem derivedDecayDefault_le_one (input : arm.Input) (query : Query) :
    arm.derivedDecayDefault input query ≤ 1 :=
  derivedJumpEvidenceRetention_le_one
    (arm.priorVariance input query) (arm.jumpVariance input query)
    (arm.priorVariance_pos input query) (arm.jumpVariance_nonneg input query)

/-- Predicate identifying the principled default WM arm while still allowing
an experimental learned-retention arm in the same contract. -/
def UsesDerivedDecayDefault : Prop :=
  ∀ input query,
    arm.decayRetention input query = arm.derivedDecayDefault input query

/-- Forgetful adapter to the already sealed legal-action workspace decoder.
Weighted evidence, registered/default retention, and gain are passed together
as its payload; none can alter legal support. -/
noncomputable def toLegalActionWorkspaceDecoder :
    LegalActionWorkspaceDecoder root where
  Params := arm.Params
  Gates := WeightedBeliefPayload Query
  parameters := arm.parameters
  gates := arm.payload
  recurrenceDepth := arm.recurrenceDepth
  score := fun parameters payload depth state action =>
    arm.score parameters payload depth state action

/-- The selective belief arm ranks exactly the sealed legal actions for every
weighted state, retention/gain schedule, parameter value, and depth. -/
theorem ranking_listsAllLegalActions :
    root.asRefinementInterface.ListsAllLegalActions
      arm.toLegalActionWorkspaceDecoder.ranking :=
  arm.toLegalActionWorkspaceDecoder.ranking_listsAllLegalActions

/-- Any gains, any weighted evidence/retention, any recurrence depth: ranking
is accepted-language equivalent to the sealed checker. -/
theorem rankedAccepts_iff_accepts
    (laws : AtomicRootLaws root)
    {budget : Nat} {trace : List (RefineAction root.Hole root.Head)}
    {program : root.Program} :
    root.asRefinementInterface.RankedAccepts
        arm.toLegalActionWorkspaceDecoder.ranking budget trace program ↔
      root.asRefinementInterface.Accepts budget trace program :=
  arm.toLegalActionWorkspaceDecoder.rankedAccepts_iff_accepts laws

/-- Soundness inherited independently of weighted evidence, retention, and
gain contents. -/
theorem rankedAccepts_sound
    (laws : AtomicRootLaws root)
    {budget : Nat} {trace : List (RefineAction root.Hole root.Head)}
    {program : root.Program}
    (haccepted : root.asRefinementInterface.RankedAccepts
      arm.toLegalActionWorkspaceDecoder.ranking budget trace program) :
    root.wellFormed program :=
  arm.toLegalActionWorkspaceDecoder.rankedAccepts_sound laws haccepted

/-- Recall inherited independently of weighted evidence, retention, and gain
contents. -/
theorem wellFormed_rankedAccepts
    (laws : AtomicRootLaws root)
    {budget : Nat} {program : root.Program}
    (hbudget : root.budgetOK budget) (hwellFormed : root.wellFormed program)
    (hcost : root.programCost program ≤ budget) :
    root.asRefinementInterface.RankedAccepts
      arm.toLegalActionWorkspaceDecoder.ranking budget
      (root.encode program) program :=
  arm.toLegalActionWorkspaceDecoder.wellFormed_rankedAccepts
    laws hbudget hwellFormed hcost

/-- Architectural inheritance package for the WM arm. -/
theorem inheritance
    (laws : AtomicRootLaws root)
    {budget : Nat} {trace : List (RefineAction root.Hole root.Head)}
    {program : root.Program} :
    (root.asRefinementInterface.RankedAccepts
        arm.toLegalActionWorkspaceDecoder.ranking budget trace program ↔
      root.asRefinementInterface.Accepts budget trace program) ∧
    (root.asRefinementInterface.RankedAccepts
        arm.toLegalActionWorkspaceDecoder.ranking budget trace program →
      root.wellFormed program) ∧
    (root.budgetOK budget → root.wellFormed program →
      root.programCost program ≤ budget →
      root.asRefinementInterface.RankedAccepts
        arm.toLegalActionWorkspaceDecoder.ranking budget
        (root.encode program) program) := by
  exact ⟨arm.rankedAccepts_iff_accepts laws,
    arm.rankedAccepts_sound laws,
    arm.wellFormed_rankedAccepts laws⟩

end WeightedSelectiveBeliefDecoder

/-! ## Exact-gain Bayesian clause and sequential motivation -/

/-- Exact-gain clause: the matrix information mean of the sealed operator
model is exactly its unique energy equilibrium. -/
theorem exactGain_equilibrium_iff_posterior
    {Index Residual : Type*}
    [Fintype Index] [DecidableEq Index]
    [Fintype Residual] [DecidableEq Residual]
    (model : LinearGaussianOperatorModel Index Residual)
    (state : LinearGaussianOperatorSpace Index) :
    model.Equilibrium state ↔
      (fun index => state index) =
        (GaussianInformation.ofOperatorModel model).mean :=
  GaussianInformation.operator_equilibrium_iff_eq_informationMean model state

/-- Derived motivation for an input-conditioned gain: under the sharp
sequential condition, every constant scalar gate loses to the Riccati gain
schedule. -/
theorem inputConditionedGain_sequentialMotivation
    (priorVariance firstNoise secondNoise gate : ℝ)
    (hprior : 0 < priorVariance)
    (hfirst : 0 < firstNoise) (hsecond : 0 < secondNoise)
    (hcross : secondNoise * (priorVariance + firstNoise) ≠ firstNoise ^ 2) :
    twoStepSequentialKalmanRisk priorVariance firstNoise secondNoise <
      twoStepSequentialConstantGateRisk
        priorVariance firstNoise secondNoise gate :=
  everyConstantGate_strictlySuboptimal_sequential
    priorVariance firstNoise secondNoise gate hprior hfirst hsecond hcross

/-! ## Concrete weighted-evidence fixture -/

/-- A Pure-beta WM-arm fixture whose score visibly consumes weighted evidence,
registered/default retention, gain, and recurrence depth. -/
noncomputable def betaWeightedSelectiveFixture
    (goal : Mettapedia.GSLT.LanguageDef.Pure.Expr) :
    WeightedSelectiveBeliefDecoder (betaAtomicRoot goal) Unit where
  Params := ℝ
  Input := Unit
  parameters := 2
  currentInput := ()
  recurrenceDepth := 3
  evidence := fun _ => ⟨2, 1⟩
  decayRetention := fun _ _ => derivedJumpEvidenceRetention 1 1
  decayRetention_le_one := by
    intro input query
    exact derivedJumpEvidenceRetention_le_one 1 1 (by norm_num) (by norm_num)
  priorVariance := fun _ _ => 1
  jumpVariance := fun _ _ => 1
  priorVariance_pos := by norm_num
  jumpVariance_nonneg := by norm_num
  gain := fun _ _ => 1 / 2
  score := fun parameter payload depth _state action => by
    change RefineAction Nat Nat at action
    exact parameter + (payload.evidence ()).pos.toReal +
      (payload.evidence ()).neg.toReal +
      (payload.decayRetention ()).toReal +
      (payload.derivedDecayDefault ()).toReal + payload.gain () +
      (depth : ℝ) + (action.hole : ℝ) + (action.head : ℝ)

/-- The concrete WM fixture registers exactly the jump-derived default. -/
theorem betaWeightedSelectiveFixture_usesDerivedDecayDefault
    (goal : Mettapedia.GSLT.LanguageDef.Pure.Expr) :
    (betaWeightedSelectiveFixture goal).UsesDerivedDecayDefault := by
  intro input query
  cases input
  cases query
  rfl

/-- The concrete weighted-evidence arm inherits sealed acceptance for
arbitrary trace and program. -/
theorem betaWeightedSelectiveFixture_rankedAccepts_iff_accepts
    (goal : Mettapedia.GSLT.LanguageDef.Pure.Expr)
    {budget : Nat}
    {trace : List (RefineAction (betaAtomicRoot goal).Hole
      (betaAtomicRoot goal).Head)}
    {program : (betaAtomicRoot goal).Program} :
    (betaAtomicRoot goal).asRefinementInterface.RankedAccepts
        (betaWeightedSelectiveFixture goal).toLegalActionWorkspaceDecoder.ranking
        budget trace program ↔
      (betaAtomicRoot goal).asRefinementInterface.Accepts
        budget trace program :=
  (betaWeightedSelectiveFixture goal).rankedAccepts_iff_accepts
    (betaAtomicLaws goal)

/-- Negative evidence boundary: weighted fusion is additive, not idempotent.
Provenance must still prevent accidental replay. -/
theorem duplicateWeightedPacket_not_idempotent :
    (⟨1, 0⟩ : WeightedEvidence) + ⟨1, 0⟩ ≠ ⟨1, 0⟩ := by
  intro heq
  have hpos := congrArg BinaryEvidence.pos heq
  norm_num [BinaryEvidence.hplus_def] at hpos

#print axioms WeightedSelectiveBeliefDecoder.ranking_listsAllLegalActions
#print axioms WeightedSelectiveBeliefDecoder.inheritance
#print axioms WeightedSelectiveBeliefDecoder.derivedDecayDefault_le_one
#print axioms exactGain_equilibrium_iff_posterior
#print axioms inputConditionedGain_sequentialMotivation
#print axioms betaWeightedSelectiveFixture_usesDerivedDecayDefault
#print axioms betaWeightedSelectiveFixture_rankedAccepts_iff_accepts
#print axioms duplicateWeightedPacket_not_idempotent

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
