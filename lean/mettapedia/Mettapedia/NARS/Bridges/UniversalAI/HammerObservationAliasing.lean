import Mettapedia.GSLT.Dynamics.ObservationPolicyFactorization
import Mettapedia.ProbabilityTheory.HiddenMarkovModels.ControlledFiniteHiddenMarkovModel

/-!
# Observation aliasing and the Hammer comparison boundary

Patrick Hammer's controlled experiments in *Reasoning-Learning Systems Based
on Non-Axiomatic Reasoning System Theory* (PMLR 192, 2022) compare OpenNARS
for Applications (ONA) with tabular Q-learning with eligibility traces.  The
original Pong task contains a particularly crisp representation obstruction:
a preceding move continues while the agent does nothing, so the current
visible ball relation does not determine the action-relevant state.  Hammer's
Table 1 reports a larger ONA success ratio on that task, while the simplified
Pong and the reactive tasks are close.

Ali Beikmohammadi and Sindri Magnússon, *Comparing NARS and Reinforcement
Learning: An Analysis of ONA and Q-Learning Algorithms* (2023), provide an
independent comparison on seven OpenAI Gym tasks.  Their results are mixed:
Q-learning is stronger on some tasks and ONA is more promising on the
FrozenLake tasks, particularly the stochastic variants.  Their protocol also
uses a different abstention treatment and, for FlappyBird, different input
encodings.

This file separates three claims that those sources do not identify:

1. a theorem: incompatible action requirements inside one observation fibre
   cannot be met by a policy that sees only that observation;
2. a controlled-HMM witness: action history can change the latent filtering
   state while the current observation remains identical;
3. empirical records: the reported comparisons, including their differing
   protocols and the observed mixed ordering.

The theorem uses the general proof-relevant policy-factorization interface.
It does not assert that ONA universally dominates Q-learning, that every
stochastic process violates the Markov property, or that ONA always discovers
the history-sensitive policy.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.NARS.Bridges.UniversalAI.HammerObservationAliasing

open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.Dynamics
open Mettapedia.ProbabilityTheory.HiddenMarkovModels.ControlledFiniteHiddenMarkovModel
open scoped ENNReal

/-! ## A history-retaining observation discipline -/

abbrev Action := Fin 2
abbrev Observation := Fin 1
abbrev Cycle := CycleObservation Action 1
abbrev History := List Cycle

/-- Retain the complete chronological action-observation history. -/
def historyCollector : WitnessCollector Cycle where
  Container := History
  collect := some

/-- The last visible observation, deliberately forgetting the preceding
action history. -/
def currentObservation (history : History) : Option Observation :=
  history.getLast?.map Prod.snd

/-- Exact history is the informative witness container; current observation
is one lossy readout from it. -/
def currentObservationDiscipline : ObservationDiscipline Cycle where
  collection := historyCollector
  Value := Option Observation
  readout := currentObservation

/-- The one-step histories representing two different continuing motions with
the same current visible observation. -/
def leftHistory : History := [((0 : Action), (0 : Observation))]

def rightHistory : History := [((1 : Action), (0 : Observation))]

@[simp] theorem currentObservation_leftHistory :
    currentObservation leftHistory = some 0 := by
  rfl

@[simp] theorem currentObservation_rightHistory :
    currentObservation rightHistory = some 0 := by
  rfl

/-- A minimal continuation requirement: retain the direction named by the
last action.  This is a mathematical canary for Hammer's continuing-movement
Pong mechanism, not a complete model of Pong or ONA. -/
def requiredContinuation (history : History) : Action :=
  match history.getLast? with
  | none => 0
  | some (action, _) => action

/-- Proof-relevant evidence that a chosen action meets the continuation
requirement at a history. -/
abbrev ContinuationAdmissible (history : History) (decision : Action) : Type 0 :=
  PLift (decision = requiredContinuation history)

@[simp] theorem requiredContinuation_leftHistory :
    requiredContinuation leftHistory = 0 := by
  rfl

@[simp] theorem requiredContinuation_rightHistory :
    requiredContinuation rightHistory = 1 := by
  rfl

/-- The two histories form one observation fibre, but no action is admissible
at both ends. -/
def continuationIncompatibleFiber :
    currentObservationDiscipline.IncompatibleDecisionFiber
      ContinuationAdmissible where
  left := leftHistory
  right := rightHistory
  sameReadout := rfl
  incompatible := by
    intro decision
    constructor
    rintro ⟨leftAdmissible, rightAdmissible⟩
    have impossible : (0 : Action) = 1 :=
      leftAdmissible.down.symm.trans rightAdmissible.down
    exact Fin.zero_ne_one impossible

/-- No deterministic policy seeing only the current observation can meet both
continuation requirements. -/
theorem no_currentObservationPolicy_realizes_continuation
    (policy : Option Observation → Action) :
    IsEmpty
      (currentObservationDiscipline.ReadoutPolicyRealization
        ContinuationAdmissible policy) :=
  continuationIncompatibleFiber.no_readoutPolicyRealization policy

/-- Retaining history is sufficient for the canary specification. -/
def requiredContinuationRealization :
    currentObservationDiscipline.PolicyRealization
      ContinuationAdmissible requiredContinuation := by
  intro history
  exact ⟨rfl⟩

/-- Consequently, the successful history policy cannot be reconstructed from
the current-observation readout. -/
theorem requiredContinuation_not_supported_by_currentObservation :
    ¬ currentObservationDiscipline.SupportsPolicy requiredContinuation :=
  continuationIncompatibleFiber.realizingPolicy_not_supported
    requiredContinuation requiredContinuationRealization

/-- Loss of history does not make every policy impossible: a constant policy
still factors through the current-observation readout.  The obstruction is
decision-relative, not a slogan that partial observation is always harmful. -/
theorem constantPolicy_supported_by_currentObservation :
    currentObservationDiscipline.SupportsPolicy (fun _ : History => (0 : Action)) := by
  exact ⟨fun _ => 0, fun _ => rfl⟩

/-! ## Controlled hidden-state witness -/

private def diracPM {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (value : α) : MeasureTheory.ProbabilityMeasure α :=
  ⟨MeasureTheory.Measure.dirac value,
    MeasureTheory.Measure.dirac.isProbabilityMeasure⟩

@[simp] private theorem diracPM_toMeasure_singleton
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [DecidableEq α] (value point : α) :
    ((diracPM value : MeasureTheory.Measure α) (Set.singleton point)) =
      if value = point then 1 else 0 := by
  change MeasureTheory.Measure.dirac value ({point} : Set α) =
    if value = point then 1 else 0
  rw [MeasureTheory.Measure.dirac_apply]
  by_cases same : value = point
  · subst same
    rw [Set.indicator_of_mem]
    · simp
    · exact Set.mem_singleton _
  · have notMem : value ∉ ({point} : Set α) := by
      intro member
      exact same (Set.mem_singleton_iff.mp member)
    rw [Set.indicator_of_notMem notMem]
    simp [same]

/-- An action writes one latent motion bit, while both latent states emit the
same visible observation.  This is the smallest controlled-HMM realization of
the aliasing mechanism; it carries no claim about benchmark frequencies. -/
noncomputable def continuationHMM : ControlledFiniteHMMParam Action 2 1 where
  init := diracPM 0
  trans := fun action _ => diracPM action
  emission := fun _ => diracPM 0

@[simp] theorem filteringMass_leftHistory_state0 :
    filteringMass continuationHMM leftHistory 0 = 1 := by
  simp only [leftHistory, filteringMass, filteringMassAux]
  unfold initialLatentMass filteringStepMass
    predictiveLatentMass
  rw [Fin.sum_univ_two]
  simp [continuationHMM, initProb, stepProb, emissionProb]

@[simp] theorem filteringMass_rightHistory_state0 :
    filteringMass continuationHMM rightHistory 0 = 0 := by
  simp only [rightHistory, filteringMass, filteringMassAux]
  unfold initialLatentMass filteringStepMass
    predictiveLatentMass
  rw [Fin.sum_univ_two]
  simp [continuationHMM, initProb, stepProb, emissionProb]

/-- The current observation cannot recover the controlled-HMM filtering
state: the two histories have the same readout and different posterior mass at
latent state `0`. -/
def filteringStateNontrivialFiber :
    NonTrivialFiber currentObservation (filteringMass continuationHMM) where
  left := leftHistory
  right := rightHistory
  sameShadow := rfl
  differentValue := by
    intro sameMass
    have atStateZero := congrFun sameMass (0 : Fin 2)
    rw [filteringMass_leftHistory_state0,
      filteringMass_rightHistory_state0] at atStateZero
    exact one_ne_zero atStateZero

/-- Exact controlled-HMM identifiability boundary. -/
theorem filteringState_not_determined_by_currentObservation :
    ¬ Factors currentObservation (filteringMass continuationHMM) :=
  filteringStateNontrivialFiber.not_factors

/-! ## Source-scoped empirical conformance records -/

inductive Source where
  | hammer2022
  | beikmohammadiMagnusson2023
  deriving DecidableEq, Repr

inductive Benchmark where
  | spaceInvaders
  | pongOriginal
  | pongSimplified
  | gridRobot
  | cliffWalking
  | taxi
  | frozenLake
  | frozenLakeSlippery
  | flappyBird
  deriving DecidableEq, Repr

/-- Regimes remain distinct: stochastic Markov dynamics are not identified
with observation aliasing, and altered input representations are recorded. -/
inductive Regime where
  | reactiveMarkov
  | actionHistoryAliased
  | stochasticMarkov
  | representationAltered
  deriving DecidableEq, Repr

inductive AbstentionTreatment where
  | explicitNothingAction
  | randomActionWhenONAAbstains
  deriving DecidableEq, Repr

inductive InputAlignment where
  | sameStateContent
  | algorithmSpecificEncoding
  deriving DecidableEq, Repr

/-- Experimental protocol fields that materially affect comparison. -/
structure ComparisonProtocol where
  source : Source
  abstention : AbstentionTreatment
  inputAlignment : InputAlignment
  qLearningHyperparametersTuned : Bool
  deriving DecidableEq, Repr

/-- Hammer's 2022 protocol: an explicit no-op was added for the Q-learner and
the ONA defaults were compared with task-specific Q-learning parameters. -/
def hammerProtocol : ComparisonProtocol where
  source := .hammer2022
  abstention := .explicitNothingAction
  inputAlignment := .sameStateContent
  qLearningHyperparametersTuned := true

/-- The independent 2023 protocol: random action on ONA abstention, grid
search for Q-learning, and an algorithm-specific FlappyBird encoding. -/
def replicationProtocol : ComparisonProtocol where
  source := .beikmohammadiMagnusson2023
  abstention := .randomActionWhenONAAbstains
  inputAlignment := .algorithmSpecificEncoding
  qLearningHyperparametersTuned := true

theorem comparisonProtocols_are_distinct :
    hammerProtocol ≠ replicationProtocol := by
  decide

/-- A reported pair of end-performance means.  The numbers are empirical data
attached to a protocol; this structure supplies no theorem that they generalize
to another task or implementation. -/
structure QuantitativeComparison where
  protocol : ComparisonProtocol
  benchmark : Benchmark
  regime : Regime
  onaMean : ℚ
  qLearningMean : ℚ
  trialsPerMethod : ℕ
  deriving Repr

def hammerSpaceInvaders : QuantitativeComparison where
  protocol := hammerProtocol
  benchmark := .spaceInvaders
  regime := .reactiveMarkov
  onaMean := 86 / 100
  qLearningMean := 85 / 100
  trialsPerMethod := 10

def hammerPongOriginal : QuantitativeComparison where
  protocol := hammerProtocol
  benchmark := .pongOriginal
  regime := .actionHistoryAliased
  onaMean := 80 / 100
  qLearningMean := 61 / 100
  trialsPerMethod := 10

def hammerPongSimplified : QuantitativeComparison where
  protocol := hammerProtocol
  benchmark := .pongSimplified
  regime := .reactiveMarkov
  onaMean := 98 / 100
  qLearningMean := 97 / 100
  trialsPerMethod := 10

def hammerGridRobot : QuantitativeComparison where
  protocol := hammerProtocol
  benchmark := .gridRobot
  regime := .reactiveMarkov
  onaMean := 91
  qLearningMean := 87
  trialsPerMethod := 10

theorem hammer_pongOriginal_reported_ONA_higher :
    hammerPongOriginal.qLearningMean < hammerPongOriginal.onaMean := by
  norm_num [hammerPongOriginal]

/-- The two Hammer reactive-game ratios differ by only one percentage point;
this is a statement about the reported table, not an equivalence theorem for
the algorithms. -/
theorem hammer_reactive_ratios_within_one_percent :
    |hammerSpaceInvaders.onaMean - hammerSpaceInvaders.qLearningMean| ≤ 1 / 100 ∧
      |hammerPongSimplified.onaMean - hammerPongSimplified.qLearningMean| ≤
        1 / 100 := by
  norm_num [hammerSpaceInvaders, hammerPongSimplified, abs_of_nonneg]

inductive ReportedDirection where
  | onaHigher
  | qLearningHigher
  deriving DecidableEq, Repr

/-- The independent study reports task-level direction without supplying a
single scalar table suitable for exact transcription from its plots. -/
structure QualitativeComparison where
  protocol : ComparisonProtocol
  benchmark : Benchmark
  regime : Regime
  direction : ReportedDirection
  deriving DecidableEq, Repr

def replicationCliffWalking : QualitativeComparison where
  protocol := replicationProtocol
  benchmark := .cliffWalking
  regime := .reactiveMarkov
  direction := .qLearningHigher

def replicationFrozenLakeSlippery : QualitativeComparison where
  protocol := replicationProtocol
  benchmark := .frozenLakeSlippery
  regime := .stochasticMarkov
  direction := .onaHigher

/-- The independent empirical anchor contains both orderings.  Therefore its
own reported task set cannot witness universal dominance by either method. -/
theorem replication_reports_mixed_ordering :
    replicationCliffWalking.direction = .qLearningHigher ∧
      replicationFrozenLakeSlippery.direction = .onaHigher := by
  exact ⟨rfl, rfl⟩

/-- Stochastic Markov dynamics and action-history aliasing are distinct
regime tags.  The replication's slippery FrozenLake evidence must not be
silently relabeled as the mechanism in Hammer's original Pong experiment. -/
theorem stochasticMarkov_ne_actionHistoryAliased :
    Regime.stochasticMarkov ≠ Regime.actionHistoryAliased := by
  decide

#print axioms no_currentObservationPolicy_realizes_continuation
#print axioms requiredContinuationRealization
#print axioms requiredContinuation_not_supported_by_currentObservation
#print axioms constantPolicy_supported_by_currentObservation
#print axioms filteringMass_leftHistory_state0
#print axioms filteringMass_rightHistory_state0
#print axioms filteringState_not_determined_by_currentObservation
#print axioms comparisonProtocols_are_distinct
#print axioms hammer_pongOriginal_reported_ONA_higher
#print axioms hammer_reactive_ratios_within_one_percent
#print axioms replication_reports_mixed_ordering
#print axioms stochasticMarkov_ne_actionHistoryAliased

end Mettapedia.NARS.Bridges.UniversalAI.HammerObservationAliasing
