import Mettapedia.OSLF.Framework.WMCalculusPatternDenotation
import Mettapedia.OSLF.Framework.WMCalculusVertexOrder
import Mettapedia.OSLF.Framework.WMCalculusContextClosure
import Mettapedia.PLN.WorldModel.PLNWorldModelSupportForgetting
import Mettapedia.PLN.WorldModel.WorldModelConservationPack
import Mettapedia.PLN.WorldModel.OrderCost.PLNWorldModelOrderCostBounds
import Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointCascade
import Mettapedia.PLN.WorldModel.Experiment.PLNWorldModelExperiment
import Mettapedia.PLN.WorldModel.Experiment.PLNWorldModelExperimentStochastic
import Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization

/-!
# Denotational soundness of the WM calculus

A `WMModel` is a world model for every axis of the maximal vertex, assembled
from the PLN world-model layers:

* the core: an additive world model whose evidence carrier counts observations;
* forgetting: a support-tracked forgetting layer, with zero preservation for the
  conservation pack;
* overlap: an overlap layer, whose merge also drives the order costs;
* provenance: a source-compatibility relation and trust policies, with partial
  and fallback revision defined from compatibility as in the Kripke provenance
  layer;
* fixpoint: rule closure over a binary world model of its own queries;
* experiments: deterministic channels on a multiset of hypotheses, and finite
  stochastic channels, priors, decision rules and utilities on weighted states;
* Kripke: a crisp satisfaction relation on points, read by counting the points
  of a state (`crispEvidence`, the Kripke world model when the points are
  pointed Kripke models);
* counting evidence, embedded in the evidence carrier by an additive map.

`denote` (through `algebra`) reads every constructor of the calculus as the
corresponding operation, and `meaning` reads every relation that a premise
queries.  Every rule of the maximal vertex and every congruence rule is valid
(`maximalRules_valid`, `congruenceRules_valid`), so under any environment that
certifies `meaning`, every step of every vertex's calculus and of its
congruence closure preserves the denotation (`wmFull_step_sound`,
`wmFullWithCong_step_sound`, `wmExtWithCong_step_sound`).

Four constructors have no denotation here: the truth-value views `Strength`,
`LowerBound` and `UpperBound` (the evidence carrier is a counting monoid without
a strength map, and no rule uses them), and `ForgetSources` (a trust policy
names the sources it keeps, not the ones it drops, and no rule uses it).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusDenotationalSoundness

open scoped ENNReal
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.WMCalculusVertexOrder
open Mettapedia.OSLF.Framework.PLNWMHypercubeBasis
open Mettapedia.OSLF.Framework.WMCalculusPatternDenotation
open Mettapedia.PLN.Evidence
open Mettapedia.PLN.Evidence.EvidenceClass (EvidenceType)
open Mettapedia.PLN.Bridges.ProbabilityTheory.ConjugateEvidenceCore (ConjugateEvidence)
open Mettapedia.PLN.WorldModel
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric (AdditiveWorldModel)
open Mettapedia.PLN.WorldModel.GenericWorldModelForgetting
  (ForgettingLayer GenericWorldModelZeroPreserving)
open Mettapedia.PLN.WorldModel.PLNWorldModelSupportForgetting (SupportTrackedForgettingLayer)
open Mettapedia.PLN.WorldModel.WorldModelConservationPack (OutsideLeakageBudget)
open Mettapedia.PLN.WorldModel.WorldModelOverlap (OverlapLayer)
open Mettapedia.PLN.WorldModel.OrderCost
  (SwapAnomalyCount scheduleErrorCount runMergeSchedule)
open Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure
  (RuleSet immediateStep leastRuleClosure immediateIter)
open Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization (crispEvidence crispWorldModel)

namespace Det
export Mettapedia.PLN.WorldModel.Experiment.PLNWorldModelExperiment
  (ExperimentChannel ExperimentQuery experimentEvidence pullbackQuery BlackwellFactorsThrough)
end Det

namespace Stoch
export Mettapedia.PLN.WorldModel.Experiment.PLNWorldModelExperimentStochastic
  (StochasticChannel StochasticExperimentQuery stochasticEvidence stochasticComp stochasticId
    DecisionRule liftDecision expectedUtility optimalValue BlackwellFactorsThrough)
end Stoch

/-! ## The model -/

section Model

variable (State Query Ev : Type) [EvidenceType State] [ConjugateEvidence Ev]
  [AdditiveWorldModel State Query Ev]

/-- A world model for every axis of the maximal vertex.  Its fields are the PLN
layers, plus the four structural facts the provenance and Kripke axes need:
compatibility is symmetric, the all-trusting policy keeps every state, and a
singleton state has exactly its point. -/
structure WMModel where
  Scope : Type
  Supp : Type
  forgetting : SupportTrackedForgettingLayer State Scope Query Ev Supp
  zeroPreserving : GenericWorldModelZeroPreserving (State := State) (Query := Query) (Ev := Ev)
  Ov : Type
  overlap : OverlapLayer State Query Ev Ov
  compatible : State → State → Prop
  compatible_symm : ∀ {first second : State}, compatible first second → compatible second first
  Policy : Type
  gate : Policy → State → State
  trustAll : Policy
  gate_trustAll : ∀ W, gate trustAll W = W
  FQuery : Type
  fixpointModel : BinaryWorldModel State FQuery
  Θ : Type
  Ω : Type
  Act : Type
  fintypeΘ : Fintype Θ
  fintypeΩ : Fintype Ω
  fintypeAct : Fintype Act
  hypotheses : State →+ Multiset Θ
  weights : State →+ (Θ → ℝ≥0∞)
  Point : Type
  ModalQuery : Type
  satisfies : Point → ModalQuery → Prop
  points : State →+ Multiset Point
  singleton : Point → State
  points_singleton : ∀ point, points (singleton point) = {point}
  ofBinary : BinaryEvidence →+ Ev

variable {State Query Ev}

instance (M : WMModel State Query Ev) : BinaryWorldModel State M.FQuery := M.fixpointModel
instance (M : WMModel State Query Ev) : Fintype M.Θ := M.fintypeΘ
instance (M : WMModel State Query Ev) : Fintype M.Ω := M.fintypeΩ
instance (M : WMModel State Query Ev) : Fintype M.Act := M.fintypeAct

/-- Partial revision: additive when the states are compatible, undefined
otherwise (as `partialRevision` in the Kripke provenance layer). -/
noncomputable def WMModel.partialRevision (M : WMModel State Query Ev) (first second : State) :
    Option State := by
  classical
  exact if M.compatible first second then some (first + second) else none

/-- Fallback revision: partial revision, or the left state when it is undefined. -/
noncomputable def WMModel.fallbackRevision (M : WMModel State Query Ev) (first second : State) :
    State :=
  (M.partialRevision first second).getD first

theorem WMModel.partialRevision_of_compatible (M : WMModel State Query Ev) {first second : State}
    (compatible : M.compatible first second) :
    M.partialRevision first second = some (first + second) := by
  classical
  simp [WMModel.partialRevision, compatible]

theorem WMModel.fallbackRevision_of_compatible (M : WMModel State Query Ev)
    {first second : State} (compatible : M.compatible first second) :
    M.fallbackRevision first second = first + second := by
  simp [WMModel.fallbackRevision, M.partialRevision_of_compatible compatible]

theorem WMModel.fallbackRevision_of_not_compatible (M : WMModel State Query Ev)
    {first second : State} (incompatible : ¬ M.compatible first second) :
    M.fallbackRevision first second = first := by
  classical
  simp [WMModel.fallbackRevision, WMModel.partialRevision, incompatible]

/-! ## Values -/

/-- Values of the sorts of the calculus. -/
inductive WMValue (M : WMModel State Query Ev) where
  | state : State → WMValue M
  | query : Query → WMValue M
  | evidence : Ev → WMValue M
  | scope : M.Scope → WMValue M
  | overlap : M.Ov → WMValue M
  | proposition : Prop → WMValue M
  | policy : M.Policy → WMValue M
  | ruleSet : RuleSet State M.FQuery → WMValue M
  | querySet : Set M.FQuery → WMValue M
  | natural : ℕ → WMValue M
  | querySpace : Finset M.FQuery → WMValue M
  | cost : ℝ≥0∞ → WMValue M
  | schedule : List State → WMValue M
  | channel : Det.ExperimentChannel M.Θ M.Ω → WMValue M
  | garbling : (M.Ω → M.Ω) → WMValue M
  | experimentQuery : Det.ExperimentQuery M.Θ M.Ω → WMValue M
  | stochasticChannel : Stoch.StochasticChannel M.Θ M.Ω → WMValue M
  | stochasticGarbling : Stoch.StochasticChannel M.Ω M.Ω → WMValue M
  | stochasticQuery : Stoch.StochasticExperimentQuery M.Θ M.Ω → WMValue M
  | prior : PMF M.Θ → WMValue M
  | decision : Stoch.DecisionRule M.Ω M.Act → WMValue M
  | utility : (M.Θ → M.Act → ℝ≥0∞) → WMValue M
  | point : M.Point → WMValue M
  | modalQuery : M.ModalQuery → WMValue M

variable {M : WMModel State Query Ev}

namespace WMValue

/-- Sort projections. -/
def asState : WMValue M → Option State | .state x => some x | _ => none
def asQuery : WMValue M → Option Query | .query x => some x | _ => none
def asEvidence : WMValue M → Option Ev | .evidence x => some x | _ => none
def asScope : WMValue M → Option M.Scope | .scope x => some x | _ => none
def asOverlap : WMValue M → Option M.Ov | .overlap x => some x | _ => none
def asPolicy : WMValue M → Option M.Policy | .policy x => some x | _ => none
def asRuleSet : WMValue M → Option (RuleSet State M.FQuery) | .ruleSet x => some x | _ => none
def asQuerySet : WMValue M → Option (Set M.FQuery) | .querySet x => some x | _ => none
def asNatural : WMValue M → Option ℕ | .natural x => some x | _ => none
def asQuerySpace : WMValue M → Option (Finset M.FQuery) | .querySpace x => some x | _ => none
def asSchedule : WMValue M → Option (List State) | .schedule x => some x | _ => none
def asChannel : WMValue M → Option (Det.ExperimentChannel M.Θ M.Ω)
  | .channel x => some x | _ => none
def asGarbling : WMValue M → Option (M.Ω → M.Ω) | .garbling x => some x | _ => none
def asExperimentQuery : WMValue M → Option (Det.ExperimentQuery M.Θ M.Ω)
  | .experimentQuery x => some x | _ => none
def asStochasticChannel : WMValue M → Option (Stoch.StochasticChannel M.Θ M.Ω)
  | .stochasticChannel x => some x | _ => none
def asStochasticGarbling : WMValue M → Option (Stoch.StochasticChannel M.Ω M.Ω)
  | .stochasticGarbling x => some x | _ => none
def asStochasticQuery : WMValue M → Option (Stoch.StochasticExperimentQuery M.Θ M.Ω)
  | .stochasticQuery x => some x | _ => none
def asPrior : WMValue M → Option (PMF M.Θ) | .prior x => some x | _ => none
def asDecision : WMValue M → Option (Stoch.DecisionRule M.Ω M.Act)
  | .decision x => some x | _ => none
def asUtility : WMValue M → Option (M.Θ → M.Act → ℝ≥0∞) | .utility x => some x | _ => none
def asPoint : WMValue M → Option M.Point | .point x => some x | _ => none
def asModalQuery : WMValue M → Option M.ModalQuery | .modalQuery x => some x | _ => none

@[simp] theorem asState_eq_some {v : WMValue M} {x : State} :
    v.asState = some x ↔ v = .state x := by cases v <;> simp [asState]
@[simp] theorem asQuery_eq_some {v : WMValue M} {x : Query} :
    v.asQuery = some x ↔ v = .query x := by cases v <;> simp [asQuery]
@[simp] theorem asEvidence_eq_some {v : WMValue M} {x : Ev} :
    v.asEvidence = some x ↔ v = .evidence x := by cases v <;> simp [asEvidence]
@[simp] theorem asScope_eq_some {v : WMValue M} {x : M.Scope} :
    v.asScope = some x ↔ v = .scope x := by cases v <;> simp [asScope]
@[simp] theorem asOverlap_eq_some {v : WMValue M} {x : M.Ov} :
    v.asOverlap = some x ↔ v = .overlap x := by cases v <;> simp [asOverlap]
@[simp] theorem asPolicy_eq_some {v : WMValue M} {x : M.Policy} :
    v.asPolicy = some x ↔ v = .policy x := by cases v <;> simp [asPolicy]
@[simp] theorem asRuleSet_eq_some {v : WMValue M} {x : RuleSet State M.FQuery} :
    v.asRuleSet = some x ↔ v = .ruleSet x := by cases v <;> simp [asRuleSet]
@[simp] theorem asQuerySet_eq_some {v : WMValue M} {x : Set M.FQuery} :
    v.asQuerySet = some x ↔ v = .querySet x := by cases v <;> simp [asQuerySet]
@[simp] theorem asNatural_eq_some {v : WMValue M} {x : ℕ} :
    v.asNatural = some x ↔ v = .natural x := by cases v <;> simp [asNatural]
@[simp] theorem asQuerySpace_eq_some {v : WMValue M} {x : Finset M.FQuery} :
    v.asQuerySpace = some x ↔ v = .querySpace x := by cases v <;> simp [asQuerySpace]
@[simp] theorem asSchedule_eq_some {v : WMValue M} {x : List State} :
    v.asSchedule = some x ↔ v = .schedule x := by cases v <;> simp [asSchedule]
@[simp] theorem asChannel_eq_some {v : WMValue M} {x : Det.ExperimentChannel M.Θ M.Ω} :
    v.asChannel = some x ↔ v = .channel x := by cases v <;> simp [asChannel]
@[simp] theorem asGarbling_eq_some {v : WMValue M} {x : M.Ω → M.Ω} :
    v.asGarbling = some x ↔ v = .garbling x := by cases v <;> simp [asGarbling]
@[simp] theorem asExperimentQuery_eq_some {v : WMValue M} {x : Det.ExperimentQuery M.Θ M.Ω} :
    v.asExperimentQuery = some x ↔ v = .experimentQuery x := by
  cases v <;> simp [asExperimentQuery]
@[simp] theorem asStochasticChannel_eq_some {v : WMValue M}
    {x : Stoch.StochasticChannel M.Θ M.Ω} :
    v.asStochasticChannel = some x ↔ v = .stochasticChannel x := by
  cases v <;> simp [asStochasticChannel]
@[simp] theorem asStochasticGarbling_eq_some {v : WMValue M}
    {x : Stoch.StochasticChannel M.Ω M.Ω} :
    v.asStochasticGarbling = some x ↔ v = .stochasticGarbling x := by
  cases v <;> simp [asStochasticGarbling]
@[simp] theorem asStochasticQuery_eq_some {v : WMValue M}
    {x : Stoch.StochasticExperimentQuery M.Θ M.Ω} :
    v.asStochasticQuery = some x ↔ v = .stochasticQuery x := by
  cases v <;> simp [asStochasticQuery]
@[simp] theorem asPrior_eq_some {v : WMValue M} {x : PMF M.Θ} :
    v.asPrior = some x ↔ v = .prior x := by cases v <;> simp [asPrior]
@[simp] theorem asDecision_eq_some {v : WMValue M} {x : Stoch.DecisionRule M.Ω M.Act} :
    v.asDecision = some x ↔ v = .decision x := by cases v <;> simp [asDecision]
@[simp] theorem asUtility_eq_some {v : WMValue M} {x : M.Θ → M.Act → ℝ≥0∞} :
    v.asUtility = some x ↔ v = .utility x := by cases v <;> simp [asUtility]
@[simp] theorem asPoint_eq_some {v : WMValue M} {x : M.Point} :
    v.asPoint = some x ↔ v = .point x := by cases v <;> simp [asPoint]
@[simp] theorem asModalQuery_eq_some {v : WMValue M} {x : M.ModalQuery} :
    v.asModalQuery = some x ↔ v = .modalQuery x := by cases v <;> simp [asModalQuery]

/-- Channel composition, first the left channel and then the right garbling,
within the deterministic and within the stochastic channels. -/
noncomputable def compose : WMValue M → WMValue M → Option (WMValue M)
  | .channel first, second => second.asGarbling.map fun g => .channel ⟨g ∘ first.run⟩
  | .garbling first, second => second.asGarbling.map fun g => .garbling (g ∘ first)
  | .stochasticChannel first, second =>
      second.asStochasticGarbling.map fun g => .stochasticChannel (Stoch.stochasticComp first g)
  | .stochasticGarbling first, second =>
      second.asStochasticGarbling.map fun g => .stochasticGarbling (Stoch.stochasticComp first g)
  | _, _ => none

end WMValue

end Model

/-! ## Constructors as operations

Labels are parsed once into `WMLabel`, so that reading a constructor unfolds a
match on an inductive type rather than a chain of string comparisons. -/

/-- The constructor labels of the calculus that the model reads. -/
inductive WMLabel where
  | revise | extract | combine | evidenceZero | evidenceOne | evidenceOneNegative
  | overlapMerge | overlapFactor | overlapCorrect | forget
  | sourceCompatible | partialRevision | fallbackRevision | trustedGate | trustedAll
  | policyRevisedState
  | immediateStep | leastClosure | immediateIter | succ | card
  | swapAnomaly | scheduleError | runSchedule | costZero | leakageBudget
  | experimentEvidence | blackwellPullback | channelComp | channelId
  | stochEvidence | expectedUtility | optimalValue | liftPolicy | stochId
  | kripkeEvidence | singleton | genericEvidence
  deriving DecidableEq

/-- The label a constructor name spells, if the model reads it. -/
def WMLabel.parse : String → Option WMLabel
  | "Revise" => some .revise
  | "Extract" => some .extract
  | "Combine" => some .combine
  | "EvidenceZero" => some .evidenceZero
  | "EvidenceOne" => some .evidenceOne
  | "EvidenceOneNegative" => some .evidenceOneNegative
  | "OverlapMerge" => some .overlapMerge
  | "OverlapFactor" => some .overlapFactor
  | "OverlapCorrect" => some .overlapCorrect
  | "Forget" => some .forget
  | "SourceCompatible" => some .sourceCompatible
  | "PartialRevision" => some .partialRevision
  | "FallbackRevision" => some .fallbackRevision
  | "TrustedGate" => some .trustedGate
  | "TrustedAll" => some .trustedAll
  | "PolicyRevisedState" => some .policyRevisedState
  | "ImmediateStep" => some .immediateStep
  | "LeastClosure" => some .leastClosure
  | "ImmediateIter" => some .immediateIter
  | "Succ" => some .succ
  | "Card" => some .card
  | "SwapAnomaly" => some .swapAnomaly
  | "ScheduleError" => some .scheduleError
  | "RunSchedule" => some .runSchedule
  | "CostZero" => some .costZero
  | "LeakageBudget" => some .leakageBudget
  | "ExperimentEvidence" => some .experimentEvidence
  | "BlackwellPullback" => some .blackwellPullback
  | "ChannelComp" => some .channelComp
  | "ChannelId" => some .channelId
  | "StochEvidence" => some .stochEvidence
  | "ExpectedUtility" => some .expectedUtility
  | "OptimalValue" => some .optimalValue
  | "LiftPolicy" => some .liftPolicy
  | "StochId" => some .stochId
  | "KripkeEvidence" => some .kripkeEvidence
  | "Singleton" => some .singleton
  | "GenericEvidence" => some .genericEvidence
  | _ => none

section Algebra

variable {State Query Ev : Type} [EvidenceType State] [ConjugateEvidence Ev]
  [AdditiveWorldModel State Query Ev]
variable (M : WMModel State Query Ev)

open WMValue

/-- An operation of a fixed arity, read on argument lists. -/
def arity0 (value : Option (WMValue M)) : List (WMValue M) → Option (WMValue M)
  | [] => value
  | _ => none

def arity1 (f : WMValue M → Option (WMValue M)) : List (WMValue M) → Option (WMValue M)
  | [a] => f a
  | _ => none

def arity2 (f : WMValue M → WMValue M → Option (WMValue M)) :
    List (WMValue M) → Option (WMValue M)
  | [a, b] => f a b
  | _ => none

def arity3 (f : WMValue M → WMValue M → WMValue M → Option (WMValue M)) :
    List (WMValue M) → Option (WMValue M)
  | [a, b, c] => f a b c
  | _ => none

def arity4 (f : WMValue M → WMValue M → WMValue M → WMValue M → Option (WMValue M)) :
    List (WMValue M) → Option (WMValue M)
  | [a, b, c, d] => f a b c d
  | _ => none

/-- The operation a label denotes. -/
noncomputable def opAt : WMLabel → List (WMValue M) → Option (WMValue M)
  | .revise => arity2 M fun a b => do
      let x ← a.asState; let y ← b.asState; pure (.state (x + y))
  | .extract => arity2 M fun w q => do
      let x ← w.asState; let y ← q.asQuery
      pure (.evidence (AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) x y))
  | .combine => arity2 M fun a b => do
      let x ← a.asEvidence; let y ← b.asEvidence; pure (.evidence (x + y))
  | .evidenceZero => arity0 M (some (.evidence 0))
  | .evidenceOne => arity0 M (some (.evidence (M.ofBinary ⟨1, 0⟩)))
  | .evidenceOneNegative => arity0 M (some (.evidence (M.ofBinary ⟨0, 1⟩)))
  | .overlapMerge => arity2 M fun a b => do
      let x ← a.asState; let y ← b.asState; pure (.state (M.overlap.merge x y))
  | .overlapFactor => arity3 M fun a b q => do
      let x ← a.asState; let y ← b.asState; let z ← q.asQuery
      pure (.overlap (M.overlap.overlap x y z))
  | .overlapCorrect => arity3 M fun a b o => do
      let x ← a.asEvidence; let y ← b.asEvidence; let z ← o.asOverlap
      pure (.evidence (M.overlap.combine x y z))
  | .forget => arity2 M fun s w => do
      let x ← s.asScope; let y ← w.asState; pure (.state (M.forgetting.forget x y))
  | .sourceCompatible => arity2 M fun a b => do
      let x ← a.asState; let y ← b.asState; pure (.proposition (M.compatible x y))
  | .partialRevision => arity2 M fun a b => do
      let x ← a.asState; let y ← b.asState
      (M.partialRevision x y).map WMValue.state
  | .fallbackRevision => arity2 M fun a b => do
      let x ← a.asState; let y ← b.asState; pure (.state (M.fallbackRevision x y))
  | .trustedGate => arity2 M fun p w => do
      let x ← p.asPolicy; let y ← w.asState; pure (.state (M.gate x y))
  | .trustedAll => arity0 M (some (.policy M.trustAll))
  | .policyRevisedState => arity3 M fun p a b => do
      let x ← p.asPolicy; let y ← a.asState; let z ← b.asState
      pure (.state (M.gate x (M.fallbackRevision y z)))
  | .immediateStep => arity4 M fun r w seed current => do
      let x ← r.asRuleSet; let y ← w.asState; let z ← seed.asQuerySet
      let c ← current.asQuerySet
      pure (.querySet (immediateStep (State := State) (Query := M.FQuery) x y z c))
  | .leastClosure => arity3 M fun r w seed => do
      let x ← r.asRuleSet; let y ← w.asState; let z ← seed.asQuerySet
      pure (.querySet (leastRuleClosure (State := State) (Query := M.FQuery) x y z))
  | .immediateIter => arity4 M fun r w seed n => do
      let x ← r.asRuleSet; let y ← w.asState; let z ← seed.asQuerySet; let k ← n.asNatural
      pure (.querySet (immediateIter (State := State) (Query := M.FQuery) x y z k))
  | .succ => arity1 M fun n => do let k ← n.asNatural; pure (.natural (k + 1))
  | .card => arity1 M fun q => do let s ← q.asQuerySpace; pure (.natural s.card)
  | .swapAnomaly => arity3 M fun a b q => do
      let x ← a.asState; let y ← b.asState; let z ← q.asQuery
      pure (.cost (SwapAnomalyCount (State := State) (Query := Query) (Ev := Ev) M.overlap x y z))
  | .scheduleError => arity4 M fun b s₁ s₂ q => do
      let x ← b.asState; let y ← s₁.asSchedule; let z ← s₂.asSchedule; let w ← q.asQuery
      pure (.cost (scheduleErrorCount (State := State) (Query := Query) (Ev := Ev)
        M.overlap x y z w))
  | .runSchedule => arity2 M fun b s => do
      let x ← b.asState; let y ← s.asSchedule
      pure (.state (runMergeSchedule (State := State) (Query := Query) (Ev := Ev) M.overlap x y))
  | .costZero => arity0 M (some (.cost 0))
  | .leakageBudget => arity3 M fun s d e => do
      let x ← s.asScope; let y ← d.asState; let z ← e.asEvidence
      pure (.proposition (OutsideLeakageBudget M.forgetting.toForgettingLayer x y
        (ConjugateEvidence.observationCount z)))
  | .experimentEvidence => arity2 M fun w q => do
      let x ← w.asState; let y ← q.asExperimentQuery
      pure (.evidence (M.ofBinary (Det.experimentEvidence (M.hypotheses x) y)))
  | .blackwellPullback => arity3 M fun s k q => do
      let x ← s.asChannel; let y ← k.asGarbling; let z ← q.asExperimentQuery
      pure (.experimentQuery (Det.pullbackQuery x y z.outcome))
  | .channelComp => arity2 M fun a b => compose a b
  | .channelId => arity0 M (some (.garbling id))
  | .stochEvidence => arity2 M fun w q => do
      let x ← w.asState; let y ← q.asStochasticQuery
      pure (.evidence (M.ofBinary (Stoch.stochasticEvidence (M.weights x) y)))
  | .expectedUtility => arity4 M fun p c d u => do
      let x ← p.asPrior; let y ← c.asStochasticChannel; let z ← d.asDecision
      let w ← u.asUtility
      pure (.cost (Stoch.expectedUtility x y z w))
  | .optimalValue => arity3 M fun p c u => do
      let x ← p.asPrior; let y ← c.asStochasticChannel; let w ← u.asUtility
      pure (.cost (Stoch.optimalValue x y w))
  | .liftPolicy => arity2 M fun k d => do
      let x ← k.asStochasticGarbling; let y ← d.asDecision
      pure (.decision (Stoch.liftDecision x y))
  | .stochId => arity0 M (some (.stochasticGarbling (Stoch.stochasticId M.Ω)))
  | .kripkeEvidence => arity2 M fun w φ => do
      let x ← w.asState; let y ← φ.asModalQuery
      pure (.evidence (M.ofBinary (crispEvidence M.satisfies (M.points x) y)))
  | .singleton => arity1 M fun p => do let x ← p.asPoint; pure (.state (M.singleton x))
  | .genericEvidence => arity2 M fun w q => do
      let x ← w.asState; let y ← q.asQuery
      pure (.evidence (AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) x y))

/-- The operation a constructor name denotes: none for names the model does not
read. -/
noncomputable def op (label : String) (args : List (WMValue M)) : Option (WMValue M) :=
  match WMLabel.parse label with
  | some parsed => opAt M parsed args
  | none => none

/-- The calculus's constructors read in the model. -/
noncomputable def algebra : PatternAlgebra (WMValue M) where
  op := op M

theorem algebra_op_of_parse {label : String} {parsed : WMLabel}
    (parse : WMLabel.parse label = some parsed) :
    (algebra M).op label = opAt M parsed := by
  funext args
  simp [algebra, op, parse]

/-- The relations the premises query. -/
inductive WMRelation where
  | outsideScope | erasesInScope | supportedInScope | cleanForScope
  | sourceCompatible | notSourceCompatible | querySpaceOf | equalCounts
  | blackwellQueryFactors | blackwellFactors | kripkeSat | kripkeNotSat | queryEquiv
  deriving DecidableEq

def WMRelation.parse : String → Option WMRelation
  | "outsideScope" => some .outsideScope
  | "erasesInScope" => some .erasesInScope
  | "supportedInScope" => some .supportedInScope
  | "cleanForScope" => some .cleanForScope
  | "sourceCompatible" => some .sourceCompatible
  | "notSourceCompatible" => some .notSourceCompatible
  | "querySpaceOf" => some .querySpaceOf
  | "equalCounts" => some .equalCounts
  | "blackwellQueryFactors" => some .blackwellQueryFactors
  | "blackwellFactors" => some .blackwellFactors
  | "kripkeSat" => some .kripkeSat
  | "kripkeNotSat" => some .kripkeNotSat
  | "queryEquiv" => some .queryEquiv
  | _ => none

/-- What each relation relates, read in the model. -/
def meaningAt : WMRelation → List (WMValue M) → Prop
  | .outsideScope, [s, q] =>
      ∃ S x, s = .scope S ∧ q = .query x ∧ ¬ M.forgetting.inScope S x
  | .erasesInScope, [s, d] =>
      ∃ S Δ, s = .scope S ∧ d = .state Δ ∧ M.forgetting.forget S Δ = 0
  | .supportedInScope, [s, d] =>
      ∃ S Δ, s = .scope S ∧ d = .state Δ ∧ M.forgetting.Supported S Δ
  | .cleanForScope, [s, w] =>
      ∃ S W, s = .scope S ∧ w = .state W ∧ M.forgetting.Clean S W
  | .sourceCompatible, [a, b] =>
      ∃ x y, a = .state x ∧ b = .state y ∧ M.compatible x y
  | .notSourceCompatible, [a, b] =>
      ∃ x y, a = .state x ∧ b = .state y ∧ ¬ M.compatible x y
  | .querySpaceOf, [r, q] =>
      ∃ R Q, r = .ruleSet R ∧ q = .querySpace Q ∧ ∀ query, query ∈ Q
  | .equalCounts, [a, b, q] =>
      ∃ x y z, a = .state x ∧ b = .state y ∧ q = .query z ∧
        AdditiveWorldModel.queryObservationCount (State := State) (Query := Query) (Ev := Ev)
            (M.overlap.merge x y) z =
          AdditiveWorldModel.queryObservationCount (State := State) (Query := Query) (Ev := Ev)
            (M.overlap.merge y x) z
  | .blackwellQueryFactors, [q, s, k] =>
      ∃ query strong κ, q = .experimentQuery query ∧ s = .channel strong ∧ k = .garbling κ ∧
        Det.BlackwellFactorsThrough strong query.channel κ
  | .blackwellFactors, [w, s, k] =>
      ∃ weak strong κ, w = .stochasticChannel weak ∧ s = .stochasticChannel strong ∧
        k = .stochasticGarbling κ ∧ Stoch.BlackwellFactorsThrough strong weak κ
  | .kripkeSat, [p, φ] => ∃ x y, p = .point x ∧ φ = .modalQuery y ∧ M.satisfies x y
  | .kripkeNotSat, [p, φ] => ∃ x y, p = .point x ∧ φ = .modalQuery y ∧ ¬ M.satisfies x y
  | .queryEquiv, [a, b] =>
      ∃ x y, a = .query x ∧ b = .query y ∧
        ∀ W, AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) W x =
          AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) W y
  | _, _ => False

/-- The relation each premise queries, read in the model; names the model does
not read relate nothing. -/
def meaning : RelationMeaning (WMValue M) := fun relation values =>
  match WMRelation.parse relation with
  | some parsed => meaningAt M parsed values
  | none => False

theorem meaning_of_parse {relation : String} {parsed : WMRelation}
    (parse : WMRelation.parse relation = some parsed) :
    meaning M relation = meaningAt M parsed := by
  funext values
  simp [meaning, parse]

end Algebra

/-! ## Reading the constructors

Each lemma says when a constructor application denotes, and what. -/

section Reading

variable {State Query Ev : Type} [EvidenceType State] [ConjugateEvidence Ev]
  [AdditiveWorldModel State Query Ev]
variable {M : WMModel State Query Ev} {ν : String → Option (WMValue M)}

open WMValue


theorem den_revise {p q : Pattern} {v : WMValue M} :
    denote (algebra M) ν (pRevise p q) = some v ↔
      ∃ x y, denote (algebra M) ν (p) = some (.state x) ∧ denote (algebra M) ν (q) = some (.state y) ∧ v = .state (x + y) := by
  simp only [pRevise, denote_apply_two, algebra_op_of_parse M (by decide : WMLabel.parse "Revise" = some .revise), opAt, arity2, Option.bind_eq_some_iff]
  aesop (add norm simp [Option.bind_eq_some_iff, Option.map_eq_some_iff])

theorem den_extract {w q : Pattern} {v : WMValue M} :
    denote (algebra M) ν (pExtract w q) = some v ↔
      ∃ x z, denote (algebra M) ν (w) = some (.state x) ∧ denote (algebra M) ν (q) = some (.query z) ∧
        v = .evidence (AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) x z) := by
  simp only [pExtract, denote_apply_two, algebra_op_of_parse M (by decide : WMLabel.parse "Extract" = some .extract), opAt, arity2, Option.bind_eq_some_iff]
  aesop (add norm simp [Option.bind_eq_some_iff, Option.map_eq_some_iff])

theorem den_combine {p q : Pattern} {v : WMValue M} :
    denote (algebra M) ν (pCombine p q) = some v ↔
      ∃ x y, denote (algebra M) ν (p) = some (.evidence x) ∧ denote (algebra M) ν (q) = some (.evidence y) ∧ v = .evidence (x + y) := by
  simp only [pCombine, denote_apply_two, algebra_op_of_parse M (by decide : WMLabel.parse "Combine" = some .combine), opAt, arity2, Option.bind_eq_some_iff]
  aesop (add norm simp [Option.bind_eq_some_iff, Option.map_eq_some_iff])

theorem den_evidenceZero : denote (algebra M) ν pEvidenceZero = some (.evidence 0) := by
  simp only [pEvidenceZero, denote_apply_nil,
    algebra_op_of_parse M (by decide : WMLabel.parse "EvidenceZero" = some .evidenceZero),
    opAt, arity0]

theorem den_evidenceOne :
    denote (algebra M) ν pEvidenceOne = some (.evidence (M.ofBinary ⟨1, 0⟩)) := by
  simp only [pEvidenceOne, denote_apply_nil,
    algebra_op_of_parse M (by decide : WMLabel.parse "EvidenceOne" = some .evidenceOne),
    opAt, arity0]

theorem den_evidenceOneNegative :
    denote (algebra M) ν pEvidenceOneNegative = some (.evidence (M.ofBinary ⟨0, 1⟩)) := by
  simp only [pEvidenceOneNegative, denote_apply_nil,
    algebra_op_of_parse M
      (by decide : WMLabel.parse "EvidenceOneNegative" = some .evidenceOneNegative),
    opAt, arity0]

theorem den_costZero : denote (algebra M) ν pCostZero = some (.cost 0) := by
  simp only [pCostZero, denote_apply_nil,
    algebra_op_of_parse M (by decide : WMLabel.parse "CostZero" = some .costZero), opAt, arity0]

theorem den_trustedAll : denote (algebra M) ν pTrustedAll = some (.policy M.trustAll) := by
  simp only [pTrustedAll, denote_apply_nil,
    algebra_op_of_parse M (by decide : WMLabel.parse "TrustedAll" = some .trustedAll),
    opAt, arity0]

theorem den_channelId : denote (algebra M) ν pChannelId = some (.garbling id) := by
  simp only [pChannelId, denote_apply_nil,
    algebra_op_of_parse M (by decide : WMLabel.parse "ChannelId" = some .channelId),
    opAt, arity0]

theorem den_stochId :
    denote (algebra M) ν pStochId = some (.stochasticGarbling (Stoch.stochasticId M.Ω)) := by
  simp only [pStochId, denote_apply_nil,
    algebra_op_of_parse M (by decide : WMLabel.parse "StochId" = some .stochId), opAt, arity0]

theorem den_overlapMerge {p q : Pattern} {v : WMValue M} :
    denote (algebra M) ν (pOverlapMerge p q) = some v ↔
      ∃ x y, denote (algebra M) ν (p) = some (.state x) ∧ denote (algebra M) ν (q) = some (.state y) ∧
        v = .state (M.overlap.merge x y) := by
  simp only [pOverlapMerge, denote_apply_two, algebra_op_of_parse M (by decide : WMLabel.parse "OverlapMerge" = some .overlapMerge), opAt, arity2, Option.bind_eq_some_iff]
  aesop (add norm simp [Option.bind_eq_some_iff, Option.map_eq_some_iff])

theorem den_overlapFactor {p q r : Pattern} {v : WMValue M} :
    denote (algebra M) ν (pOverlapFactor p q r) = some v ↔
      ∃ x y z, denote (algebra M) ν (p) = some (.state x) ∧ denote (algebra M) ν (q) = some (.state y) ∧ denote (algebra M) ν (r) = some (.query z) ∧
        v = .overlap (M.overlap.overlap x y z) := by
  simp only [pOverlapFactor, denote_apply_three, algebra_op_of_parse M (by decide : WMLabel.parse "OverlapFactor" = some .overlapFactor), opAt, arity3, Option.bind_eq_some_iff]
  aesop (add norm simp [Option.bind_eq_some_iff, Option.map_eq_some_iff])

theorem den_overlapCorrect {p q r : Pattern} {v : WMValue M} :
    denote (algebra M) ν (pOverlapCorrect p q r) = some v ↔
      ∃ x y z, denote (algebra M) ν (p) = some (.evidence x) ∧ denote (algebra M) ν (q) = some (.evidence y) ∧
        denote (algebra M) ν (r) = some (.overlap z) ∧ v = .evidence (M.overlap.combine x y z) := by
  simp only [pOverlapCorrect, denote_apply_three, algebra_op_of_parse M (by decide : WMLabel.parse "OverlapCorrect" = some .overlapCorrect), opAt, arity3, Option.bind_eq_some_iff]
  aesop (add norm simp [Option.bind_eq_some_iff, Option.map_eq_some_iff])

theorem den_forget {s w : Pattern} {v : WMValue M} :
    denote (algebra M) ν (pForget s w) = some v ↔
      ∃ S x, denote (algebra M) ν (s) = some (.scope S) ∧ denote (algebra M) ν (w) = some (.state x) ∧
        v = .state (M.forgetting.forget S x) := by
  simp only [pForget, denote_apply_two, algebra_op_of_parse M (by decide : WMLabel.parse "Forget" = some .forget), opAt, arity2, Option.bind_eq_some_iff]
  aesop (add norm simp [Option.bind_eq_some_iff, Option.map_eq_some_iff])

theorem den_sourceCompatible {p q : Pattern} {v : WMValue M} :
    denote (algebra M) ν (pSourceCompatible p q) = some v ↔
      ∃ x y, denote (algebra M) ν (p) = some (.state x) ∧ denote (algebra M) ν (q) = some (.state y) ∧
        v = .proposition (M.compatible x y) := by
  simp only [pSourceCompatible, denote_apply_two, algebra_op_of_parse M (by decide : WMLabel.parse "SourceCompatible" = some .sourceCompatible), opAt, arity2, Option.bind_eq_some_iff]
  aesop (add norm simp [Option.bind_eq_some_iff, Option.map_eq_some_iff])

theorem den_partialRevision {p q : Pattern} {v : WMValue M} :
    denote (algebra M) ν (pPartialRevision p q) = some v ↔
      ∃ x y z, denote (algebra M) ν (p) = some (.state x) ∧ denote (algebra M) ν (q) = some (.state y) ∧
        M.partialRevision x y = some z ∧ v = .state z := by
  simp only [pPartialRevision, denote_apply_two, algebra_op_of_parse M (by decide : WMLabel.parse "PartialRevision" = some .partialRevision), opAt, arity2, Option.bind_eq_some_iff]
  aesop (add norm simp [Option.bind_eq_some_iff, Option.map_eq_some_iff])

theorem den_fallbackRevision {p q : Pattern} {v : WMValue M} :
    denote (algebra M) ν (pFallbackRevision p q) = some v ↔
      ∃ x y, denote (algebra M) ν (p) = some (.state x) ∧ denote (algebra M) ν (q) = some (.state y) ∧
        v = .state (M.fallbackRevision x y) := by
  simp only [pFallbackRevision, denote_apply_two, algebra_op_of_parse M (by decide : WMLabel.parse "FallbackRevision" = some .fallbackRevision), opAt, arity2, Option.bind_eq_some_iff]
  aesop (add norm simp [Option.bind_eq_some_iff, Option.map_eq_some_iff])

theorem den_trustedGate {p w : Pattern} {v : WMValue M} :
    denote (algebra M) ν (pTrustedGate p w) = some v ↔
      ∃ x y, denote (algebra M) ν (p) = some (.policy x) ∧ denote (algebra M) ν (w) = some (.state y) ∧ v = .state (M.gate x y) := by
  simp only [pTrustedGate, denote_apply_two, algebra_op_of_parse M (by decide : WMLabel.parse "TrustedGate" = some .trustedGate), opAt, arity2, Option.bind_eq_some_iff]
  aesop (add norm simp [Option.bind_eq_some_iff, Option.map_eq_some_iff])

theorem den_policyRevisedState {p a b : Pattern} {v : WMValue M} :
    denote (algebra M) ν (pPolicyRevisedState p a b) = some v ↔
      ∃ x y z, denote (algebra M) ν (p) = some (.policy x) ∧ denote (algebra M) ν (a) = some (.state y) ∧ denote (algebra M) ν (b) = some (.state z) ∧
        v = .state (M.gate x (M.fallbackRevision y z)) := by
  simp only [pPolicyRevisedState, denote_apply_three, algebra_op_of_parse M (by decide : WMLabel.parse "PolicyRevisedState" = some .policyRevisedState), opAt, arity3, Option.bind_eq_some_iff]
  aesop (add norm simp [Option.bind_eq_some_iff, Option.map_eq_some_iff])

theorem den_immediateStep {r w s c : Pattern} {v : WMValue M} :
    denote (algebra M) ν (pImmediateStep r w s c) = some v ↔
      ∃ R x seed current, denote (algebra M) ν (r) = some (.ruleSet R) ∧ denote (algebra M) ν (w) = some (.state x) ∧
        denote (algebra M) ν (s) = some (.querySet seed) ∧ denote (algebra M) ν (c) = some (.querySet current) ∧
        v = .querySet (immediateStep (State := State) (Query := M.FQuery) R x seed current) := by
  simp only [pImmediateStep, denote_apply_four, algebra_op_of_parse M (by decide : WMLabel.parse "ImmediateStep" = some .immediateStep), opAt, arity4, Option.bind_eq_some_iff]
  aesop (add norm simp [Option.bind_eq_some_iff, Option.map_eq_some_iff])

theorem den_leastClosure {r w s : Pattern} {v : WMValue M} :
    denote (algebra M) ν (pLeastClosure r w s) = some v ↔
      ∃ R x seed, denote (algebra M) ν (r) = some (.ruleSet R) ∧ denote (algebra M) ν (w) = some (.state x) ∧
        denote (algebra M) ν (s) = some (.querySet seed) ∧
        v = .querySet (leastRuleClosure (State := State) (Query := M.FQuery) R x seed) := by
  simp only [pLeastClosure, denote_apply_three, algebra_op_of_parse M (by decide : WMLabel.parse "LeastClosure" = some .leastClosure), opAt, arity3, Option.bind_eq_some_iff]
  aesop (add norm simp [Option.bind_eq_some_iff, Option.map_eq_some_iff])

theorem den_immediateIter {r w s n : Pattern} {v : WMValue M} :
    denote (algebra M) ν (pImmediateIter r w s n) = some v ↔
      ∃ R x seed k, denote (algebra M) ν (r) = some (.ruleSet R) ∧ denote (algebra M) ν (w) = some (.state x) ∧
        denote (algebra M) ν (s) = some (.querySet seed) ∧ denote (algebra M) ν (n) = some (.natural k) ∧
        v = .querySet (immediateIter (State := State) (Query := M.FQuery) R x seed k) := by
  simp only [pImmediateIter, denote_apply_four, algebra_op_of_parse M (by decide : WMLabel.parse "ImmediateIter" = some .immediateIter), opAt, arity4, Option.bind_eq_some_iff]
  aesop (add norm simp [Option.bind_eq_some_iff, Option.map_eq_some_iff])

theorem den_succ {n : Pattern} {v : WMValue M} :
    denote (algebra M) ν (pSucc n) = some v ↔ ∃ k, denote (algebra M) ν (n) = some (.natural k) ∧ v = .natural (k + 1) := by
  simp only [pSucc, denote_apply_one, algebra_op_of_parse M (by decide : WMLabel.parse "Succ" = some .succ), opAt, arity1, Option.bind_eq_some_iff]
  aesop (add norm simp [Option.bind_eq_some_iff, Option.map_eq_some_iff])

theorem den_card {q : Pattern} {v : WMValue M} :
    denote (algebra M) ν (pCard q) = some v ↔ ∃ Q, denote (algebra M) ν (q) = some (.querySpace Q) ∧ v = .natural Q.card := by
  simp only [pCard, denote_apply_one, algebra_op_of_parse M (by decide : WMLabel.parse "Card" = some .card), opAt, arity1, Option.bind_eq_some_iff]
  aesop (add norm simp [Option.bind_eq_some_iff, Option.map_eq_some_iff])

theorem den_swapAnomaly {p q r : Pattern} {v : WMValue M} :
    denote (algebra M) ν (pSwapAnomaly p q r) = some v ↔
      ∃ x y z, denote (algebra M) ν (p) = some (.state x) ∧ denote (algebra M) ν (q) = some (.state y) ∧ denote (algebra M) ν (r) = some (.query z) ∧
        v = .cost (SwapAnomalyCount (State := State) (Query := Query) (Ev := Ev)
          M.overlap x y z) := by
  simp only [pSwapAnomaly, denote_apply_three, algebra_op_of_parse M (by decide : WMLabel.parse "SwapAnomaly" = some .swapAnomaly), opAt, arity3, Option.bind_eq_some_iff]
  aesop (add norm simp [Option.bind_eq_some_iff, Option.map_eq_some_iff])

theorem den_scheduleError {b s₁ s₂ q : Pattern} {v : WMValue M} :
    denote (algebra M) ν (pScheduleError b s₁ s₂ q) = some v ↔
      ∃ x y z w, denote (algebra M) ν (b) = some (.state x) ∧ denote (algebra M) ν (s₁) = some (.schedule y) ∧
        denote (algebra M) ν (s₂) = some (.schedule z) ∧ denote (algebra M) ν (q) = some (.query w) ∧
        v = .cost (scheduleErrorCount (State := State) (Query := Query) (Ev := Ev)
          M.overlap x y z w) := by
  simp only [pScheduleError, denote_apply_four, algebra_op_of_parse M (by decide : WMLabel.parse "ScheduleError" = some .scheduleError), opAt, arity4, Option.bind_eq_some_iff]
  aesop (add norm simp [Option.bind_eq_some_iff, Option.map_eq_some_iff])

theorem den_experimentEvidence {w q : Pattern} {v : WMValue M} :
    denote (algebra M) ν (pExperimentEvidence w q) = some v ↔
      ∃ x y, denote (algebra M) ν (w) = some (.state x) ∧ denote (algebra M) ν (q) = some (.experimentQuery y) ∧
        v = .evidence (M.ofBinary (Det.experimentEvidence (M.hypotheses x) y)) := by
  simp only [pExperimentEvidence, denote_apply_two, algebra_op_of_parse M (by decide : WMLabel.parse "ExperimentEvidence" = some .experimentEvidence), opAt, arity2, Option.bind_eq_some_iff]
  aesop (add norm simp [Option.bind_eq_some_iff, Option.map_eq_some_iff])

theorem den_blackwellPullback {s k q : Pattern} {v : WMValue M} :
    denote (algebra M) ν (pBlackwellPullback s k q) = some v ↔
      ∃ strong κ query, denote (algebra M) ν (s) = some (.channel strong) ∧ denote (algebra M) ν (k) = some (.garbling κ) ∧
        denote (algebra M) ν (q) = some (.experimentQuery query) ∧
        v = .experimentQuery (Det.pullbackQuery strong κ query.outcome) := by
  simp only [pBlackwellPullback, denote_apply_three, algebra_op_of_parse M (by decide : WMLabel.parse "BlackwellPullback" = some .blackwellPullback), opAt, arity3, Option.bind_eq_some_iff]
  aesop (add norm simp [Option.bind_eq_some_iff, Option.map_eq_some_iff])

theorem den_channelComp {p q : Pattern} {v : WMValue M} :
    denote (algebra M) ν (pChannelComp p q) = some v ↔
      ∃ a b, denote (algebra M) ν (p) = some a ∧ denote (algebra M) ν (q) = some b ∧ WMValue.compose a b = some v := by
  simp only [pChannelComp, denote_apply_two, algebra_op_of_parse M (by decide : WMLabel.parse "ChannelComp" = some .channelComp), opAt, arity2, Option.bind_eq_some_iff]
  aesop

theorem den_stochEvidence {w q : Pattern} {v : WMValue M} :
    denote (algebra M) ν (pStochEvidence w q) = some v ↔
      ∃ x y, denote (algebra M) ν (w) = some (.state x) ∧ denote (algebra M) ν (q) = some (.stochasticQuery y) ∧
        v = .evidence (M.ofBinary (Stoch.stochasticEvidence (M.weights x) y)) := by
  simp only [pStochEvidence, denote_apply_two, algebra_op_of_parse M (by decide : WMLabel.parse "StochEvidence" = some .stochEvidence), opAt, arity2, Option.bind_eq_some_iff]
  aesop (add norm simp [Option.bind_eq_some_iff, Option.map_eq_some_iff])

theorem den_expectedUtility {p c d u : Pattern} {v : WMValue M} :
    denote (algebra M) ν (pExpectedUtility p c d u) = some v ↔
      ∃ π ch δ util, denote (algebra M) ν (p) = some (.prior π) ∧ denote (algebra M) ν (c) = some (.stochasticChannel ch) ∧
        denote (algebra M) ν (d) = some (.decision δ) ∧ denote (algebra M) ν (u) = some (.utility util) ∧
        v = .cost (Stoch.expectedUtility π ch δ util) := by
  simp only [pExpectedUtility, denote_apply_four, algebra_op_of_parse M (by decide : WMLabel.parse "ExpectedUtility" = some .expectedUtility), opAt, arity4, Option.bind_eq_some_iff]
  aesop (add norm simp [Option.bind_eq_some_iff, Option.map_eq_some_iff])

theorem den_liftPolicy {k d : Pattern} {v : WMValue M} :
    denote (algebra M) ν (pLiftPolicy k d) = some v ↔
      ∃ κ δ, denote (algebra M) ν (k) = some (.stochasticGarbling κ) ∧ denote (algebra M) ν (d) = some (.decision δ) ∧
        v = .decision (Stoch.liftDecision κ δ) := by
  simp only [pLiftPolicy, denote_apply_two, algebra_op_of_parse M (by decide : WMLabel.parse "LiftPolicy" = some .liftPolicy), opAt, arity2, Option.bind_eq_some_iff]
  aesop (add norm simp [Option.bind_eq_some_iff, Option.map_eq_some_iff])

theorem den_kripkeEvidence {w φ : Pattern} {v : WMValue M} :
    denote (algebra M) ν (pKripkeEvidence w φ) = some v ↔
      ∃ x y, denote (algebra M) ν (w) = some (.state x) ∧ denote (algebra M) ν (φ) = some (.modalQuery y) ∧
        v = .evidence (M.ofBinary (crispEvidence M.satisfies (M.points x) y)) := by
  simp only [pKripkeEvidence, denote_apply_two, algebra_op_of_parse M (by decide : WMLabel.parse "KripkeEvidence" = some .kripkeEvidence), opAt, arity2, Option.bind_eq_some_iff]
  aesop (add norm simp [Option.bind_eq_some_iff, Option.map_eq_some_iff])

/-- The Kripke reading is the crisp world model of the model's satisfaction
relation, read at the points of a state.  For pointed Kripke models with their
satisfaction relation and the identity reading of states, this is the Kripke
world model of `PLNWorldModelKripke`. -/
theorem den_kripkeEvidence_crisp {w φ : Pattern} {x : State} {y : M.ModalQuery}
    (hw : denote (algebra M) ν w = some (.state x))
    (hφ : denote (algebra M) ν φ = some (.modalQuery y)) :
    denote (algebra M) ν (pKripkeEvidence w φ) =
      some (.evidence (M.ofBinary
        (@BinaryWorldModel.evidence _ _ _ (crispWorldModel M.satisfies) (M.points x) y))) :=
  den_kripkeEvidence.mpr ⟨x, y, hw, hφ, rfl⟩

theorem den_singleton {p : Pattern} {v : WMValue M} :
    denote (algebra M) ν (pSingleton p) = some v ↔ ∃ x, denote (algebra M) ν (p) = some (.point x) ∧ v = .state (M.singleton x) := by
  simp only [pSingleton, denote_apply_one, algebra_op_of_parse M (by decide : WMLabel.parse "Singleton" = some .singleton), opAt, arity1, Option.bind_eq_some_iff]
  aesop (add norm simp [Option.bind_eq_some_iff, Option.map_eq_some_iff])

theorem den_genericEvidence {w q : Pattern} {v : WMValue M} :
    denote (algebra M) ν (pGenericEvidence w q) = some v ↔
      ∃ x z, denote (algebra M) ν (w) = some (.state x) ∧ denote (algebra M) ν (q) = some (.query z) ∧
        v = .evidence (AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) x z) := by
  simp only [pGenericEvidence, denote_apply_two, algebra_op_of_parse M (by decide : WMLabel.parse "GenericEvidence" = some .genericEvidence), opAt, arity2, Option.bind_eq_some_iff]
  aesop (add norm simp [Option.bind_eq_some_iff, Option.map_eq_some_iff])

/-- Channel composition is defined within the deterministic and within the
stochastic channels. -/
theorem compose_eq_some {a b v : WMValue M} :
    WMValue.compose a b = some v ↔
      (∃ f g, a = .channel f ∧ b = .garbling g ∧ v = .channel ⟨g ∘ f.run⟩) ∨
      (∃ f g, a = .garbling f ∧ b = .garbling g ∧ v = .garbling (g ∘ f)) ∨
      (∃ f g, a = .stochasticChannel f ∧ b = .stochasticGarbling g ∧
        v = .stochasticChannel (Stoch.stochasticComp f g)) ∨
      (∃ f g, a = .stochasticGarbling f ∧ b = .stochasticGarbling g ∧
        v = .stochasticGarbling (Stoch.stochasticComp f g)) := by
  cases a <;> simp [WMValue.compose, Option.map_eq_some_iff] <;> aesop (add norm simp [Option.bind_eq_some_iff, Option.map_eq_some_iff])

/-- A relation premise over two first-order arguments holds when both denote
and their values are related. -/
theorem premise_two {M' : RelationMeaning (WMValue M)} {relation : String} {p q : Pattern}
    (holds : PremiseHolds (algebra M) M' ν (.relationQuery relation [p, q])) :
    ∃ a b, denote (algebra M) ν (p) = some a ∧ denote (algebra M) ν (q) = some b ∧ M' relation [a, b] := by
  simp only [PremiseHolds, denoteList_cons, denoteList_nil, Option.bind_eq_some_iff,
    Option.map_eq_some_iff] at holds
  aesop (add norm simp [Option.bind_eq_some_iff, Option.map_eq_some_iff])

theorem premise_three {M' : RelationMeaning (WMValue M)} {relation : String}
    {p q r : Pattern}
    (holds : PremiseHolds (algebra M) M' ν (.relationQuery relation [p, q, r])) :
    ∃ a b c, denote (algebra M) ν (p) = some a ∧ denote (algebra M) ν (q) = some b ∧ denote (algebra M) ν (r) = some c ∧ M' relation [a, b, c] := by
  simp only [PremiseHolds, denoteList_cons, denoteList_nil, Option.bind_eq_some_iff,
    Option.map_eq_some_iff] at holds
  aesop (add norm simp [Option.bind_eq_some_iff, Option.map_eq_some_iff])

end Reading

/-! ## Every rule is valid -/

section Validity

variable {State Query Ev : Type} [EvidenceType State] [ConjugateEvidence Ev]
  [AdditiveWorldModel State Query Ev]
variable {M : WMModel State Query Ev}

open WMValue
open Mettapedia.PLN.WorldModel.PLNWorldModelSupportForgetting.SupportTrackedForgettingLayer
  (forget_add_of_supported)

/-- Two readings of the same pattern agree. -/
private theorem same {ν : String → Option (WMValue M)} {p : Pattern} {a b : WMValue M}
    (first : denote (algebra M) ν p = some a) (second : denote (algebra M) ν p = some b) :
    a = b :=
  Option.some.inj (first.symm.trans second)

private theorem stochasticComp_assoc {α β γ δ : Type} (f : Stoch.StochasticChannel α β)
    (g : Stoch.StochasticChannel β γ) (h : Stoch.StochasticChannel γ δ) :
    Stoch.stochasticComp (Stoch.stochasticComp f g) h =
      Stoch.stochasticComp f (Stoch.stochasticComp g h) := by
  funext θ
  simp only [Mettapedia.PLN.WorldModel.Experiment.PLNWorldModelExperimentStochastic.stochasticComp,
    PMF.bind_bind]
  rfl

private theorem stochasticComp_id {α β : Type} (f : Stoch.StochasticChannel α β) :
    Stoch.stochasticComp f (Stoch.stochasticId β) = f := by
  funext θ
  show (f θ).bind PMF.pure = f θ
  exact PMF.bind_pure (f θ)

theorem compose_assoc {a b c ab v : WMValue M} (first : WMValue.compose a b = some ab)
    (second : WMValue.compose ab c = some v) :
    ∃ bc, WMValue.compose b c = some bc ∧ WMValue.compose a bc = some v := by
  rcases compose_eq_some.mp first with ⟨f, g, rfl, rfl, rfl⟩ | ⟨f, g, rfl, rfl, rfl⟩ |
      ⟨f, g, rfl, rfl, rfl⟩ | ⟨f, g, rfl, rfl, rfl⟩ <;>
    rcases compose_eq_some.mp second with ⟨f', h, ⟨⟩, rfl, rfl⟩ | ⟨f', h, ⟨⟩, rfl, rfl⟩ |
      ⟨f', h, ⟨⟩, rfl, rfl⟩ | ⟨f', h, ⟨⟩, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, by rw [stochasticComp_assoc]; rfl⟩
  · exact ⟨_, rfl, by rw [stochasticComp_assoc]; rfl⟩

theorem evidenceAdd_valid : RuleValid (algebra M) (meaning M) ruleEvidenceAdd := by
  intro ν _ value left
  obtain ⟨w, z, hw, hz, rfl⟩ := den_extract.mp left
  obtain ⟨x, y, hx, hy, ⟨⟩⟩ := den_revise.mp hw
  refine den_combine.mpr ⟨_, _, den_extract.mpr ⟨x, z, hx, hz, rfl⟩,
    den_extract.mpr ⟨y, z, hy, hz, rfl⟩, ?_⟩
  rw [AdditiveWorldModel.extract_add]

theorem revisionComm_valid : RuleValid (algebra M) (meaning M) ruleRevisionComm := by
  intro ν _ value left
  obtain ⟨x, y, hx, hy, rfl⟩ := den_revise.mp left
  exact den_revise.mpr ⟨y, x, hy, hx, by rw [add_comm]⟩

theorem revisionAssoc_valid : RuleValid (algebra M) (meaning M) ruleRevisionAssoc := by
  intro ν _ value left
  obtain ⟨xy, z, hxy, hz, rfl⟩ := den_revise.mp left
  obtain ⟨x, y, hx, hy, ⟨⟩⟩ := den_revise.mp hxy
  exact den_revise.mpr ⟨x, y + z, hx, den_revise.mpr ⟨y, z, hy, hz, rfl⟩, by rw [add_assoc]⟩

theorem combineComm_valid : RuleValid (algebra M) (meaning M) ruleCombineComm := by
  intro ν _ value left
  obtain ⟨x, y, hx, hy, rfl⟩ := den_combine.mp left
  exact den_combine.mpr ⟨y, x, hy, hx, by rw [add_comm]⟩

theorem combineZero_valid : RuleValid (algebra M) (meaning M) ruleCombineZero := by
  intro ν _ value left
  obtain ⟨x, y, hx, hy, rfl⟩ := den_combine.mp left
  obtain rfl : (0 : Ev) = y := WMValue.evidence.inj (same den_evidenceZero hy)
  rw [add_zero]
  exact hx

theorem overlapExtract_valid : RuleValid (algebra M) (meaning M) ruleOverlapExtract := by
  intro ν _ value left
  obtain ⟨w, z, hw, hz, rfl⟩ := den_extract.mp left
  obtain ⟨x, y, hx, hy, ⟨⟩⟩ := den_overlapMerge.mp hw
  refine den_overlapCorrect.mpr ⟨_, _, _, den_extract.mpr ⟨x, z, hx, hz, rfl⟩,
    den_extract.mpr ⟨y, z, hy, hz, rfl⟩, den_overlapFactor.mpr ⟨x, y, z, hx, hy, hz, rfl⟩, ?_⟩
  rw [M.overlap.evidence_merge]

theorem forgetOutside_valid : RuleValid (algebra M) (meaning M) ruleForgetOutside := by
  intro ν holds value left
  obtain ⟨w, z, hw, hz, rfl⟩ := den_extract.mp left
  obtain ⟨S, x, hS, hx, ⟨⟩⟩ := den_forget.mp hw
  obtain ⟨a, b, ha, hb, related⟩ := premise_two
    (holds (.relationQuery "outsideScope" [.fvar "S", .fvar "q"]) (by simp [ruleForgetOutside]))
  rw [meaning_of_parse M (by decide : WMRelation.parse "outsideScope" = some .outsideScope)]
    at related
  obtain ⟨S', z', rfl, rfl, outside⟩ := related
  obtain rfl : S' = S := WMValue.scope.inj (same ha hS)
  obtain rfl : z' = z := WMValue.query.inj (same hb hz)
  exact den_extract.mpr ⟨x, z', hx, hz, by rw [M.forgetting.outsideInvariant outside]⟩

theorem forgetIdempotent_valid : RuleValid (algebra M) (meaning M) ruleForgetIdempotent := by
  intro ν _ value left
  obtain ⟨S, w, hS, hw, rfl⟩ := den_forget.mp left
  obtain ⟨S', x, hS', hx, ⟨⟩⟩ := den_forget.mp hw
  obtain rfl : S' = S := WMValue.scope.inj (same hS' hS)
  exact den_forget.mpr ⟨S', x, hS', hx, by rw [M.forgetting.idempotent]⟩

theorem forgetAbsorbSupported_valid :
    RuleValid (algebra M) (meaning M) ruleForgetAbsorbSupported := by
  intro ν holds value left
  obtain ⟨S, w, hS, hw, rfl⟩ := den_forget.mp left
  obtain ⟨x, d, hx, hd, ⟨⟩⟩ := den_revise.mp hw
  obtain ⟨a, b, ha, hb, related⟩ := premise_two
    (holds (.relationQuery "supportedInScope" [.fvar "S", .fvar "D"])
      (by simp [ruleForgetAbsorbSupported]))
  rw [meaning_of_parse M (by decide : WMRelation.parse "supportedInScope" = some .supportedInScope)]
    at related
  obtain ⟨S', d', rfl, rfl, supported⟩ := related
  obtain rfl : S' = S := WMValue.scope.inj (same ha hS)
  obtain rfl : d' = d := WMValue.state.inj (same hb hd)
  exact den_forget.mpr ⟨S', x, hS, hx, by rw [forget_add_of_supported M.forgetting supported]⟩

theorem forgetClean_valid : RuleValid (algebra M) (meaning M) ruleForgetClean := by
  intro ν holds value left
  obtain ⟨S, x, hS, hx, rfl⟩ := den_forget.mp left
  obtain ⟨a, b, ha, hb, related⟩ := premise_two
    (holds (.relationQuery "cleanForScope" [.fvar "S", .fvar "W"]) (by simp [ruleForgetClean]))
  rw [meaning_of_parse M (by decide : WMRelation.parse "cleanForScope" = some .cleanForScope)]
    at related
  obtain ⟨S', x', rfl, rfl, clean⟩ := related
  obtain rfl : S' = S := WMValue.scope.inj (same ha hS)
  obtain rfl : x' = x := WMValue.state.inj (same hb hx)
  rw [M.forgetting.forget_eq_self_of_clean clean]
  exact hx

theorem compatibleSymm_valid : RuleValid (algebra M) (meaning M) ruleCompatibleSymm := by
  intro ν _ value left
  obtain ⟨x, y, hx, hy, rfl⟩ := den_sourceCompatible.mp left
  refine den_sourceCompatible.mpr ⟨y, x, hy, hx, ?_⟩
  rw [propext ⟨M.compatible_symm, M.compatible_symm⟩]

/-- The compatibility premise of the provenance rules, read at the matched
states. -/
private theorem compatible_of_premise {ν : String → Option (WMValue M)} {x y : State}
    {premises : List Premise} (holds : ∀ premise ∈ premises, PremiseHolds (algebra M) (meaning M) ν premise)
    (member : sourceCompatiblePremise ∈ premises)
    (hx : denote (algebra M) ν (.fvar "W1") = some (.state x))
    (hy : denote (algebra M) ν (.fvar "W2") = some (.state y)) : M.compatible x y := by
  obtain ⟨a, b, ha, hb, related⟩ := premise_two (holds sourceCompatiblePremise member)
  rw [meaning_of_parse M (by decide : WMRelation.parse "sourceCompatible" = some .sourceCompatible)]
    at related
  obtain ⟨x', y', rfl, rfl, compatible⟩ := related
  obtain rfl : x' = x := WMValue.state.inj (same ha hx)
  obtain rfl : y' = y := WMValue.state.inj (same hb hy)
  exact compatible

theorem fallbackCompatible_valid : RuleValid (algebra M) (meaning M) ruleFallbackCompatible := by
  intro ν holds value left
  obtain ⟨x, y, hx, hy, rfl⟩ := den_fallbackRevision.mp left
  have compatible := compatible_of_premise holds (by simp [ruleFallbackCompatible]) hx hy
  exact den_revise.mpr ⟨x, y, hx, hy, by rw [M.fallbackRevision_of_compatible compatible]⟩

theorem fallbackIncompatible_valid :
    RuleValid (algebra M) (meaning M) ruleFallbackIncompatible := by
  intro ν holds value left
  obtain ⟨x, y, hx, hy, rfl⟩ := den_fallbackRevision.mp left
  obtain ⟨a, b, ha, hb, related⟩ := premise_two
    (holds (.relationQuery "notSourceCompatible" [.fvar "W1", .fvar "W2"])
      (by simp [ruleFallbackIncompatible]))
  rw [meaning_of_parse M
    (by decide : WMRelation.parse "notSourceCompatible" = some .notSourceCompatible)] at related
  obtain ⟨x', y', rfl, rfl, incompatible⟩ := related
  obtain rfl : x' = x := WMValue.state.inj (same ha hx)
  obtain rfl : y' = y := WMValue.state.inj (same hb hy)
  rw [M.fallbackRevision_of_not_compatible incompatible]
  exact hx

theorem partialRevisionCompatible_valid :
    RuleValid (algebra M) (meaning M) rulePartialRevisionCompatible := by
  intro ν holds value left
  obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := den_partialRevision.mp left
  have compatible := compatible_of_premise holds (by simp [rulePartialRevisionCompatible]) hx hy
  rw [M.partialRevision_of_compatible compatible] at hz
  obtain rfl := Option.some.inj hz
  exact den_revise.mpr ⟨x, y, hx, hy, rfl⟩

theorem trustedGateAll_valid : RuleValid (algebra M) (meaning M) ruleTrustedGateAll := by
  intro ν _ value left
  obtain ⟨p, y, hp, hy, rfl⟩ := den_trustedGate.mp left
  obtain rfl : M.trustAll = p := WMValue.policy.inj (same den_trustedAll hp)
  rw [M.gate_trustAll]
  exact hy

theorem sourceEvidenceAdd_valid : RuleValid (algebra M) (meaning M) ruleSourceEvidenceAdd := by
  intro ν holds value left
  obtain ⟨w, z, hw, hz, rfl⟩ := den_extract.mp left
  obtain ⟨x, y, hx, hy, ⟨⟩⟩ := den_fallbackRevision.mp hw
  have compatible := compatible_of_premise holds (by simp [ruleSourceEvidenceAdd]) hx hy
  refine den_combine.mpr ⟨_, _, den_extract.mpr ⟨x, z, hx, hz, rfl⟩,
    den_extract.mpr ⟨y, z, hy, hz, rfl⟩, ?_⟩
  rw [M.fallbackRevision_of_compatible compatible, AdditiveWorldModel.extract_add]

theorem closureFixpoint_valid : RuleValid (algebra M) (meaning M) ruleClosureFixpoint := by
  intro ν _ value left
  obtain ⟨R, x, seed, current, hR, hx, hseed, hcurrent, rfl⟩ := den_immediateStep.mp left
  obtain ⟨R', x', seed', hR', hx', hseed', closure⟩ := den_leastClosure.mp hcurrent
  obtain rfl : R' = R := WMValue.ruleSet.inj (same hR' hR)
  obtain rfl : x' = x := WMValue.state.inj (same hx' hx)
  obtain rfl : seed' = seed := WMValue.querySet.inj (same hseed' hseed)
  obtain rfl := WMValue.querySet.inj closure
  refine den_leastClosure.mpr ⟨R', x', seed', hR, hx, hseed, ?_⟩
  rw [Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.leastRuleClosure_fixedpoint]

theorem iterUnfolding_valid : RuleValid (algebra M) (meaning M) ruleIterUnfolding := by
  intro ν _ value left
  obtain ⟨R, x, seed, k, hR, hx, hseed, hk, rfl⟩ := den_immediateIter.mp left
  obtain ⟨n, hn, ⟨⟩⟩ := den_succ.mp hk
  exact den_immediateStep.mpr ⟨R, x, seed, _, hR, hx, hseed,
    den_immediateIter.mpr ⟨R, x, seed, n, hR, hx, hseed, hn, rfl⟩, rfl⟩

theorem policyTrustedAllCompatible_valid :
    RuleValid (algebra M) (meaning M) rulePolicyTrustedAllCompatible := by
  intro ν holds value left
  obtain ⟨p, x, y, hp, hx, hy, rfl⟩ := den_policyRevisedState.mp left
  obtain rfl : M.trustAll = p := WMValue.policy.inj (same den_trustedAll hp)
  have compatible :=
    compatible_of_premise holds (by simp [rulePolicyTrustedAllCompatible]) hx hy
  exact den_revise.mpr ⟨x, y, hx, hy, by
    rw [M.gate_trustAll, M.fallbackRevision_of_compatible compatible]⟩

theorem cascadeAtCard_valid : RuleValid (algebra M) (meaning M) ruleCascadeAtCard := by
  intro ν holds value left
  obtain ⟨R, x, seed, k, hR, hx, hseed, hk, rfl⟩ := den_immediateIter.mp left
  obtain ⟨Q, hQ, ⟨⟩⟩ := den_card.mp hk
  obtain ⟨a, b, ha, hb, related⟩ := premise_two
    (holds (.relationQuery "querySpaceOf" [.fvar "R", .fvar "Q"]) (by simp [ruleCascadeAtCard]))
  rw [meaning_of_parse M (by decide : WMRelation.parse "querySpaceOf" = some .querySpaceOf)]
    at related
  obtain ⟨R', Q', rfl, rfl, covers⟩ := related
  obtain rfl : Q' = Q := WMValue.querySpace.inj (same hb hQ)
  refine den_leastClosure.mpr ⟨R, x, seed, hR, hx, hseed, ?_⟩
  let space : Fintype M.FQuery := ⟨Q', covers⟩
  have bound := @Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointCascade.immediateIter_eq_leastRuleClosure_at_card_of_finite
    State M.FQuery _ _ space R x seed
  rw [← bound]
  rfl

theorem swapAnomalySymm_valid : RuleValid (algebra M) (meaning M) ruleSwapAnomalySymm := by
  intro ν _ value left
  obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := den_swapAnomaly.mp left
  exact den_swapAnomaly.mpr ⟨y, x, z, hy, hx, hz, by
    rw [Mettapedia.PLN.WorldModel.OrderCost.swapAnomalyCount_symm]⟩

theorem swapAnomalyZero_valid : RuleValid (algebra M) (meaning M) ruleSwapAnomalyZero := by
  intro ν holds value left
  obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := den_swapAnomaly.mp left
  obtain ⟨a, b, c, ha, hb, hc, related⟩ := premise_three
    (holds (.relationQuery "equalCounts" [.fvar "W1", .fvar "W2", .fvar "q"])
      (by simp [ruleSwapAnomalyZero]))
  rw [meaning_of_parse M (by decide : WMRelation.parse "equalCounts" = some .equalCounts)]
    at related
  obtain ⟨x', y', z', rfl, rfl, rfl, counts⟩ := related
  obtain rfl : x' = x := WMValue.state.inj (same ha hx)
  obtain rfl : y' = y := WMValue.state.inj (same hb hy)
  obtain rfl : z' = z := WMValue.query.inj (same hc hz)
  rw [Mettapedia.PLN.WorldModel.OrderCost.swapAnomalyCount_zero_of_count_eq _ _ _ _ counts]
  exact den_costZero

theorem scheduleErrorSymm_valid : RuleValid (algebra M) (meaning M) ruleScheduleErrorSymm := by
  intro ν _ value left
  obtain ⟨x, y, z, w, hx, hy, hz, hw, rfl⟩ := den_scheduleError.mp left
  exact den_scheduleError.mpr ⟨x, z, y, w, hx, hz, hy, hw, by
    rw [Mettapedia.PLN.WorldModel.OrderCost.scheduleErrorCount_symm]⟩

/-- The two conservation premises, read at the matched revision and query: some
scope erases the revision and excludes the query. -/
private theorem erasedOutside_of_premises {ν : String → Option (WMValue M)} {Δ : State}
    {q : Query} {premises : List Premise}
    (holds : ∀ premise ∈ premises, PremiseHolds (algebra M) (meaning M) ν premise)
    (member : ∀ premise ∈ erasedOutsideScopePremises, premise ∈ premises)
    (hD : denote (algebra M) ν (.fvar "D") = some (.state Δ))
    (hq : denote (algebra M) ν (.fvar "q") = some (.query q)) :
    ∃ S, M.forgetting.forget S Δ = 0 ∧ ¬ M.forgetting.inScope S q := by
  obtain ⟨a, b, ha, hb, erased⟩ := premise_two
    (holds (.relationQuery "erasesInScope" [.fvar "S", .fvar "D"])
      (member _ (by simp [erasedOutsideScopePremises])))
  obtain ⟨a', b', ha', hb', outside⟩ := premise_two
    (holds (.relationQuery "outsideScope" [.fvar "S", .fvar "q"])
      (member _ (by simp [erasedOutsideScopePremises])))
  rw [meaning_of_parse M (by decide : WMRelation.parse "erasesInScope" = some .erasesInScope)]
    at erased
  rw [meaning_of_parse M (by decide : WMRelation.parse "outsideScope" = some .outsideScope)]
    at outside
  obtain ⟨S, Δ', rfl, rfl, erases⟩ := erased
  obtain ⟨S', q', rfl, rfl, excluded⟩ := outside
  obtain rfl : Δ' = Δ := WMValue.state.inj (same hb hD)
  obtain rfl : q' = q := WMValue.query.inj (same hb' hq)
  obtain rfl : S' = S := WMValue.scope.inj (same ha' ha)
  exact ⟨S', erases, excluded⟩

theorem antiHallucination_valid : RuleValid (algebra M) (meaning M) ruleAntiHallucination := by
  intro ν holds value left
  obtain ⟨x, z, hx, hz, rfl⟩ := den_extract.mp left
  obtain ⟨S, erases, outside⟩ := erasedOutside_of_premises holds
    (fun premise member => by simpa [ruleAntiHallucination] using member) hx hz
  rw [Mettapedia.PLN.WorldModel.WorldModelConservationPack.antiHallucination_outsideScope_of_erases
    M.forgetting.toForgettingLayer M.zeroPreserving erases z outside]
  exact den_evidenceZero

theorem noetherConservation_valid :
    RuleValid (algebra M) (meaning M) ruleNoetherConservation := by
  intro ν holds value left
  obtain ⟨w, z, hw, hz, rfl⟩ := den_extract.mp left
  obtain ⟨x, d, hx, hd, ⟨⟩⟩ := den_revise.mp hw
  obtain ⟨S, erases, outside⟩ := erasedOutside_of_premises holds
    (fun premise member => by simpa [ruleNoetherConservation] using member) hd hz
  exact den_extract.mpr ⟨x, z, hx, hz, by
    rw [Mettapedia.PLN.WorldModel.WorldModelConservationPack.outsideScopeEvidence_conserved_of_erases
      M.forgetting.toForgettingLayer M.zeroPreserving erases x z outside]⟩

theorem experimentEvidenceAdd_valid :
    RuleValid (algebra M) (meaning M) ruleExperimentEvidenceAdd := by
  intro ν _ value left
  obtain ⟨w, e, hw, he, rfl⟩ := den_experimentEvidence.mp left
  obtain ⟨x, y, hx, hy, ⟨⟩⟩ := den_revise.mp hw
  refine den_combine.mpr ⟨_, _, den_experimentEvidence.mpr ⟨x, e, hx, he, rfl⟩,
    den_experimentEvidence.mpr ⟨y, e, hy, he, rfl⟩, ?_⟩
  rw [map_add, Mettapedia.PLN.WorldModel.Experiment.PLNWorldModelExperiment.experimentEvidence_add,
    map_add]

theorem blackwellPullback_valid : RuleValid (algebra M) (meaning M) ruleBlackwellPullback := by
  intro ν holds value left
  obtain ⟨x, pulled, hx, hpulled, rfl⟩ := den_experimentEvidence.mp left
  obtain ⟨strong, κ, query, hstrong, hκ, hquery, ⟨⟩⟩ := den_blackwellPullback.mp hpulled
  obtain ⟨a, b, c, ha, hb, hc, related⟩ := premise_three
    (holds (.relationQuery "blackwellQueryFactors" [.fvar "q", .fvar "Strong", .fvar "k"])
      (by simp [ruleBlackwellPullback]))
  rw [meaning_of_parse M
    (by decide : WMRelation.parse "blackwellQueryFactors" = some .blackwellQueryFactors)] at related
  obtain ⟨query', strong', κ', rfl, rfl, rfl, factors⟩ := related
  obtain rfl : query' = query := WMValue.experimentQuery.inj (same ha hquery)
  obtain rfl : strong' = strong := WMValue.channel.inj (same hb hstrong)
  obtain rfl : κ' = κ := WMValue.garbling.inj (same hc hκ)
  refine den_experimentEvidence.mpr ⟨x, query', hx, hquery, ?_⟩
  have equivalent :=
    Mettapedia.PLN.WorldModel.Experiment.PLNWorldModelExperiment.wmQueryEq_of_blackwellFactor
      strong' query'.channel κ' factors query'.outcome (M.hypotheses x)
  exact congrArg (fun e => WMValue.evidence (M.ofBinary e)) equivalent.symm

theorem channelCompId_valid : RuleValid (algebra M) (meaning M) ruleChannelCompId := by
  intro ν _ value left
  obtain ⟨a, b, ha, hb, composed⟩ := den_channelComp.mp left
  obtain rfl := same hb den_channelId
  rcases compose_eq_some.mp composed with ⟨f, g, rfl, same', rfl⟩ | ⟨f, g, rfl, same', rfl⟩ |
      ⟨f, g, rfl, same', rfl⟩ | ⟨f, g, rfl, same', rfl⟩
  · obtain rfl := WMValue.garbling.inj same'
    exact ha
  · obtain rfl := WMValue.garbling.inj same'
    exact ha
  · cases same'
  · cases same'

theorem stochEvidenceAdd_valid : RuleValid (algebra M) (meaning M) ruleStochEvidenceAdd := by
  intro ν _ value left
  obtain ⟨w, e, hw, he, rfl⟩ := den_stochEvidence.mp left
  obtain ⟨x, y, hx, hy, ⟨⟩⟩ := den_revise.mp hw
  refine den_combine.mpr ⟨_, _, den_stochEvidence.mpr ⟨x, e, hx, he, rfl⟩,
    den_stochEvidence.mpr ⟨y, e, hy, he, rfl⟩, ?_⟩
  rw [map_add,
    Mettapedia.PLN.WorldModel.Experiment.PLNWorldModelExperimentStochastic.stochasticEvidence_add,
    map_add]

theorem channelCompAssoc_valid : RuleValid (algebra M) (meaning M) ruleChannelCompAssoc := by
  intro ν _ value left
  obtain ⟨ab, c, hab, hc, composed⟩ := den_channelComp.mp left
  obtain ⟨a, b, ha, hb, first⟩ := den_channelComp.mp hab
  obtain ⟨bc, hbc, abc⟩ := compose_assoc first composed
  exact den_channelComp.mpr ⟨a, bc, ha, den_channelComp.mpr ⟨b, c, hb, hc, hbc⟩, abc⟩

theorem blackwellUtilityTransport_valid :
    RuleValid (algebra M) (meaning M) ruleBlackwellUtilityTransport := by
  intro ν holds value left
  obtain ⟨π, ch, δ, util, hπ, hch, hδ, hutil, rfl⟩ := den_expectedUtility.mp left
  obtain ⟨a, b, c, ha, hb, hc, related⟩ := premise_three
    (holds (.relationQuery "blackwellFactors" [.fvar "Weak", .fvar "Strong", .fvar "k"])
      (by simp [ruleBlackwellUtilityTransport]))
  rw [meaning_of_parse M (by decide : WMRelation.parse "blackwellFactors" = some .blackwellFactors)]
    at related
  obtain ⟨weak, strong, κ, rfl, rfl, rfl, factors⟩ := related
  obtain rfl : weak = ch := WMValue.stochasticChannel.inj (same ha hch)
  refine den_expectedUtility.mpr ⟨π, strong, _, util, hπ, hb,
    den_liftPolicy.mpr ⟨κ, δ, hc, hδ, rfl⟩, hutil, ?_⟩
  rw [Mettapedia.PLN.WorldModel.Experiment.PLNWorldModelExperimentStochastic.expectedUtility_eq_of_blackwellFactor
    π strong weak κ factors δ util]

theorem kleisliIdentity_valid : RuleValid (algebra M) (meaning M) ruleKleisliIdentity := by
  intro ν _ value left
  obtain ⟨a, b, ha, hb, composed⟩ := den_channelComp.mp left
  obtain rfl := same hb den_stochId
  rcases compose_eq_some.mp composed with ⟨f, g, rfl, same', rfl⟩ | ⟨f, g, rfl, same', rfl⟩ |
      ⟨f, g, rfl, same', rfl⟩ | ⟨f, g, rfl, same', rfl⟩
  · cases same'
  · cases same'
  · obtain rfl := WMValue.stochasticGarbling.inj same'
    rw [stochasticComp_id]
    exact ha
  · obtain rfl := WMValue.stochasticGarbling.inj same'
    rw [stochasticComp_id]
    exact ha

theorem kripkeEvidenceAdd_valid : RuleValid (algebra M) (meaning M) ruleKripkeEvidenceAdd := by
  intro ν _ value left
  obtain ⟨w, φ, hw, hφ, rfl⟩ := den_kripkeEvidence.mp left
  obtain ⟨x, y, hx, hy, ⟨⟩⟩ := den_revise.mp hw
  refine den_combine.mpr ⟨_, _, den_kripkeEvidence.mpr ⟨x, φ, hx, hφ, rfl⟩,
    den_kripkeEvidence.mpr ⟨y, φ, hy, hφ, rfl⟩, ?_⟩
  rw [map_add, Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization.crispEvidence_add,
    map_add]

/-- The singleton premises, read at the matched point and formula. -/
private theorem singleton_reading {ν : String → Option (WMValue M)} {w : State}
    (hw : denote (algebra M) ν (pSingleton (.fvar "pk")) = some (.state w)) :
    ∃ p, denote (algebra M) ν (.fvar "pk") = some (.point p) ∧ w = M.singleton p := by
  obtain ⟨p, hp, same'⟩ := den_singleton.mp hw
  exact ⟨p, hp, WMValue.state.inj same'⟩

theorem kripkeSingletonSat_valid : RuleValid (algebra M) (meaning M) ruleKripkeSingletonSat := by
  intro ν holds value left
  obtain ⟨w, φ, hw, hφ, rfl⟩ := den_kripkeEvidence.mp left
  obtain ⟨p, hp, rfl⟩ := singleton_reading hw
  obtain ⟨a, b, ha, hb, related⟩ := premise_two
    (holds (.relationQuery "kripkeSat" [.fvar "pk", .fvar "phi"]) (by simp [ruleKripkeSingletonSat]))
  rw [meaning_of_parse M (by decide : WMRelation.parse "kripkeSat" = some .kripkeSat)] at related
  obtain ⟨p', φ', rfl, rfl, satisfied⟩ := related
  obtain rfl : p' = p := WMValue.point.inj (same ha hp)
  obtain rfl : φ' = φ := WMValue.modalQuery.inj (same hb hφ)
  rw [M.points_singleton,
    Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization.crispEvidence_singleton_of_satisfies
      M.satisfies p' φ' satisfied]
  exact den_evidenceOne

theorem kripkeSingletonNotSat_valid :
    RuleValid (algebra M) (meaning M) ruleKripkeSingletonNotSat := by
  intro ν holds value left
  obtain ⟨w, φ, hw, hφ, rfl⟩ := den_kripkeEvidence.mp left
  obtain ⟨p, hp, rfl⟩ := singleton_reading hw
  obtain ⟨a, b, ha, hb, related⟩ := premise_two
    (holds (.relationQuery "kripkeNotSat" [.fvar "pk", .fvar "phi"])
      (by simp [ruleKripkeSingletonNotSat]))
  rw [meaning_of_parse M (by decide : WMRelation.parse "kripkeNotSat" = some .kripkeNotSat)]
    at related
  obtain ⟨p', φ', rfl, rfl, refuted⟩ := related
  obtain rfl : p' = p := WMValue.point.inj (same ha hp)
  obtain rfl : φ' = φ := WMValue.modalQuery.inj (same hb hφ)
  rw [M.points_singleton,
    Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization.crispEvidence_singleton_of_not_satisfies
      M.satisfies p' φ' refuted]
  exact den_evidenceOneNegative

theorem genericEvidenceAdd_valid : RuleValid (algebra M) (meaning M) ruleGenericEvidenceAdd := by
  intro ν _ value left
  obtain ⟨w, z, hw, hz, rfl⟩ := den_genericEvidence.mp left
  obtain ⟨x, y, hx, hy, ⟨⟩⟩ := den_revise.mp hw
  refine den_combine.mpr ⟨_, _, den_genericEvidence.mpr ⟨x, z, hx, hz, rfl⟩,
    den_genericEvidence.mpr ⟨y, z, hy, hz, rfl⟩, ?_⟩
  rw [AdditiveWorldModel.extract_add]

theorem queryEquivTransport_valid :
    RuleValid (algebra M) (meaning M) ruleQueryEquivTransport := by
  intro ν holds value left
  obtain ⟨x, z, hx, hz, rfl⟩ := den_genericEvidence.mp left
  obtain ⟨a, b, ha, hb, related⟩ := premise_two
    (holds (.relationQuery "queryEquiv" [.fvar "q1", .fvar "q2"]) (by simp [ruleQueryEquivTransport]))
  rw [meaning_of_parse M (by decide : WMRelation.parse "queryEquiv" = some .queryEquiv)] at related
  obtain ⟨z', z₂, rfl, rfl, equivalent⟩ := related
  obtain rfl : z' = z := WMValue.query.inj (same ha hz)
  exact den_genericEvidence.mpr ⟨x, z₂, hx, hb, by rw [equivalent x]⟩

theorem logicRules_empty (x : WMLogic) : logicRules x = [] := by cases x <;> rfl
theorem tvRules_empty (x : WMTruthValue) : tvRules x = [] := by cases x <;> rfl
theorem intervalRules_empty (x : WMIntervalSemantics) : intervalRules x = [] := by
  cases x <;> rfl
theorem typingRules_empty (x : WMQueryTyping) : typingRules x = [] := by cases x <;> rfl

/-- The 37 rules of the maximal vertex, in the order of its LanguageDef. -/
def maximalRuleList : List RewriteRule :=
  [ruleEvidenceAdd, ruleRevisionComm, ruleRevisionAssoc, ruleCombineComm, ruleCombineZero,
   ruleOverlapExtract, ruleForgetOutside, ruleForgetIdempotent,
   ruleForgetAbsorbSupported, ruleForgetClean,
   ruleCompatibleSymm, ruleFallbackCompatible, ruleFallbackIncompatible,
   rulePartialRevisionCompatible, ruleTrustedGateAll, ruleSourceEvidenceAdd,
   ruleClosureFixpoint, ruleIterUnfolding, rulePolicyTrustedAllCompatible, ruleCascadeAtCard,
   ruleSwapAnomalySymm, ruleSwapAnomalyZero, ruleScheduleErrorSymm,
   ruleAntiHallucination, ruleNoetherConservation,
   ruleExperimentEvidenceAdd, ruleBlackwellPullback, ruleChannelCompId, ruleStochEvidenceAdd,
   ruleChannelCompAssoc, ruleBlackwellUtilityTransport, ruleKleisliIdentity,
   ruleKripkeEvidenceAdd, ruleKripkeSingletonSat, ruleKripkeSingletonNotSat,
   ruleGenericEvidenceAdd, ruleQueryEquivTransport]

theorem maximalRules_eq :
    (wmFullVertexLanguageDef wmFullVertexMaximal).rewrites = maximalRuleList := rfl

/-- The 24 entries of the two congruence lists, in order: 21 rules, three of which
(`ruleOverlapMergeCongLeft`, `ruleOverlapMergeCongRight`, `ruleForgetCongRight`)
occur in both lists. -/
def congruenceRuleList : List RewriteRule :=
  [ruleReviseCongLeft, ruleReviseCongRight, ruleExtractCongLeft, ruleExtractCongRight,
   ruleCombineCongLeft, ruleCombineCongRight,
   ruleForgetCongRight, ruleOverlapMergeCongLeft, ruleOverlapMergeCongRight,
   ruleFallbackRevisionCongLeft, ruleFallbackRevisionCongRight,
   ruleExperimentEvidenceCongLeft, ruleKripkeEvidenceCongLeft, ruleGenericEvidenceCongLeft,
   ruleOverlapMergeCongLeft, ruleOverlapMergeCongRight,
   ruleOverlapFactorCongFirst, ruleOverlapFactorCongSecond, ruleOverlapFactorCongQuery,
   ruleOverlapCorrectCongFirst, ruleOverlapCorrectCongSecond, ruleOverlapCorrectCongFactor,
   ruleForgetCongLeft, ruleForgetCongRight]

theorem congruenceRules_eq :
    allCongruenceRules ++ combinedExtensionCongruenceRules = congruenceRuleList := rfl

/-- **Every rule of the maximal vertex is valid.** -/
theorem maximalRules_valid :
    ∀ rule ∈ (wmFullVertexLanguageDef wmFullVertexMaximal).rewrites,
      RuleValid (algebra M) (meaning M) rule := by
  rw [maximalRules_eq]
  intro rule member
  simp only [maximalRuleList, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h
  exacts [evidenceAdd_valid, revisionComm_valid, revisionAssoc_valid, combineComm_valid,
    combineZero_valid, overlapExtract_valid, forgetOutside_valid, forgetIdempotent_valid,
    forgetAbsorbSupported_valid, forgetClean_valid, compatibleSymm_valid,
    fallbackCompatible_valid, fallbackIncompatible_valid, partialRevisionCompatible_valid,
    trustedGateAll_valid, sourceEvidenceAdd_valid, closureFixpoint_valid, iterUnfolding_valid,
    policyTrustedAllCompatible_valid, cascadeAtCard_valid, swapAnomalySymm_valid,
    swapAnomalyZero_valid, scheduleErrorSymm_valid, antiHallucination_valid,
    noetherConservation_valid, experimentEvidenceAdd_valid, blackwellPullback_valid,
    channelCompId_valid, stochEvidenceAdd_valid, channelCompAssoc_valid,
    blackwellUtilityTransport_valid, kleisliIdentity_valid, kripkeEvidenceAdd_valid,
    kripkeSingletonSat_valid, kripkeSingletonNotSat_valid, genericEvidenceAdd_valid,
    queryEquivTransport_valid]

/-- **Every congruence rule is valid**, in every model: each rewrites one
argument position of one constructor. -/
theorem congruenceRules_valid :
    ∀ rule ∈ allCongruenceRules ++ combinedExtensionCongruenceRules,
      RuleValid (algebra M) (meaning M) rule := by
  rw [congruenceRules_eq]
  intro rule member
  simp only [congruenceRuleList, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h <;> subst h
  · exact congruence_valid _ "Revise" [] [.fvar "W2"] "W1" "W1p" _ rfl rfl rfl
  · exact congruence_valid _ "Revise" [.fvar "W1"] [] "W2" "W2p" _ rfl rfl rfl
  · exact congruence_valid _ "Extract" [] [.fvar "q"] "W" "Wp" _ rfl rfl rfl
  · exact congruence_valid _ "Extract" [.fvar "W"] [] "q" "qp" _ rfl rfl rfl
  · exact congruence_valid _ "Combine" [] [.fvar "e2"] "e1" "e1p" _ rfl rfl rfl
  · exact congruence_valid _ "Combine" [.fvar "e1"] [] "e2" "e2p" _ rfl rfl rfl
  · exact congruence_valid _ "Forget" [.fvar "S"] [] "W" "Wp" _ rfl rfl rfl
  · exact congruence_valid _ "OverlapMerge" [] [.fvar "W2"] "W1" "W1p" _ rfl rfl rfl
  · exact congruence_valid _ "OverlapMerge" [.fvar "W1"] [] "W2" "W2p" _ rfl rfl rfl
  · exact congruence_valid _ "FallbackRevision" [] [.fvar "W2"] "W1" "W1p" _ rfl rfl rfl
  · exact congruence_valid _ "FallbackRevision" [.fvar "W1"] [] "W2" "W2p" _ rfl rfl rfl
  · exact congruence_valid _ "ExperimentEvidence" [] [.fvar "q"] "W" "Wp" _ rfl rfl rfl
  · exact congruence_valid _ "KripkeEvidence" [] [.fvar "phi"] "W" "Wp" _ rfl rfl rfl
  · exact congruence_valid _ "GenericEvidence" [] [.fvar "q"] "W" "Wp" _ rfl rfl rfl
  · exact congruence_valid _ "OverlapMerge" [] [.fvar "W2"] "W1" "W1p" _ rfl rfl rfl
  · exact congruence_valid _ "OverlapMerge" [.fvar "W1"] [] "W2" "W2p" _ rfl rfl rfl
  · exact congruence_valid _ "OverlapFactor" [] [.fvar "W2", .fvar "q"] "W1" "W1p" _ rfl rfl rfl
  · exact congruence_valid _ "OverlapFactor" [.fvar "W1"] [.fvar "q"] "W2" "W2p" _ rfl rfl rfl
  · exact congruence_valid _ "OverlapFactor" [.fvar "W1", .fvar "W2"] [] "q" "qp" _ rfl rfl rfl
  · exact congruence_valid _ "OverlapCorrect" [] [.fvar "e2", .fvar "ov"] "e1" "e1p" _
      rfl rfl rfl
  · exact congruence_valid _ "OverlapCorrect" [.fvar "e1"] [.fvar "ov"] "e2" "e2p" _
      rfl rfl rfl
  · exact congruence_valid _ "OverlapCorrect" [.fvar "e1", .fvar "e2"] [] "ov" "ovp" _
      rfl rfl rfl
  · exact congruence_valid _ "Forget" [] [.fvar "W"] "S" "Sp" _ rfl rfl rfl
  · exact congruence_valid _ "Forget" [.fvar "S"] [] "W" "Wp" _ rfl rfl rfl

end Validity

/-! ## The calculus is sound

**What a denotation forgets.**  A term denotes a value of the model, so its
denotation forgets how the value was built:
* evidence identity: which observations, points or hypotheses contributed
  (two states with equal evidence values are not told apart at evidence sorts);
* scheduling: the order and grouping of revisions, since revision is a
  commutative monoid operation (`revisionComm_valid`, `revisionAssoc_valid`);
* provenance beyond what the model's compatibility relation and trust gates
  read;
* handle identity: two handles that decode to the same value denote the same.
Preservation is a property of single terms, so a run's phase, the rules that
fired and the failed attempts on the way are not observed.

**Relative to a valuation.**  `Certifies` reads rows under the valuation `ρ` of
the free names, which for a checked provider is its handle table: the theorems
below are sound relative to that table, and a handle the table does not decode
denotes nothing. -/

section Soundness

variable {State Query Ev : Type} [EvidenceType State] [ConjugateEvidence Ev]
  [AdditiveWorldModel State Query Ev]
variable {M : WMModel State Query Ev}

/-- Every rule of the maximal vertex has the first-order shape the evaluator
reads. -/
theorem maximalRules_denotable :
    ∀ rule ∈ (wmFullVertexLanguageDef wmFullVertexMaximal).rewrites,
      ruleDenotable rule = true := by
  decide +kernel

/-- So does every congruence rule. -/
theorem congruenceRules_denotable :
    ∀ rule ∈ allCongruenceRules ++ combinedExtensionCongruenceRules,
      ruleDenotable rule = true := by
  decide +kernel

/-- The rules of a full vertex are rules of the maximal vertex. -/
theorem fullRules_in_maximal (v : WMFullVertex) :
    ∀ rule ∈ (wmFullVertexLanguageDef v).rewrites,
      rule ∈ (wmFullVertexLanguageDef wmFullVertexMaximal).rewrites :=
  wmFullVertexRules_subset_of_le (wmFullVertexMaximal_le v)

/-- The rules of a six-axis vertex are rules of the maximal vertex. -/
theorem extRules_in_maximal (v : WMExtVertex) :
    ∀ rule ∈ (wmExtVertexLanguageDef v).rewrites,
      rule ∈ (wmFullVertexLanguageDef wmFullVertexMaximal).rewrites := by
  intro rule member
  have below : wmExtVertexFull ≤ v :=
    ⟨by cases v.overlap <;> trivial, by cases v.forgetting <;> trivial⟩
  have inFull := wmExtVertexRules_subset_of_le below rule member
  have fullEq : (wmExtVertexLanguageDef wmExtVertexFull).rewrites =
      [ruleEvidenceAdd, ruleRevisionComm, ruleRevisionAssoc, ruleCombineComm, ruleCombineZero,
        ruleOverlapExtract, ruleForgetOutside, ruleForgetIdempotent] := rfl
  rw [fullEq] at inFull
  rw [maximalRules_eq]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at inFull
  simp only [maximalRuleList, List.mem_cons]
  rcases inFull with h | h | h | h | h | h | h | h <;> subst h <;> simp

private theorem fullWithCong_cases (v : WMFullVertex) {rule : RewriteRule}
    (member : rule ∈ (wmFullVertexLanguageDefWithCong v).rewrites) :
    rule ∈ (wmFullVertexLanguageDef wmFullVertexMaximal).rewrites ∨
      rule ∈ allCongruenceRules ++ combinedExtensionCongruenceRules := by
  simp only [wmFullVertexLanguageDefWithCong, List.mem_append] at member
  rcases member with member | member
  · exact Or.inl (fullRules_in_maximal v rule member)
  · exact Or.inr (List.mem_append_left _ member)

private theorem extWithCong_cases (v : WMExtVertex) {rule : RewriteRule}
    (member : rule ∈ (wmExtVertexLanguageDefWithCong v).rewrites) :
    rule ∈ (wmFullVertexLanguageDef wmFullVertexMaximal).rewrites ∨
      rule ∈ allCongruenceRules ++ combinedExtensionCongruenceRules := by
  simp only [wmExtVertexLanguageDefWithCong, List.mem_append] at member
  rcases member with member | member
  · exact Or.inl (extRules_in_maximal v rule member)
  · right
    simp only [allCongruenceRules, List.mem_append]
    exact Or.inl (Or.inl member)

theorem fullWithCong_valid (v : WMFullVertex) :
    ∀ rule ∈ (wmFullVertexLanguageDefWithCong v).rewrites,
      RuleValid (algebra M) (meaning M) rule := fun rule member =>
  (fullWithCong_cases v member).elim (maximalRules_valid rule) (congruenceRules_valid rule)

theorem fullWithCong_denotable (v : WMFullVertex) :
    ∀ rule ∈ (wmFullVertexLanguageDefWithCong v).rewrites, ruleDenotable rule = true :=
  fun rule member => (fullWithCong_cases v member).elim (maximalRules_denotable rule)
    (congruenceRules_denotable rule)

theorem extWithCong_valid (v : WMExtVertex) :
    ∀ rule ∈ (wmExtVertexLanguageDefWithCong v).rewrites,
      RuleValid (algebra M) (meaning M) rule := fun rule member =>
  (extWithCong_cases v member).elim (maximalRules_valid rule) (congruenceRules_valid rule)

theorem extWithCong_denotable (v : WMExtVertex) :
    ∀ rule ∈ (wmExtVertexLanguageDefWithCong v).rewrites, ruleDenotable rule = true :=
  fun rule member => (extWithCong_cases v member).elim (maximalRules_denotable rule)
    (congruenceRules_denotable rule)

variable {ρ : String → Option (WMValue M)} {env : RelationEnv}

/-- **Soundness of the WM calculus, at every full vertex, under contexts.**  Under
an environment that certifies `meaning`, a step of the congruence closure, at
any contextual depth, preserves the denotation of its source. -/
theorem wmFullWithCong_step_sound (certified : Certifies (algebra M) (meaning M) ρ env)
    (v : WMFullVertex) {source target : Pattern}
    (step : langReducesUsing env (wmFullVertexLanguageDefWithCong v) source target) :
    ∀ value, denote (algebra M) ρ source = some value →
      denote (algebra M) ρ target = some value :=
  step_preserves certified (fullWithCong_denotable v) (fullWithCong_valid v) step

/-- The same for the calculus without congruence rules: its steps are steps of
the closure. -/
theorem wmFull_step_sound (certified : Certifies (algebra M) (meaning M) ρ env)
    (v : WMFullVertex) {source target : Pattern}
    (step : langReducesUsing env (wmFullVertexLanguageDef v) source target) :
    ∀ value, denote (algebra M) ρ source = some value →
      denote (algebra M) ρ target = some value :=
  wmFullWithCong_step_sound certified v
    (congReducesUsing_of_reducesUsing_full env v source target step)

/-- **Runs.**  Every finite run of the congruence closure preserves the
denotation. -/
theorem wmFullWithCong_run_sound (certified : Certifies (algebra M) (meaning M) ρ env)
    (v : WMFullVertex) {source target : Pattern}
    (run : Relation.ReflTransGen (langReducesUsing env (wmFullVertexLanguageDefWithCong v))
      source target) :
    ∀ value, denote (algebra M) ρ source = some value →
      denote (algebra M) ρ target = some value := by
  induction run with
  | refl => exact fun _ h => h
  | tail _ last ih =>
      exact fun value h => wmFullWithCong_step_sound certified v last value (ih value h)

/-- At six-axis vertices, steps of the congruence closure preserve the
denotation. -/
theorem wmExtWithCong_step_sound (certified : Certifies (algebra M) (meaning M) ρ env)
    (v : WMExtVertex) {source target : Pattern}
    (step : langReducesUsing env (wmExtVertexLanguageDefWithCong v) source target) :
    ∀ value, denote (algebra M) ρ source = some value →
      denote (algebra M) ρ target = some value :=
  step_preserves certified (extWithCong_denotable v) (extWithCong_valid v) step

/-- And so do their runs. -/
theorem wmExtWithCong_run_sound (certified : Certifies (algebra M) (meaning M) ρ env)
    (v : WMExtVertex) {source target : Pattern}
    (run : Relation.ReflTransGen (langReducesUsing env (wmExtVertexLanguageDefWithCong v))
      source target) :
    ∀ value, denote (algebra M) ρ source = some value →
      denote (algebra M) ρ target = some value := by
  induction run with
  | refl => exact fun _ h => h
  | tail _ last ih =>
      exact fun value h => wmExtWithCong_step_sound certified v last value (ih value h)

end Soundness

#print axioms maximalRules_valid
#print axioms congruenceRules_valid
#print axioms maximalRules_denotable
#print axioms congruenceRules_denotable
#print axioms extRules_in_maximal
#print axioms wmFullWithCong_step_sound
#print axioms wmFull_step_sound
#print axioms wmFullWithCong_run_sound
#print axioms wmExtWithCong_step_sound
#print axioms wmExtWithCong_run_sound
#print axioms WMModel.fallbackRevision_of_compatible
#print axioms den_revise
#print axioms den_kripkeEvidence_crisp
#print axioms compose_eq_some

end Mettapedia.OSLF.Framework.WMCalculusDenotationalSoundness
