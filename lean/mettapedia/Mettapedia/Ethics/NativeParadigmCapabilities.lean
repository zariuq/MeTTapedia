import Mettapedia.Ethics.MoralUndecidability

/-!
# Native ethical paradigm capabilities

Verdict-set representability does not make an ethical paradigm native.  A
native capability must expose the operations and evidence characteristic of
the paradigm itself.  This module separates three such capabilities:

* a deontic policy applies rules and returns either a compliance receipt or an
  explicitly authorized override receipt;
* an empirical consequential policy observes candidate outcomes and returns
  evidence that the selected action is optimal for its declared score; and
* a virtue-learning policy updates a disposition and returns evidence that
  the resulting action hits every active target.

`NativeEthicalAgent` carries all three without collapsing their evidence.
Its decision type is a dependent sum indexed by the selected paradigm, so an
identical action can retain different justifications.

The concrete rescue specimen supplies positive and negative canaries:

* ordinary compliance and emergency override are both inhabited;
* an override in an ordinary situation cannot be forged;
* empirical short-horizon optimization selects waiting;
* learned courage selects crossing in the emergency, even though crossing is
  not optimal for that declared short-horizon score; and
* deontic override and virtue motivation can select the same action while
  remaining distinct dependent decisions.

The final computability theorems qualify exact cross-paradigm embeddings: the
responsiveness code has neither a finite computable duty theory nor a finite
computable conditional-target theory.  Its semantic embeddings remain valid,
but they retain the source theory's undecidable content.
-/

set_option autoImplicit false

namespace Mettapedia.Ethics.NativeParadigmCapabilities

open Mettapedia.Ethics.MoralUndecidability

universe uSituation uAction uRule uReason uObservation uScore
  uExperience uDisposition uVirtue

/-! ## Deontic rule following and authorized override -/

/-- A deontic policy separates applicability, compliance, and authority to
override.  An override is not an untyped escape hatch: it has its own
predicate and must be exhibited in a receipt. -/
structure DeonticPolicy
    (Situation : Type uSituation) (Action : Type uAction)
    (Rule : Type uRule) (Reason : Type uReason) where
  applies : Rule → Situation → Prop
  complies : Rule → Situation → Action → Prop
  overrideAllowed : Rule → Reason → Situation → Action → Prop

/-- Proof that an applicable rule was intentionally violated under a named,
authorized exception. -/
structure OverrideReceipt
    {Situation : Type uSituation} {Action : Type uAction}
    {Rule : Type uRule} {Reason : Type uReason}
    (policy : DeonticPolicy Situation Action Rule Reason)
    (situation : Situation) (action : Action) : Type
    (max uSituation uAction uRule uReason) where
  rule : Rule
  reason : Reason
  applicable : policy.applies rule situation
  violates : ¬ policy.complies rule situation action
  authorized : policy.overrideAllowed rule reason situation action

/-- Deontic justification preserves whether the action followed a rule or
used an authorized override. -/
inductive DeonticReceipt
    {Situation : Type uSituation} {Action : Type uAction}
    {Rule : Type uRule} {Reason : Type uReason}
    (policy : DeonticPolicy Situation Action Rule Reason)
    (situation : Situation) (action : Action) : Type
    (max uSituation uAction uRule uReason) where
  | follows (rule : Rule)
      (applicable : policy.applies rule situation)
      (compliant : policy.complies rule situation action)
  | overrides (receipt : OverrideReceipt policy situation action)

/-! ## Empirical consequential observation and optimization -/

/-- A consequential policy makes its empirical observation and scoring map
explicit.  The order on scores is supplied independently. -/
structure EmpiricalConsequentialPolicy
    (Situation : Type uSituation) (Action : Type uAction)
    (Observation : Type uObservation) (Score : Type uScore) where
  observe : Situation → Action → Observation
  evaluate : Observation → Score

/-- The selected action scores at least as highly as every alternative under
the declared empirical observation map. -/
def EmpiricalConsequentialPolicy.IsOptimal
    {Situation : Type uSituation} {Action : Type uAction}
    {Observation : Type uObservation} {Score : Type uScore}
    [Preorder Score]
    (policy : EmpiricalConsequentialPolicy Situation Action Observation Score)
    (situation : Situation) (action : Action) : Prop :=
  ∀ alternative,
    policy.evaluate (policy.observe situation alternative) ≤
      policy.evaluate (policy.observe situation action)

/-- A consequential receipt retains the observation used for the selected
action as well as the global optimality claim. -/
structure ConsequentialReceipt
    {Situation : Type uSituation} {Action : Type uAction}
    {Observation : Type uObservation} {Score : Type uScore}
    [Preorder Score]
    (policy : EmpiricalConsequentialPolicy Situation Action Observation Score)
    (situation : Situation) (action : Action) : Type
    (max uSituation uAction uObservation uScore) where
  observation : Observation
  observed : observation = policy.observe situation action
  optimal : policy.IsOptimal situation action

/-! ## Disposition-level virtue learning -/

/-- A virtue-learning policy has diachronic state.  Experience updates a
disposition; the resulting disposition selects an action; active virtue
fields impose targets on that action.  External utility is deliberately not
an argument of `update` or `act`. -/
structure VirtueLearningPolicy
    (Situation : Type uSituation) (Action : Type uAction)
    (Experience : Type uExperience) (Disposition : Type uDisposition)
    (Virtue : Type uVirtue) where
  update : Disposition → Experience → Disposition
  act : Disposition → Situation → Action
  field : Virtue → Situation → Prop
  mode : Virtue → Situation → Action → Prop
  target : Virtue → Situation → Action → Prop

/-- All targets active in a situation are hit by the action selected from the
current disposition. -/
def VirtueLearningPolicy.HitsActiveTargets
    {Situation : Type uSituation} {Action : Type uAction}
    {Experience : Type uExperience} {Disposition : Type uDisposition}
    {Virtue : Type uVirtue}
    (policy : VirtueLearningPolicy Situation Action Experience Disposition Virtue)
    (disposition : Disposition) (situation : Situation) : Prop :=
  ∀ virtue, policy.field virtue situation →
    policy.mode virtue situation (policy.act disposition situation) ∧
      policy.target virtue situation (policy.act disposition situation)

/-- A learning receipt retains the updated disposition, the induced action,
and evidence that every active target is hit. -/
structure VirtueLearningReceipt
    {Situation : Type uSituation} {Action : Type uAction}
    {Experience : Type uExperience} {Disposition : Type uDisposition}
    {Virtue : Type uVirtue}
    (policy : VirtueLearningPolicy Situation Action Experience Disposition Virtue)
    (before : Disposition) (experience : Experience)
    (situation : Situation) (action : Action) : Type
    (max uSituation uAction uExperience uDisposition uVirtue) where
  after : Disposition
  updated : after = policy.update before experience
  acted : policy.act after situation = action
  hitsTargets : policy.HitsActiveTargets after situation

/-! ## One agent, three native modes, dependent evidence -/

/-- The ethical mode chosen for one decision. -/
inductive EthicalMode : Type
  | deontic
  | consequential
  | virtue
  deriving DecidableEq, Repr

/-- An agent carrying all three capabilities as independent fields. -/
structure NativeEthicalAgent
    (Situation : Type uSituation) (Action : Type uAction)
    (Rule : Type uRule) (Reason : Type uReason)
    (Observation : Type uObservation) (Score : Type uScore)
    (Experience : Type uExperience) (Disposition : Type uDisposition)
    (Virtue : Type uVirtue) [Preorder Score] where
  deontic : DeonticPolicy Situation Action Rule Reason
  consequential :
    EmpiricalConsequentialPolicy Situation Action Observation Score
  virtue : VirtueLearningPolicy Situation Action Experience Disposition Virtue

/-- The evidence family selected by an ethical mode.  Constructors retain
the native receipt rather than coercing all paradigms to one proposition. -/
inductive NativeEthicalAgent.Justification
    {Situation : Type uSituation} {Action : Type uAction}
    {Rule : Type uRule} {Reason : Type uReason}
    {Observation : Type uObservation} {Score : Type uScore}
    {Experience : Type uExperience} {Disposition : Type uDisposition}
    {Virtue : Type uVirtue} [Preorder Score]
    (agent : NativeEthicalAgent Situation Action Rule Reason Observation Score
      Experience Disposition Virtue)
    (before : Disposition) (experience : Experience)
    (situation : Situation) : EthicalMode → Action → Type
    (max uSituation uAction uRule uReason uObservation uScore
      uExperience uDisposition uVirtue) where
  | deontic {action : Action}
      (receipt : DeonticReceipt agent.deontic situation action) :
      Justification agent before experience situation .deontic action
  | consequential {action : Action}
      (receipt : ConsequentialReceipt agent.consequential situation action) :
      Justification agent before experience situation .consequential action
  | virtue {action : Action}
      (receipt : VirtueLearningReceipt agent.virtue before experience
        situation action) :
      Justification agent before experience situation .virtue action

/-- A decision retains its selected paradigm, action, and paradigm-specific
justification. -/
abbrev NativeEthicalAgent.Decision
    {Situation : Type uSituation} {Action : Type uAction}
    {Rule : Type uRule} {Reason : Type uReason}
    {Observation : Type uObservation} {Score : Type uScore}
    {Experience : Type uExperience} {Disposition : Type uDisposition}
    {Virtue : Type uVirtue} [Preorder Score]
    (agent : NativeEthicalAgent Situation Action Rule Reason Observation Score
      Experience Disposition Virtue)
    (before : Disposition) (experience : Experience)
    (situation : Situation) :=
  Sigma fun mode : EthicalMode =>
    Sigma fun action : Action =>
      agent.Justification before experience situation mode action

def NativeEthicalAgent.Decision.mode
    {Situation : Type uSituation} {Action : Type uAction}
    {Rule : Type uRule} {Reason : Type uReason}
    {Observation : Type uObservation} {Score : Type uScore}
    {Experience : Type uExperience} {Disposition : Type uDisposition}
    {Virtue : Type uVirtue} [Preorder Score]
    {agent : NativeEthicalAgent Situation Action Rule Reason Observation Score
      Experience Disposition Virtue}
    {before : Disposition} {experience : Experience} {situation : Situation}
    (decision : agent.Decision before experience situation) : EthicalMode :=
  decision.1

def NativeEthicalAgent.Decision.action
    {Situation : Type uSituation} {Action : Type uAction}
    {Rule : Type uRule} {Reason : Type uReason}
    {Observation : Type uObservation} {Score : Type uScore}
    {Experience : Type uExperience} {Disposition : Type uDisposition}
    {Virtue : Type uVirtue} [Preorder Score]
    {agent : NativeEthicalAgent Situation Action Rule Reason Observation Score
      Experience Disposition Virtue}
    {before : Disposition} {experience : Experience} {situation : Situation}
    (decision : agent.Decision before experience situation) : Action :=
  decision.2.1

/-! ## A concrete rescue canary -/

inductive RescueSituation : Type
  | ordinary
  | emergency
  deriving DecidableEq, Repr

inductive RescueAction : Type
  | wait
  | cross
  deriving DecidableEq, Repr

inductive RescueRule : Type
  | stayPut
  deriving DecidableEq, Repr

inductive RescueReason : Type
  | saveLife
  deriving DecidableEq, Repr

inductive RescueExperience : Type
  | practicedAid
  deriving DecidableEq, Repr

inductive CourageDisposition : Type
  | untrained
  | trained
  deriving DecidableEq, Repr

inductive RescueVirtue : Type
  | courage
  deriving DecidableEq, Repr

/-- The standing rule says to wait.  Crossing is an authorized violation only
in an emergency and only for the stated rescue reason. -/
def rescueDeonticPolicy :
    DeonticPolicy RescueSituation RescueAction RescueRule RescueReason where
  applies _ _ := True
  complies _ _ action := action = .wait
  overrideAllowed _ reason situation action :=
    reason = .saveLife ∧ situation = .emergency ∧ action = .cross

/-- Ordinary rule-following is inhabited. -/
def ordinaryWaitReceipt :
    DeonticReceipt rescueDeonticPolicy .ordinary .wait :=
  .follows .stayPut trivial rfl

/-- Rule-following remains available during the emergency. -/
def emergencyWaitReceipt :
    DeonticReceipt rescueDeonticPolicy .emergency .wait :=
  .follows .stayPut trivial rfl

/-- Crossing during the emergency has an explicit authorized-override
receipt. -/
def emergencyCrossingOverride :
    OverrideReceipt rescueDeonticPolicy .emergency .cross where
  rule := .stayPut
  reason := .saveLife
  applicable := trivial
  violates := by simp [rescueDeonticPolicy]
  authorized := by simp [rescueDeonticPolicy]

def emergencyCrossingDeonticReceipt :
    DeonticReceipt rescueDeonticPolicy .emergency .cross :=
  .overrides emergencyCrossingOverride

/-- The same crossing cannot be classified as an authorized override in an
ordinary situation. -/
theorem ordinaryCrossing_has_no_override :
    ¬ Nonempty (OverrideReceipt rescueDeonticPolicy .ordinary .cross) := by
  rintro ⟨receipt⟩
  simpa [rescueDeonticPolicy] using receipt.authorized

/-- Short-horizon empirical evidence assigns score two to waiting and one to
crossing. -/
def shortHorizonConsequentialPolicy :
    EmpiricalConsequentialPolicy RescueSituation RescueAction Nat Nat where
  observe _ action :=
    match action with
    | .wait => 2
    | .cross => 1
  evaluate score := score

theorem wait_is_shortHorizon_optimal (situation : RescueSituation) :
    shortHorizonConsequentialPolicy.IsOptimal situation .wait := by
  intro alternative
  cases alternative <;> simp [shortHorizonConsequentialPolicy]

theorem cross_is_not_shortHorizon_optimal (situation : RescueSituation) :
    ¬ shortHorizonConsequentialPolicy.IsOptimal situation .cross := by
  intro optimal
  have := optimal .wait
  simp [shortHorizonConsequentialPolicy] at this

def emergencyWaitConsequentialReceipt :
    ConsequentialReceipt shortHorizonConsequentialPolicy .emergency .wait where
  observation := 2
  observed := rfl
  optimal := wait_is_shortHorizon_optimal .emergency

/-- Practicing aid cultivates the trained disposition.  The trained policy
acts courageously in an emergency and otherwise waits. -/
def courageLearningPolicy :
    VirtueLearningPolicy RescueSituation RescueAction RescueExperience
      CourageDisposition RescueVirtue where
  update _ _ := .trained
  act disposition situation :=
    match disposition, situation with
    | .trained, .emergency => .cross
    | _, _ => .wait
  field _ situation := situation = .emergency
  mode _ _ action := action = .cross
  target _ _ action := action = .cross

def learnedCourageReceipt :
    VirtueLearningReceipt courageLearningPolicy .untrained .practicedAid
      .emergency .cross where
  after := .trained
  updated := rfl
  acted := rfl
  hitsTargets := by
    intro virtue active
    cases virtue
    simp [courageLearningPolicy]

/-- The courage theory and the declared short-horizon optimizer choose
different actions.  This witnesses different *theory content*, not a limit on
cross-paradigm expressibility: `OptimizerVirtueBridge` separately constructs a
virtue-learning theory that behaves exactly as this optimizer. -/
theorem learnedCourage_not_shortHorizon_optimal :
    ¬ shortHorizonConsequentialPolicy.IsOptimal .emergency .cross :=
  cross_is_not_shortHorizon_optimal .emergency

def rescueAgent :
    NativeEthicalAgent RescueSituation RescueAction RescueRule RescueReason
      Nat Nat RescueExperience CourageDisposition RescueVirtue where
  deontic := rescueDeonticPolicy
  consequential := shortHorizonConsequentialPolicy
  virtue := courageLearningPolicy

def deonticEmergencyDecision :
    rescueAgent.Decision .untrained .practicedAid .emergency :=
  ⟨.deontic, ⟨.cross, .deontic emergencyCrossingDeonticReceipt⟩⟩

def consequentialEmergencyDecision :
    rescueAgent.Decision .untrained .practicedAid .emergency :=
  ⟨.consequential, ⟨.wait, .consequential emergencyWaitConsequentialReceipt⟩⟩

def virtueEmergencyDecision :
    rescueAgent.Decision .untrained .practicedAid .emergency :=
  ⟨.virtue, ⟨.cross, .virtue learnedCourageReceipt⟩⟩

/-- Deontic override and learned virtue select the same visible action. -/
theorem deontic_virtue_same_action :
    deonticEmergencyDecision.action = virtueEmergencyDecision.action :=
  rfl

/-- Their dependent decisions remain distinct because the justification mode
is retained. -/
theorem deontic_virtue_distinct_decisions :
    deonticEmergencyDecision ≠ virtueEmergencyDecision := by
  intro equality
  have modeEquality := congrArg NativeEthicalAgent.Decision.mode equality
  cases modeEquality

/-- The consequential decision selects a different action on the same
situation under its declared score. -/
theorem consequential_virtue_different_actions :
    consequentialEmergencyDecision.action ≠ virtueEmergencyDecision.action := by
  decide

/-! ## Computability of exact finite embeddings -/

/-- The responsiveness code has no finite duty theory with computably
judgeable duties. -/
theorem responsiveness_has_no_computable_finiteDutyTheory :
    ¬ Exists fun theory : FiniteDutyTheory =>
      (∀ i, ComputablePred (theory.duty i)) ∧
        theory.compliance = responsivenessCode := by
  rintro ⟨theory, computableDuties, classifies⟩
  exact no_computable_finiteDutyTheory_for_responsiveness theory
    computableDuties classifies

/-- Nor does it have a finite conditional-target theory whose active
target checks are all computable. -/
theorem responsiveness_has_no_computable_finiteTargetTheory :
    ¬ Exists fun theory : FiniteTargetTheory =>
      (∀ i, ComputablePred fun action =>
        action ∈ theory.virtueField i → theory.target i action) ∧
      theory.targetCompliance = responsivenessCode := by
  rintro ⟨theory, computableTargets, classifies⟩
  have consequential : Consequentialist theory.targetCompliance := by
    rw [classifies]
    exact responsivenessCode_consequentialist
  have nontrivial : MorallyNontrivial theory.targetCompliance := by
    rw [classifies]
    exact responsivenessCode_nontrivial
  exact finiteTargetTheory_computability_boundary theory computableTargets
    consequential nontrivial

/-! ## Consolidated capability boundary -/

/-- The rescue specimen exhibits all three native capabilities and their
non-collapse boundaries in one statement. -/
theorem native_paradigm_capability_boundary :
    Nonempty (DeonticReceipt rescueDeonticPolicy .ordinary .wait) ∧
      Nonempty (OverrideReceipt rescueDeonticPolicy .emergency .cross) ∧
      ¬ Nonempty (OverrideReceipt rescueDeonticPolicy .ordinary .cross) ∧
      shortHorizonConsequentialPolicy.IsOptimal .emergency .wait ∧
      ¬ shortHorizonConsequentialPolicy.IsOptimal .emergency .cross ∧
      Nonempty (VirtueLearningReceipt courageLearningPolicy .untrained
        .practicedAid .emergency .cross) ∧
      deonticEmergencyDecision.action = virtueEmergencyDecision.action ∧
      deonticEmergencyDecision ≠ virtueEmergencyDecision ∧
      consequentialEmergencyDecision.action ≠
        virtueEmergencyDecision.action :=
  ⟨⟨ordinaryWaitReceipt⟩,
    ⟨emergencyCrossingOverride⟩,
    ordinaryCrossing_has_no_override,
    wait_is_shortHorizon_optimal .emergency,
    learnedCourage_not_shortHorizon_optimal,
    ⟨learnedCourageReceipt⟩,
    deontic_virtue_same_action,
    deontic_virtue_distinct_decisions,
    consequential_virtue_different_actions⟩

/-! ## Axiom audit -/

#print axioms ordinaryCrossing_has_no_override
#print axioms wait_is_shortHorizon_optimal
#print axioms cross_is_not_shortHorizon_optimal
#print axioms learnedCourageReceipt
#print axioms learnedCourage_not_shortHorizon_optimal
#print axioms deontic_virtue_same_action
#print axioms deontic_virtue_distinct_decisions
#print axioms consequential_virtue_different_actions
#print axioms responsiveness_has_no_computable_finiteDutyTheory
#print axioms responsiveness_has_no_computable_finiteTargetTheory
#print axioms native_paradigm_capability_boundary

end Mettapedia.Ethics.NativeParadigmCapabilities
