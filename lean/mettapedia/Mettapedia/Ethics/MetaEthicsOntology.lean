import Mettapedia.Ethics.Core

/-!
# Typed Core of the Formal Ethics Ontology

This module reconstructs the central ontological distinctions used by the
Formal Ethics Ontology in ordinary dependent types.  It does not import the
whole SUMO upper ontology.  Instead it keeps the parts needed for ethical
theory comparison explicit:

* agents act in situations and face nonempty choice points;
* ethical theories belong to a structured family hierarchy;
* a theory may contain both native ethical sentences and background sentences
  that support native ones;
* arguments and justification are objects, not Boolean labels; and
* metaethical theories are theories *about* ethical theories, not a subclass
  of ethical theories.

The construction is intentionally prior to any claim that deontological,
utilitarian, or virtue theories are equivalent.  Those claims must be proved
by translations between the concrete theory structures built on this core.
-/

set_option autoImplicit false

namespace Mettapedia.Ethics.MetaEthicsOntology

open Mettapedia.Ethics

universe uAgent uSituation uAction uSentence uField

/-! ## Ethical-theory hierarchy -/

/-- Families of ethical theories retained from the source ontology.

`ethical` is the common root.  The remaining constructors name genuine
theory families rather than merely tagging a single moral verdict. -/
inductive EthicalTheoryKind : Type
  | ethical
  | valueJudgment
  | simpleActionValueJudgment
  | deontological
  | deontologicalImperative
  | utilitarian
  | consequentialist
  | consequentialistUtilitarian
  | hedonisticUtilitarian
  | generalVirtue
  | virtue
  | targetCenteredVirtue
  | completeTargetCenteredVirtue
  | ruleConsequentialist
  | twoLevelUtilitarian
  | kantianDeontological
  deriving DecidableEq, Repr

/-- The explicitly declared specialization relation between ethical-theory
families. -/
inductive EthicalTheoryKind.Specializes :
    EthicalTheoryKind → EthicalTheoryKind → Prop
  | refl (kind) : Specializes kind kind
  | valueJudgmentEthical : Specializes .valueJudgment .ethical
  | simpleActionValueJudgmentValue :
      Specializes .simpleActionValueJudgment .valueJudgment
  | deontologicalEthical : Specializes .deontological .ethical
  | imperativeDeontological :
      Specializes .deontologicalImperative .deontological
  | utilitarianEthical : Specializes .utilitarian .ethical
  | consequentialistEthical : Specializes .consequentialist .ethical
  | consequentialistUtilitarianConsequentialist :
      Specializes .consequentialistUtilitarian .consequentialist
  | consequentialistUtilitarianUtilitarian :
      Specializes .consequentialistUtilitarian .utilitarian
  | hedonisticUtilitarianUtilitarian :
      Specializes .hedonisticUtilitarian .utilitarian
  | generalVirtueEthical : Specializes .generalVirtue .ethical
  | virtueGeneralVirtue : Specializes .virtue .generalVirtue
  | targetCenteredVirtueGeneralVirtue :
      Specializes .targetCenteredVirtue .generalVirtue
  | completeTargetCenteredVirtueTargetCentered :
      Specializes .completeTargetCenteredVirtue .targetCenteredVirtue
  | ruleConsequentialistConsequentialist :
      Specializes .ruleConsequentialist .consequentialist
  | ruleConsequentialistImperative :
      Specializes .ruleConsequentialist .deontologicalImperative
  | twoLevelUtilitarianEthical :
      Specializes .twoLevelUtilitarian .ethical
  | kantianDeontologicalImperative :
      Specializes .kantianDeontological .deontologicalImperative
  | trans {first second third}
      (h₁ : Specializes first second) (h₂ : Specializes second third) :
      Specializes first third

theorem EthicalTheoryKind.Specializes.targetCenteredVirtue_ethical :
    EthicalTheoryKind.Specializes .targetCenteredVirtue .ethical :=
  .trans .targetCenteredVirtueGeneralVirtue .generalVirtueEthical

theorem EthicalTheoryKind.Specializes.virtue_ethical :
    EthicalTheoryKind.Specializes .virtue .ethical :=
  .trans .virtueGeneralVirtue .generalVirtueEthical

theorem EthicalTheoryKind.Specializes.imperative_ethical :
    EthicalTheoryKind.Specializes .deontologicalImperative .ethical :=
  .trans .imperativeDeontological .deontologicalEthical

/-- The agent-centered virtue branch. This predicate is used to prove that
the source ontology does not place target-centered virtue ethics below
agent-centered virtue ethics. -/
def EthicalTheoryKind.AgentVirtueBranch : EthicalTheoryKind → Prop
  | .virtue => True
  | _ => False

/-- The target-centered virtue branch, including its complete subfamily. -/
def EthicalTheoryKind.TargetVirtueBranch : EthicalTheoryKind → Prop
  | .targetCenteredVirtue | .completeTargetCenteredVirtue => True
  | _ => False

theorem EthicalTheoryKind.Specializes.agentBranch_downward
    {first second : EthicalTheoryKind}
    (specializes : Specializes first second) :
    second.AgentVirtueBranch → first.AgentVirtueBranch := by
  induction specializes with
  | refl => exact id
  | trans _ _ firstToSecond secondToThird =>
      exact fun thirdAgent => firstToSecond (secondToThird thirdAgent)
  | _ => simp [EthicalTheoryKind.AgentVirtueBranch]

theorem EthicalTheoryKind.Specializes.targetBranch_downward
    {first second : EthicalTheoryKind}
    (specializes : Specializes first second) :
    second.TargetVirtueBranch → first.TargetVirtueBranch := by
  induction specializes with
  | refl => exact id
  | completeTargetCenteredVirtueTargetCentered => exact id
  | trans _ _ firstToSecond secondToThird =>
      exact fun thirdTarget => firstToSecond (secondToThird thirdTarget)
  | _ => simp [EthicalTheoryKind.TargetVirtueBranch]

/-- Agent-centered and target-centered virtue ethics are sibling theory
families, not a parent and child. -/
theorem EthicalTheoryKind.targetCentered_not_specializes_virtue :
    ¬ EthicalTheoryKind.Specializes .targetCenteredVirtue .virtue := by
  intro specializes
  have targetIsAgent := specializes.agentBranch_downward (by trivial)
  exact targetIsAgent

theorem EthicalTheoryKind.virtue_not_specializes_targetCentered :
    ¬ EthicalTheoryKind.Specializes .virtue .targetCenteredVirtue := by
  intro specializes
  have virtueIsTarget := specializes.targetBranch_downward (by trivial)
  exact virtueIsTarget

/-- Sentence families retained from the source ontology. The hierarchy keeps
action judgments, situational judgments, imperative sentences, utility
assignments/comparisons, and virtue-target sentences distinct. -/
inductive EthicalSentenceKind : Type
  | ethical
  | valueJudgment
  | simpleValueJudgment
  | simpleActionValueJudgment
  | simpleSituationalActionValueJudgment
  | deontological
  | imperative
  | simpleImperative
  | utilitarian
  | simpleUtilitarian
  | utilityAssignment
  | utilityComparison
  | generalVirtue
  | simpleGeneralVirtue
  | virtue
  | simpleVirtue
  | simpleVirtueDesire
  | minimalVirtueDesire
  | targetCenteredVirtue
  | simpleTargetCenteredVirtue
  | virtueAspect
  | simpleVirtueTarget
  | fieldTargetVirtueAspect
  | completeVirtueAspect
  deriving DecidableEq, Repr

/-- Declared specialization among ethical sentence families. -/
inductive EthicalSentenceKind.Specializes :
    EthicalSentenceKind → EthicalSentenceKind → Prop
  | refl (kind) : Specializes kind kind
  | valueJudgmentEthical : Specializes .valueJudgment .ethical
  | simpleValueJudgmentValue :
      Specializes .simpleValueJudgment .valueJudgment
  | actionValueJudgmentSimple :
      Specializes .simpleActionValueJudgment .simpleValueJudgment
  | situationalActionValueJudgmentValue :
      Specializes .simpleSituationalActionValueJudgment .valueJudgment
  | deontologicalEthical : Specializes .deontological .ethical
  | imperativeDeontological : Specializes .imperative .deontological
  | simpleImperativeImperative : Specializes .simpleImperative .imperative
  | utilitarianEthical : Specializes .utilitarian .ethical
  | simpleUtilitarianUtilitarian :
      Specializes .simpleUtilitarian .utilitarian
  | utilityAssignmentSimple :
      Specializes .utilityAssignment .simpleUtilitarian
  | utilityComparisonSimple :
      Specializes .utilityComparison .simpleUtilitarian
  | generalVirtueEthical : Specializes .generalVirtue .ethical
  | simpleGeneralVirtueGeneral :
      Specializes .simpleGeneralVirtue .generalVirtue
  | virtueGeneral : Specializes .virtue .generalVirtue
  | simpleVirtueVirtue : Specializes .simpleVirtue .virtue
  | simpleVirtueDesireVirtue :
      Specializes .simpleVirtueDesire .virtue
  | minimalVirtueDesireSimple :
      Specializes .minimalVirtueDesire .simpleVirtueDesire
  | targetCenteredVirtueGeneral :
      Specializes .targetCenteredVirtue .generalVirtue
  | simpleTargetCenteredVirtueTarget :
      Specializes .simpleTargetCenteredVirtue .targetCenteredVirtue
  | simpleTargetCenteredVirtueSimpleGeneral :
      Specializes .simpleTargetCenteredVirtue .simpleGeneralVirtue
  | virtueAspectTarget : Specializes .virtueAspect .targetCenteredVirtue
  | simpleVirtueTargetAspect :
      Specializes .simpleVirtueTarget .virtueAspect
  | fieldTargetVirtueAspectTarget :
      Specializes .fieldTargetVirtueAspect .targetCenteredVirtue
  | completeVirtueAspectTarget :
      Specializes .completeVirtueAspect .targetCenteredVirtue
  | trans {first second third}
      (h₁ : Specializes first second) (h₂ : Specializes second third) :
      Specializes first third

/-- Whether a sentence family is native to a theory family. Background
sentences need not satisfy this predicate; they enter a theory through an
explicit support relation instead. -/
def EthicalSentenceKind.NativeFor
    (sentence : EthicalSentenceKind) : EthicalTheoryKind → Prop
  | .ethical => sentence.Specializes .ethical
  | .valueJudgment => sentence.Specializes .valueJudgment
  | .simpleActionValueJudgment =>
      sentence.Specializes .simpleActionValueJudgment
  | .deontological => sentence.Specializes .deontological
  | .deontologicalImperative => sentence.Specializes .imperative
  | .utilitarian => sentence.Specializes .utilitarian
  | .consequentialist => sentence.Specializes .ethical
  | .consequentialistUtilitarian => sentence.Specializes .utilitarian
  | .hedonisticUtilitarian => sentence.Specializes .utilitarian
  | .generalVirtue => sentence.Specializes .generalVirtue
  | .virtue => sentence.Specializes .virtue
  | .targetCenteredVirtue => sentence.Specializes .targetCenteredVirtue
  | .completeTargetCenteredVirtue =>
      sentence.Specializes .targetCenteredVirtue
  | .ruleConsequentialist => sentence.Specializes .imperative
  | .twoLevelUtilitarian => sentence.Specializes .ethical
  | .kantianDeontological => sentence.Specializes .imperative

theorem EthicalSentenceKind.targetCenteredVirtue_native_for_generalVirtue :
    EthicalSentenceKind.targetCenteredVirtue.NativeFor
      EthicalTheoryKind.generalVirtue :=
  .targetCenteredVirtueGeneral

/-- Sentence families belonging specifically to the agent-centered virtue
branch. -/
def EthicalSentenceKind.AgentVirtueBranch : EthicalSentenceKind → Prop
  | .virtue | .simpleVirtue | .simpleVirtueDesire
  | .minimalVirtueDesire => True
  | _ => False

theorem EthicalSentenceKind.Specializes.agentBranch_downward
    {first second : EthicalSentenceKind}
    (specializes : Specializes first second) :
    second.AgentVirtueBranch → first.AgentVirtueBranch := by
  induction specializes with
  | refl => exact id
  | simpleVirtueVirtue | simpleVirtueDesireVirtue
  | minimalVirtueDesireSimple => exact id
  | trans _ _ firstToSecond secondToThird =>
      exact fun thirdAgent => firstToSecond (secondToThird thirdAgent)
  | _ => simp [EthicalSentenceKind.AgentVirtueBranch]

theorem EthicalSentenceKind.targetCenteredVirtue_not_native_for_virtue :
    ¬ EthicalSentenceKind.targetCenteredVirtue.NativeFor
      EthicalTheoryKind.virtue := by
  intro specializes
  have targetIsAgent := specializes.agentBranch_downward (by trivial)
  exact targetIsAgent

theorem EthicalSentenceKind.utilityComparison_native_for_utilitarian :
    EthicalSentenceKind.utilityComparison.NativeFor
      EthicalTheoryKind.utilitarian :=
  .trans .utilityComparisonSimple .simpleUtilitarianUtilitarian

/-- Ethical and metaethical theories occupy distinct branches.  This mirrors
the source ontology's decision not to classify a theory *about ethical
theories* as itself an ethical theory. -/
inductive TheoryDomain : Type
  | ethical (kind : EthicalTheoryKind)
  | metaethical
  deriving DecidableEq, Repr

@[simp] theorem TheoryDomain.metaethical_ne_ethical
    (kind : EthicalTheoryKind) :
    TheoryDomain.metaethical ≠ .ethical kind := by
  simp

/-! ## Agents, situations, actions, and choice points -/

/-- A nonempty set of actions available to one agent in one situation.

The capability relation is retained explicitly.  Mutual exclusion is not
built in because the source ontology marks it as a substantive question rather
than part of the definition of every choice point. -/
structure SituatedChoicePoint
    (Agent : Type uAgent) (Situation : Type uSituation)
    (Action : Type uAction) where
  agent : Agent
  situation : Situation
  options : Set Action
  options_nonempty : options.Nonempty
  capable : Agent → Situation → Action → Prop
  options_capable : ∀ ⦃action⦄, action ∈ options → capable agent situation action

namespace SituatedChoicePoint

variable {Agent : Type uAgent} {Situation : Type uSituation}
  {Action : Type uAction}

theorem has_capable_option
    (choice : SituatedChoicePoint Agent Situation Action) :
    ∃ action, action ∈ choice.options ∧
      choice.capable choice.agent choice.situation action := by
  rcases choice.options_nonempty with ⟨action, available⟩
  exact ⟨action, available, choice.options_capable available⟩

/-- A moral judgment about one available action, retaining the choice point
and the proof that the action was genuinely among its options. -/
structure Judgment
    (choice : SituatedChoicePoint Agent Situation Action) where
  action : Action
  available : action ∈ choice.options
  verdict : MoralValueAttribute

end SituatedChoicePoint

/-- The extensional result returned by theory evaluation: one moral verdict
for each context/action pair.  Concrete paradigms below must construct this
result from their own native structure. -/
abbrev MoralClassifier (Context : Type*) (Action : Type*) :=
  Context → Action → MoralValueAttribute

/-! ## Sentences, support, arguments, and justification -/

/-- An argument retains its premises and conclusion.  No validity claim is
smuggled into the data structure; validity belongs to a separately supplied
consequence relation. -/
structure EthicalArgument (Sentence : Type uSentence) where
  premises : Set Sentence
  conclusion : Sentence

/-- The portion of a consequentialist argument that relates its premises to
one action's consequences. A premise may directly describe a consequence or
refer to the consequence set as a whole. -/
structure ConsequenceGrounding
    (Sentence : Type uSentence) (Consequence : Type uAction) where
  consequenceSet : Set Consequence
  directlyRepresents : Sentence → Consequence → Prop
  refersToSet : Sentence → Set Consequence → Prop

/-- A sentence is grounded by a consequence set when it directly represents
one of its members or explicitly refers to the set. -/
def ConsequenceGrounding.Grounds
    {Sentence : Type uSentence} {Consequence : Type uAction}
    (grounding : ConsequenceGrounding Sentence Consequence)
    (sentence : Sentence) : Prop :=
  (∃ consequence, consequence ∈ grounding.consequenceSet ∧
      grounding.directlyRepresents sentence consequence) ∨
    grounding.refersToSet sentence grounding.consequenceSet

/-- Every premise of the argument is justified by the declared consequence
set. This is the source ontology's defining constraint on a
consequentialist argument. -/
def EthicalArgument.ConsequenceGrounded
    {Sentence : Type uSentence} {Consequence : Type uAction}
    (argument : EthicalArgument Sentence)
    (grounding : ConsequenceGrounding Sentence Consequence) : Prop :=
  ∀ ⦃premise⦄, premise ∈ argument.premises → grounding.Grounds premise

/-- An argument together with the consequence set that grounds all of its
premises. -/
structure ConsequentialistArgument
    (Sentence : Type uSentence) (Consequence : Type uAction) where
  toEthicalArgument : EthicalArgument Sentence
  grounding : ConsequenceGrounding Sentence Consequence
  premise_grounded : toEthicalArgument.ConsequenceGrounded grounding

/-- An ethical theory contains native ethical sentences and may also contain
background sentences whose role is to support a native sentence.

`sentence_supported` is the typed counterpart of the source ontology's
`hasPurposeInArgumentFor` coverage condition. -/
structure EthicalTheory (Sentence : Type uSentence) where
  kind : EthicalTheoryKind
  sentences : Set Sentence
  nativeSentence : Sentence → Prop
  supports : Sentence → Sentence → Prop
  sentence_supported :
    ∀ ⦃sentence⦄, sentence ∈ sentences →
      nativeSentence sentence ∨
        ∃ target, target ∈ sentences ∧
          nativeSentence target ∧ supports sentence target

/-- A source-faithful ethical theory whose sentences carry their ontological
families. Native sentences must belong to the family appropriate for the
theory; non-native sentences remain available as explicit supporting
background. -/
structure ClassifiedEthicalTheory (Sentence : Type uSentence) where
  toEthicalTheory : EthicalTheory Sentence
  sentenceKind : Sentence → EthicalSentenceKind
  native_well_typed :
    ∀ ⦃sentence⦄, toEthicalTheory.nativeSentence sentence →
      (sentenceKind sentence).NativeFor toEthicalTheory.kind

namespace EthicalTheory

variable {Sentence : Type uSentence}

/-- A substantive ethical theory contains at least one native ethical
sentence.  Keeping this as a separate predicate avoids silently forbidding an
empty or purely background `EthicalTheory` when studying boundary cases. -/
def Substantive (theory : EthicalTheory Sentence) : Prop :=
  ∃ sentence, sentence ∈ theory.sentences ∧ theory.nativeSentence sentence

theorem background_supports_native
    (theory : EthicalTheory Sentence) {sentence : Sentence}
    (member : sentence ∈ theory.sentences)
    (notNative : ¬ theory.nativeSentence sentence) :
    ∃ target, target ∈ theory.sentences ∧
      theory.nativeSentence target ∧ theory.supports sentence target := by
  rcases theory.sentence_supported member with native | supported
  · exact False.elim (notNative native)
  · exact supported

theorem not_substantive_of_no_native
    (theory : EthicalTheory Sentence)
    (noneNative : ∀ sentence, sentence ∈ theory.sentences →
      ¬ theory.nativeSentence sentence) :
    ¬ theory.Substantive := by
  rintro ⟨sentence, member, native⟩
  exact noneNative sentence member native

end EthicalTheory

/-- A justified ethical theory retains the arguments that justify each of its
sentences.  Premises used by an internal argument must themselves belong to
the theory. -/
structure JustifiedEthicalTheory (Sentence : Type uSentence) where
  toEthicalTheory : EthicalTheory Sentence
  arguments : Set (EthicalArgument Sentence)
  justified :
    ∀ ⦃sentence⦄, sentence ∈ toEthicalTheory.sentences →
      ∃ argument, argument ∈ arguments ∧
        argument.conclusion = sentence ∧
        argument.premises ⊆ toEthicalTheory.sentences

/-- A consequentialist theory is an ethical theory in the consequentialist
branch for which every sentence is concluded by an internally supported,
consequence-grounded argument. This deliberately does not restrict the
ontological family of the concluded ethical sentence. -/
structure ConsequentialistEthicalTheory
    (Sentence : Type uSentence) (Consequence : Type uAction) where
  toEthicalTheory : EthicalTheory Sentence
  kind_specializes : EthicalTheoryKind.Specializes
    toEthicalTheory.kind .consequentialist
  arguments : Set (ConsequentialistArgument Sentence Consequence)
  justified :
    ∀ ⦃sentence⦄, sentence ∈ toEthicalTheory.sentences →
      ∃ argument, argument ∈ arguments ∧
        argument.toEthicalArgument.conclusion = sentence ∧
        argument.toEthicalArgument.premises ⊆ toEthicalTheory.sentences

namespace ConsequentialistEthicalTheory

variable {Sentence : Type uSentence} {Consequence : Type uAction}

/-- Forgetting the consequence witnesses yields an ordinary justified ethical
theory. -/
def toJustifiedEthicalTheory
    (theory : ConsequentialistEthicalTheory Sentence Consequence) :
    JustifiedEthicalTheory Sentence where
  toEthicalTheory := theory.toEthicalTheory
  arguments := ConsequentialistArgument.toEthicalArgument '' theory.arguments
  justified := by
    intro sentence member
    rcases theory.justified member with
      ⟨argument, argumentMember, conclusion, internalPremises⟩
    exact ⟨argument.toEthicalArgument,
      ⟨argument, argumentMember, rfl⟩, conclusion, internalPremises⟩

end ConsequentialistEthicalTheory

/-- Semantic validity of an ethical argument: every model satisfying all
premises satisfies its conclusion. -/
def EthicalArgument.SemanticallyValid
    {Sentence : Type uSentence} {Model : Type uField}
    (semantics : Semantics Sentence Model)
    (argument : EthicalArgument Sentence) : Prop :=
  ∀ model,
    (∀ premise, premise ∈ argument.premises → semantics.Sat model premise) →
      semantics.Sat model argument.conclusion

/-- The source ontology's justified-true ethical theory, with the claimed
truth and deductive validity made explicit rather than folded into a tag. -/
structure JustifiedTrueEthicalTheory
    (Sentence : Type uSentence) (Model : Type uField)
    (semantics : Semantics Sentence Model) where
  toJustifiedEthicalTheory : JustifiedEthicalTheory Sentence
  actualModel : Model
  true_at_actualModel :
    Models semantics actualModel
      toJustifiedEthicalTheory.toEthicalTheory.sentences
  arguments_valid :
    ∀ ⦃argument⦄,
      argument ∈ toJustifiedEthicalTheory.arguments →
        argument.SemanticallyValid semantics

/-- A theory about ethical theories.  It is deliberately not coercible to
`EthicalTheory`: conflating the two would undo the source ontology's
ethical/metaethical distinction. -/
structure MetaEthicalTheory
    (Sentence : Type uSentence) (EthicalTheoryId : Type uField) where
  sentences : Set Sentence
  concerns : Sentence → EthicalTheoryId → Prop
  hasSubject : ∀ ⦃sentence⦄, sentence ∈ sentences →
    ∃ theory, concerns sentence theory

/-! ## Philosophy/theory correspondence and social commitment -/

/-- A bidirectional correspondence between fields of ethical inquiry and
their syntactic theories. It captures the source ontology's
`theoryFieldPairSubclass` condition without identifying a philosophy with a
set of sentences. -/
structure TheoryFieldCorrespondence
    (Field : Type uField) (TheoryId : Type uAction) where
  paired : Field → TheoryId → Prop
  field_has_theory : ∀ field, ∃ theory, paired field theory
  theory_has_field : ∀ theory, ∃ field, paired field theory

/-- One judging event whose result is a sentence belonging to the held
ethical theory. -/
structure EthicalJudgingEvent
    {Sentence : Type uSentence} (Agent : Type uAgent)
    (theory : EthicalTheory Sentence) where
  judge : Agent
  result : Sentence
  result_mem : result ∈ theory.sentences

/-- A group holds an ethical theory when its members have judging events for
every sentence and the theory influences at least one relevant decision.
Member judgments and decision influence remain separate relations. -/
structure HeldEthicalTheory
    {Sentence : Type uSentence}
    (Member : Type uAgent) (Decision : Type uAction)
    (theory : EthicalTheory Sentence) where
  members : Set Member
  judgments : Set (EthicalJudgingEvent Member theory)
  every_sentence_judged :
    ∀ ⦃sentence⦄, sentence ∈ theory.sentences →
      ∃ event, event ∈ judgments ∧
        event.result = sentence ∧ event.judge ∈ members
  relevantDecision : Decision → Prop
  influencedByTheory : Decision → Prop
  some_relevant_decision_influenced :
    ∃ decision, relevantDecision decision ∧ influencedByTheory decision

theorem HeldEthicalTheory.has_member_of_substantive
    {Sentence : Type uSentence}
    {Member : Type uAgent} {Decision : Type uAction}
    {theory : EthicalTheory Sentence}
    (held : HeldEthicalTheory Member Decision theory)
    (substantive : theory.Substantive) : held.members.Nonempty := by
  rcases substantive with ⟨sentence, member, _native⟩
  rcases held.every_sentence_judged member with
    ⟨event, _recorded, _result, judgeMember⟩
  exact ⟨event.judge, judgeMember⟩

/-! ## Positive and negative canaries -/

inductive ConsequenceCanarySentence : Type
  | survivalFact
  | rescueObligation
  | unrelatedRemark
  deriving DecidableEq, Repr

inductive ConsequenceCanaryEvent : Type
  | survivorContinues
  deriving DecidableEq, Repr

/-- A consequence set and its direct factual description. The rescue
obligation is a conclusion, not itself a consequence description. -/
def rescueGrounding :
    ConsequenceGrounding ConsequenceCanarySentence ConsequenceCanaryEvent where
  consequenceSet := { .survivorContinues }
  directlyRepresents sentence consequence :=
    sentence = .survivalFact ∧ consequence = .survivorContinues
  refersToSet sentence _consequences := sentence = .rescueObligation

def rescueArgument
    (conclusion : ConsequenceCanarySentence) :
    EthicalArgument ConsequenceCanarySentence where
  premises := { .survivalFact }
  conclusion := conclusion

theorem rescueArgument_consequence_grounded
    (conclusion : ConsequenceCanarySentence) :
    (rescueArgument conclusion).ConsequenceGrounded rescueGrounding := by
  intro premise member
  simp only [rescueArgument, Set.mem_singleton_iff] at member
  subst premise
  exact Or.inl ⟨.survivorContinues, by simp [rescueGrounding], rfl, rfl⟩

def unrelatedArgument : EthicalArgument ConsequenceCanarySentence where
  premises := { .unrelatedRemark }
  conclusion := .rescueObligation

/-- Merely calling an argument consequentialist cannot ground a premise that
neither describes nor refers to the declared consequences. -/
theorem unrelatedArgument_not_consequence_grounded :
    ¬ unrelatedArgument.ConsequenceGrounded rescueGrounding := by
  intro grounded
  have unrelatedGrounded := grounded (premise := .unrelatedRemark)
    (by simp [unrelatedArgument])
  rcases unrelatedGrounded with directly | refers
  · rcases directly with ⟨consequence, _member, represents⟩
    have impossible :
        ConsequenceCanarySentence.unrelatedRemark = .survivalFact :=
      represents.1
    exact ConsequenceCanarySentence.noConfusion impossible
  · have impossible :
        ConsequenceCanarySentence.unrelatedRemark = .rescueObligation :=
      refers
    exact ConsequenceCanarySentence.noConfusion impossible

/-- A consequentialist theory may conclude an imperative sentence. What
makes it consequentialist is the argument discipline, not a utilitarian
sentence family. -/
theorem EthicalSentenceKind.imperative_native_for_consequentialist :
    EthicalSentenceKind.imperative.NativeFor
      EthicalTheoryKind.consequentialist :=
  .trans .imperativeDeontological .deontologicalEthical

def consequentialistRescueTheory :
    ConsequentialistEthicalTheory
      ConsequenceCanarySentence ConsequenceCanaryEvent where
  toEthicalTheory :=
    { kind := .consequentialist
      sentences := { .survivalFact, .rescueObligation }
      nativeSentence sentence := sentence = .rescueObligation
      supports source target :=
        source = .survivalFact ∧ target = .rescueObligation
      sentence_supported := by
        intro sentence member
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at member
        rcases member with rfl | rfl
        · exact Or.inr ⟨.rescueObligation, by simp, rfl, by simp⟩
        · exact Or.inl rfl }
  kind_specializes := .refl _
  arguments := Set.univ
  justified := by
    intro sentence member
    let argument :
        ConsequentialistArgument
          ConsequenceCanarySentence ConsequenceCanaryEvent :=
      { toEthicalArgument := rescueArgument sentence
        grounding := rescueGrounding
        premise_grounded := rescueArgument_consequence_grounded sentence }
    refine ⟨argument, Set.mem_univ argument, rfl, ?_⟩
    intro premise premiseMember
    change premise ∈ ({.survivalFact} : Set ConsequenceCanarySentence) at premiseMember
    simp only [Set.mem_singleton_iff] at premiseMember
    subst premise
    simp

theorem consequentialistRescueTheory_is_justified :
    (consequentialistRescueTheory.toJustifiedEthicalTheory).toEthicalTheory =
      consequentialistRescueTheory.toEthicalTheory :=
  rfl

inductive SupportCanarySentence : Type
  | judgment
  | empiricalReason
  | disconnectedRemark
  deriving DecidableEq, Repr

/-- A two-sentence theory whose empirical sentence supports its native moral
judgment. -/
def supportedCanaryTheory : EthicalTheory SupportCanarySentence where
  kind := .valueJudgment
  sentences := { .judgment, .empiricalReason }
  nativeSentence sentence := sentence = .judgment
  supports source target :=
    source = .empiricalReason ∧ target = .judgment
  sentence_supported := by
    intro sentence member
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at member
    rcases member with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨.judgment, by simp, rfl, by simp⟩

theorem supportedCanaryTheory_substantive :
    supportedCanaryTheory.Substantive := by
  exact ⟨.judgment, by simp [supportedCanaryTheory], rfl⟩

theorem supportedCanaryTheory_reason_supports_judgment :
    supportedCanaryTheory.supports .empiricalReason .judgment := by
  simp [supportedCanaryTheory]

/-- A disconnected background remark cannot be added to the canary theory
while keeping the same native-sentence and support relations. -/
theorem disconnectedRemark_breaks_support_coverage :
    ¬ (supportedCanaryTheory.nativeSentence .disconnectedRemark ∨
      ∃ target, target ∈ supportedCanaryTheory.sentences ∧
        supportedCanaryTheory.nativeSentence target ∧
        supportedCanaryTheory.supports .disconnectedRemark target) := by
  simp [supportedCanaryTheory]

inductive CorrespondenceCanaryField : Type
  | ethics
  | metaEthics
  deriving DecidableEq, Repr

inductive CorrespondenceCanaryTheory : Type
  | ethicalTheory
  | metaethicalTheory
  deriving DecidableEq, Repr

/-- A two-branch theory/field correspondence that keeps ethics and
metaethics paired but distinct. -/
def correspondenceCanary :
    TheoryFieldCorrespondence
      CorrespondenceCanaryField CorrespondenceCanaryTheory where
  paired field theory :=
    match field, theory with
    | .ethics, .ethicalTheory => True
    | .metaEthics, .metaethicalTheory => True
    | _, _ => False
  field_has_theory := by
    intro field
    cases field
    · exact ⟨.ethicalTheory, trivial⟩
    · exact ⟨.metaethicalTheory, trivial⟩
  theory_has_field := by
    intro theory
    cases theory
    · exact ⟨.ethics, trivial⟩
    · exact ⟨.metaEthics, trivial⟩

theorem correspondenceCanary_ethics_paired :
    correspondenceCanary.paired .ethics .ethicalTheory :=
  trivial

theorem correspondenceCanary_rejects_cross_pair :
    ¬ correspondenceCanary.paired .ethics .metaethicalTheory := by
  simp [correspondenceCanary]

/-- The supported theory can be held by a one-member group, with each theory
sentence backed by an explicit judging event and one influenced decision. -/
def heldSupportedCanaryTheory :
    HeldEthicalTheory Unit Bool supportedCanaryTheory where
  members := Set.univ
  judgments := Set.univ
  every_sentence_judged := by
    intro sentence member
    let event : EthicalJudgingEvent Unit supportedCanaryTheory :=
      { judge := ()
        result := sentence
        result_mem := member }
    exact ⟨event, Set.mem_univ event, rfl, Set.mem_univ ()⟩
  relevantDecision decision := decision = true
  influencedByTheory decision := decision = true
  some_relevant_decision_influenced := ⟨true, rfl, rfl⟩

theorem heldSupportedCanaryTheory_has_member :
    heldSupportedCanaryTheory.members.Nonempty :=
  heldSupportedCanaryTheory.has_member_of_substantive
    supportedCanaryTheory_substantive

/-! ## Axiom audit -/

#print axioms EthicalTheoryKind.Specializes.targetCenteredVirtue_ethical
#print axioms EthicalTheoryKind.targetCentered_not_specializes_virtue
#print axioms EthicalTheoryKind.virtue_not_specializes_targetCentered
#print axioms EthicalSentenceKind.targetCenteredVirtue_native_for_generalVirtue
#print axioms EthicalSentenceKind.targetCenteredVirtue_not_native_for_virtue
#print axioms EthicalSentenceKind.utilityComparison_native_for_utilitarian
#print axioms SituatedChoicePoint.has_capable_option
#print axioms EthicalTheory.background_supports_native
#print axioms HeldEthicalTheory.has_member_of_substantive
#print axioms rescueArgument_consequence_grounded
#print axioms unrelatedArgument_not_consequence_grounded
#print axioms EthicalSentenceKind.imperative_native_for_consequentialist
#print axioms consequentialistRescueTheory_is_justified
#print axioms supportedCanaryTheory_substantive
#print axioms disconnectedRemark_breaks_support_coverage
#print axioms correspondenceCanary_ethics_paired
#print axioms correspondenceCanary_rejects_cross_pair
#print axioms heldSupportedCanaryTheory_has_member

end Mettapedia.Ethics.MetaEthicsOntology
