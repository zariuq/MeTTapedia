import Mettapedia.Ethics.MetaEthicsOntology
import Mettapedia.Languages.KIF.DeclarationDecode

/-!
# Formal Ethics source hierarchy concordance

This module gives the ethical-theory and ethical-sentence families in the
source ontology exact SUO-KIF names.  It also records the direct subclass
edges among those families and proves that every such source edge is sound for
the typed specialization relations.

The companion source checker compares these finite edge tables with the
parsed ontology file.  Thus the executable check detects source drift, while
the theorems below establish the meaning of every admitted edge in Lean.
Upper-ontology mixins such as `JustifiedTheory` are intentionally outside the
family edge tables; they are represented by separate typed structures in the
core ontology.
-/

set_option autoImplicit false

namespace Mettapedia.Ethics.SourceHierarchyConcordance

open Mettapedia.Ethics.MetaEthicsOntology
open Mettapedia.Languages.KIF

abbrev TheoryEdge := EthicalTheoryKind × EthicalTheoryKind
abbrev SentenceEdge := EthicalSentenceKind × EthicalSentenceKind

def theorySourceName : EthicalTheoryKind → String
  | .ethical => "EthicalTheory"
  | .valueJudgment => "ValueJudgmentTheory"
  | .simpleActionValueJudgment => "SimpleActionValueJudgmentTheory"
  | .deontological => "DeontologicalTheory"
  | .deontologicalImperative => "DeontologicalImperativeTheory"
  | .utilitarian => "UtilitarianTheory"
  | .consequentialist => "ConsequentialistTheory"
  | .consequentialistUtilitarian => "ConsequentialistUtilitarianTheory"
  | .hedonisticUtilitarian => "HedonisticUtilitarianTheory"
  | .generalVirtue => "GeneralVirtueEthicsTheory"
  | .virtue => "VirtueEthicsTheory"
  | .targetCenteredVirtue => "TargetCenteredVirtueEthicsTheory"
  | .completeTargetCenteredVirtue => "CompleteTargetCenteredVirtueEthicsTheory"
  | .ruleConsequentialist => "RuleConsequentialistTheory"
  | .twoLevelUtilitarian => "TwoLevelUtilitarianTheory"
  | .kantianDeontological => "KantianDeontologicalTheory"

def sentenceSourceName : EthicalSentenceKind → String
  | .ethical => "EthicalSentence"
  | .valueJudgment => "ValueJudgmentSentence"
  | .simpleValueJudgment => "SimpleValueJudgmentSentence"
  | .simpleActionValueJudgment => "SimpleActionValueJudgmentSentence"
  | .simpleSituationalActionValueJudgment =>
      "SimpleSituationalActionValueJudgmentSentence"
  | .deontological => "DeontologicalSentence"
  | .imperative => "ImperativeSentence"
  | .simpleImperative => "SimpleImperativeSentence"
  | .utilitarian => "UtilitarianSentence"
  | .simpleUtilitarian => "SimpleUtilitarianSentence"
  | .utilityAssignment => "UtilityAssignmentSentence"
  | .utilityComparison => "UtilityComparisonSentence"
  | .generalVirtue => "GeneralVirtueEthicsSentence"
  | .simpleGeneralVirtue => "SimpleGeneralVirtueSentence"
  | .virtue => "VirtueEthicsSentence"
  | .simpleVirtue => "SimpleVirtueSentence"
  | .simpleVirtueDesire => "SimpleVirtueDesireSentence"
  | .minimalVirtueDesire => "MinimalVirtueDesireSentence"
  | .targetCenteredVirtue => "TargetCenteredVirtueEthicsSentence"
  | .simpleTargetCenteredVirtue => "SimpleTargetCenteredVirtueEthicsSentence"
  | .virtueAspect => "VirtueAspectSentence"
  | .simpleVirtueTarget => "SimpleVirtueTargetSentence"
  | .fieldTargetVirtueAspect => "FTVirtueAspectSentence"
  | .completeVirtueAspect => "CompleteVirtueAspectSentence"

def theoryKinds : List EthicalTheoryKind :=
  [ .ethical, .valueJudgment, .simpleActionValueJudgment, .deontological,
    .deontologicalImperative, .utilitarian, .consequentialist,
    .consequentialistUtilitarian, .hedonisticUtilitarian, .generalVirtue,
    .virtue, .targetCenteredVirtue, .completeTargetCenteredVirtue,
    .ruleConsequentialist, .twoLevelUtilitarian, .kantianDeontological ]

def sentenceKinds : List EthicalSentenceKind :=
  [ .ethical, .valueJudgment, .simpleValueJudgment,
    .simpleActionValueJudgment, .simpleSituationalActionValueJudgment,
    .deontological, .imperative, .simpleImperative, .utilitarian,
    .simpleUtilitarian, .utilityAssignment, .utilityComparison,
    .generalVirtue, .simpleGeneralVirtue, .virtue, .simpleVirtue,
    .simpleVirtueDesire, .minimalVirtueDesire, .targetCenteredVirtue,
    .simpleTargetCenteredVirtue, .virtueAspect, .simpleVirtueTarget,
    .fieldTargetVirtueAspect, .completeVirtueAspect ]

/-- Direct source edges among the represented ethical-theory families.  The
source states the redundant deontological edge for rule consequentialism as
well as its more specific imperative edge, so both are retained. -/
def expectedTheoryEdges : List TheoryEdge :=
  [ (.valueJudgment, .ethical),
    (.simpleActionValueJudgment, .valueJudgment),
    (.deontological, .ethical),
    (.deontologicalImperative, .deontological),
    (.utilitarian, .ethical),
    (.consequentialist, .ethical),
    (.consequentialistUtilitarian, .consequentialist),
    (.consequentialistUtilitarian, .utilitarian),
    (.hedonisticUtilitarian, .utilitarian),
    (.generalVirtue, .ethical),
    (.virtue, .generalVirtue),
    (.targetCenteredVirtue, .generalVirtue),
    (.completeTargetCenteredVirtue, .targetCenteredVirtue),
    (.ruleConsequentialist, .deontological),
    (.ruleConsequentialist, .consequentialist),
    (.ruleConsequentialist, .deontologicalImperative),
    (.twoLevelUtilitarian, .ethical),
    (.kantianDeontological, .deontologicalImperative) ]

def expectedSentenceEdges : List SentenceEdge :=
  [ (.valueJudgment, .ethical),
    (.simpleValueJudgment, .valueJudgment),
    (.simpleActionValueJudgment, .simpleValueJudgment),
    (.simpleSituationalActionValueJudgment, .valueJudgment),
    (.deontological, .ethical),
    (.imperative, .deontological),
    (.simpleImperative, .imperative),
    (.utilitarian, .ethical),
    (.simpleUtilitarian, .utilitarian),
    (.utilityAssignment, .simpleUtilitarian),
    (.utilityComparison, .simpleUtilitarian),
    (.generalVirtue, .ethical),
    (.simpleGeneralVirtue, .generalVirtue),
    (.virtue, .generalVirtue),
    (.simpleVirtue, .virtue),
    (.simpleVirtueDesire, .virtue),
    (.minimalVirtueDesire, .simpleVirtueDesire),
    (.targetCenteredVirtue, .generalVirtue),
    (.simpleTargetCenteredVirtue, .targetCenteredVirtue),
    (.simpleTargetCenteredVirtue, .simpleGeneralVirtue),
    (.virtueAspect, .targetCenteredVirtue),
    (.simpleVirtueTarget, .virtueAspect),
    (.fieldTargetVirtueAspect, .targetCenteredVirtue),
    (.completeVirtueAspect, .targetCenteredVirtue) ]

theorem expectedTheoryEdge_sound {edge : TheoryEdge}
    (member : edge ∈ expectedTheoryEdges) :
    EthicalTheoryKind.Specializes edge.1 edge.2 := by
  simp only [expectedTheoryEdges, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .valueJudgmentEthical
  · exact .simpleActionValueJudgmentValue
  · exact .deontologicalEthical
  · exact .imperativeDeontological
  · exact .utilitarianEthical
  · exact .consequentialistEthical
  · exact .consequentialistUtilitarianConsequentialist
  · exact .consequentialistUtilitarianUtilitarian
  · exact .hedonisticUtilitarianUtilitarian
  · exact .generalVirtueEthical
  · exact .virtueGeneralVirtue
  · exact .targetCenteredVirtueGeneralVirtue
  · exact .completeTargetCenteredVirtueTargetCentered
  · exact .trans .ruleConsequentialistImperative .imperativeDeontological
  · exact .ruleConsequentialistConsequentialist
  · exact .ruleConsequentialistImperative
  · exact .twoLevelUtilitarianEthical
  · exact .kantianDeontologicalImperative

theorem expectedSentenceEdge_sound {edge : SentenceEdge}
    (member : edge ∈ expectedSentenceEdges) :
    EthicalSentenceKind.Specializes edge.1 edge.2 := by
  simp only [expectedSentenceEdges, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact .valueJudgmentEthical
  · exact .simpleValueJudgmentValue
  · exact .actionValueJudgmentSimple
  · exact .situationalActionValueJudgmentValue
  · exact .deontologicalEthical
  · exact .imperativeDeontological
  · exact .simpleImperativeImperative
  · exact .utilitarianEthical
  · exact .simpleUtilitarianUtilitarian
  · exact .utilityAssignmentSimple
  · exact .utilityComparisonSimple
  · exact .generalVirtueEthical
  · exact .simpleGeneralVirtueGeneral
  · exact .virtueGeneral
  · exact .simpleVirtueVirtue
  · exact .simpleVirtueDesireVirtue
  · exact .minimalVirtueDesireSimple
  · exact .targetCenteredVirtueGeneral
  · exact .simpleTargetCenteredVirtueTarget
  · exact .simpleTargetCenteredVirtueSimpleGeneral
  · exact .virtueAspectTarget
  · exact .simpleVirtueTargetAspect
  · exact .fieldTargetVirtueAspectTarget
  · exact .completeVirtueAspectTarget

def expectedNamedTheoryEdges : List (String × String) :=
  expectedTheoryEdges.map fun edge =>
    (theorySourceName edge.1, theorySourceName edge.2)

def expectedNamedSentenceEdges : List (String × String) :=
  expectedSentenceEdges.map fun edge =>
    (sentenceSourceName edge.1, sentenceSourceName edge.2)

def representedTheoryNames : List String := theoryKinds.map theorySourceName
def representedSentenceNames : List String := sentenceKinds.map sentenceSourceName

/-- Extract only symbol-to-symbol subclass assertions.  Class-valued function
terms remain in the decoded ontology but are not mistaken for named hierarchy
edges. -/
def namedSubclassEdges (declarations : List SuoDeclaration) :
    List (String × String) :=
  declarations.filterMap fun
    | .subclass child parent =>
        parent.asSymbol?.map fun parentName => (child.text, parentName.text)
    | _ => none

def relevantTheoryEdges (declarations : List SuoDeclaration) :
    List (String × String) :=
  (namedSubclassEdges declarations).filter fun edge =>
    representedTheoryNames.contains edge.1 &&
      representedTheoryNames.contains edge.2

def relevantSentenceEdges (declarations : List SuoDeclaration) :
    List (String × String) :=
  (namedSubclassEdges declarations).filter fun edge =>
    representedSentenceNames.contains edge.1 &&
      representedSentenceNames.contains edge.2

def edgeDifference
    (left right : List (String × String)) : List (String × String) :=
  left.eraseDups.filter fun edge => !right.contains edge

theorem targetCenteredTheory_not_directly_agentVirtue :
    (.targetCenteredVirtue, .virtue) ∉ expectedTheoryEdges := by
  decide

theorem agentVirtueTheory_not_directly_targetCentered :
    (.virtue, .targetCenteredVirtue) ∉ expectedTheoryEdges := by
  decide

#print axioms expectedTheoryEdge_sound
#print axioms expectedSentenceEdge_sound
#print axioms targetCenteredTheory_not_directly_agentVirtue
#print axioms agentVirtueTheory_not_directly_targetCentered

end Mettapedia.Ethics.SourceHierarchyConcordance
