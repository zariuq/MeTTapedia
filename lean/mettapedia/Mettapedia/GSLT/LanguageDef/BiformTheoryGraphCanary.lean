import Mettapedia.GSLT.LanguageDef.BiformTheoryGraph
import Mettapedia.GSLT.LanguageDef.InstitutionConsequence
import Mettapedia.TypeTheory.SimpleDependentInstitutionBridge

/-!
# A simple-to-dependent heterogeneous biform canary

This specimen selects a closed predicate theory in a contextual simple
institution, transports it to the dependent-family institution, and carries a
two-occurrence operational loop across the same route.  The positive theorem
constructs the resulting heterogeneous biform arrow.  The negative theorem
changes the target event meaning while leaving both component translations
unchanged and proves that the incompatible pair is rejected.

Thus neither a logic embedding nor a GSLT pass alone is enough: a biform route
exists exactly when their native meaning readings agree.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BiformTheoryGraphCanary

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.ProofRelevant
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.InstitutionConsequence
open Mettapedia.GSLT.LanguageDef.TheoryGraph
open Mettapedia.GSLT.LanguageDef.BiformTheoryGraph
open Mettapedia.TypeTheory.SimpleDependentInstitutionBridge
open Mettapedia.TypeTheory.SetFamilyChangeOfBaseAdjunction

/-! ## Native logical endpoints -/

abbrev simpleConsequence :=
  consequenceProjection (simpleInstitution Bool)

abbrev dependentConsequence :=
  consequenceProjection (dependentInstitution Bool)

def falseSentence : Sigma fun _ : Bool => Bool := ⟨false, false⟩

def trueSentence : Sigma fun _ : Bool => Bool := ⟨true, false⟩

def sourceLogical : PiInstitution.TheoryObject simpleConsequence :=
  PiInstitution.generatedTheory simpleConsequence Bool
    ({falseSentence, trueSentence} : Set (Sigma fun _ : Bool => Bool))

def sourceTheory : TheoryGraph.Object :=
  TheoryGraph.Object.mk' simpleConsequence sourceLogical

def simpleDependentConsequenceRoute :
    PiInstitution.Comorphism simpleConsequence dependentConsequence :=
  comorphismProjection (simpleToDependent Bool)

def targetTheory : TheoryGraph.Object :=
  TheoryGraph.Object.mk' dependentConsequence
    (TheoryGraph.directImage simpleDependentConsequenceRoute sourceTheory.logical)

def logicalRoute : sourceTheory ⟶ targetTheory :=
  TheoryGraph.translate
    (source := sourceTheory)
    (targetInstitution := dependentConsequence)
    simpleDependentConsequenceRoute

def targetFalseSentence :
    targetTheory.institution.sentence.obj targetTheory.logical.signature :=
  translateSentence (TheoryGraph.Hom.institution logicalRoute)
    (TheoryGraph.Hom.mapSignature logicalRoute)
    falseSentence

def targetTrueSentence :
    targetTheory.institution.sentence.obj targetTheory.logical.signature :=
  translateSentence (TheoryGraph.Hom.institution logicalRoute)
    (TheoryGraph.Hom.mapSignature logicalRoute)
    trueSentence

theorem falseSentence_mem : falseSentence ∈ sourceLogical.theory.1 :=
  PiInstitution.derives_of_mem simpleConsequence Bool
    (Set.mem_insert falseSentence {trueSentence})

theorem trueSentence_mem : trueSentence ∈ sourceLogical.theory.1 :=
  PiInstitution.derives_of_mem simpleConsequence Bool
    (Set.mem_insert_of_mem falseSentence (Set.mem_singleton trueSentence))

/-! ## A nontrivial proof-relevant operational model -/

def loopTheory : GSLT where
  Term := Unit
  equations := ⟨Eq, eq_equivalence⟩
  rewrites := fun _ _ => True
  rewrites_resp_left := by
    intro source source' target equivalent step
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equivalent
    exact step

def loopEvidence : StepEvidence loopTheory where
  Evidence := fun _ _ => Bool
  erases_iff := by
    intro source target
    constructor
    · intro evidence
      trivial
    · intro step
      exact ⟨false⟩

def loopAlgorithm : ProofRelevantGSLT := ⟨loopTheory, loopEvidence⟩

def falseEvent : loopAlgorithm.Event := ⟨(), (), false⟩

def trueEvent : loopAlgorithm.Event := ⟨(), (), true⟩

theorem retained_events_distinct : falseEvent ≠ trueEvent := by
  intro equal
  have evidenceEqual := congrArg ProofRelevantGSLT.Event.evidence equal
  exact Bool.false_ne_true evidenceEqual

/-! ## Positive and negative biform routes -/

def sourceBiform : BiformTheoryGraph.Object where
  logical := sourceTheory
  algorithm := loopAlgorithm
  meaning := fun _ => falseSentence
  meaning_sound := by
    intro event
    exact falseSentence_mem

def targetBiform : BiformTheoryGraph.Object where
  logical := targetTheory
  algorithm := loopAlgorithm
  meaning := fun _ => targetFalseSentence
  meaning_sound := by
    intro event
    exact TheoryGraph.Hom.preserves logicalRoute falseSentence_mem

/-- Positive control: the cross-institution logical route and identity
operational route agree on the meaning of both retained loop occurrences. -/
def biformRoute : Hom sourceBiform targetBiform where
  logical := logicalRoute
  operational := Translation.id loopAlgorithm
  meaning_natural := by
    intro event
    rfl

def changedTargetBiform : BiformTheoryGraph.Object where
  logical := targetTheory
  algorithm := loopAlgorithm
  meaning := fun _ => targetTrueSentence
  meaning_sound := by
    intro event
    exact TheoryGraph.Hom.preserves logicalRoute trueSentence_mem

def incompatiblePair :
    (sourceBiform.logical ⟶ changedTargetBiform.logical) ×
      Translation sourceBiform.algorithm changedTargetBiform.algorithm :=
  (logicalRoute, Translation.id loopAlgorithm)

theorem target_sentences_distinct : targetFalseSentence ≠ targetTrueSentence := by
  intro equal
  have firstEqual := congrArg Sigma.fst equal
  change false = true at firstEqual
  exact Bool.false_ne_true firstEqual

/-- Negative control: reusing both component arrows does not create a biform
route when the target assigns a different native theorem to the event. -/
theorem changed_meaning_is_incompatible :
    ¬ Compatible incompatiblePair := by
  intro compatible
  have meaningEqual := compatible falseEvent
  change targetFalseSentence = targetTrueSentence at meaningEqual
  exact target_sentences_distinct meaningEqual

theorem no_biform_route_with_incompatible_pair :
    ¬ ∃ route : Hom sourceBiform changedTargetBiform,
      routePair route = incompatiblePair := by
  rw [routePair_range_iff_compatible]
  exact changed_meaning_is_incompatible

#print axioms logicalRoute
#print axioms retained_events_distinct
#print axioms biformRoute
#print axioms target_sentences_distinct
#print axioms changed_meaning_is_incompatible
#print axioms no_biform_route_with_incompatible_pair

end Mettapedia.GSLT.LanguageDef.BiformTheoryGraphCanary
