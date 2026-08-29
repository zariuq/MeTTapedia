import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.MILCheckedChain
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.IntrinsicMILSemanticAdequacy
import Mettapedia.GSLT.LanguageDef.NIKInferenceExtensionAdmission

/-!
# Proof-relevant admission of a learned MIL chain

The generic inference checker validates the finite proof program, while an
independent `Type`-valued interpretation constructs its relational evidence.
The chain interpretation retains the middle occurrence and both premise
derivations.  A validated calculus-language extension and its interpretation
are then composed by the ordinary revision-indexed NIK admission doctrine.

The final bridge maps this evidence into Prime's intrinsic indexed hypothesis
language.  Thus the learned rule is neither a privileged MIL evaluator nor a
new source of theoremhood: it is checked presentation data whose meaning is an
ordinary proof-relevant Prime relation.
-/

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace MILLearnedProofRelevantAdmission

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension
open Mettapedia.GSLT.LanguageDef.InferenceProofRelevantSemanticExtension
open Mettapedia.GSLT.LanguageDef.NIKInferenceExtensionAdmission
open Mettapedia.GSLT.LanguageDef.NIKIndexedExecutionAdmission
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.NIKRevisionAlignedComposition
open Presentation


/-! ## Independent proof-relevant meaning -/

/-- Exact relational evidence for the three-rule learned calculus language. -/
inductive Reach : Pattern → Pattern → Type where
  | mother : Reach MILCheckedChain.alice MILCheckedChain.bob
  | father : Reach MILCheckedChain.bob MILCheckedChain.carol
  | chain {source middle target : Pattern} :
      Reach source middle → Reach middle target → Reach source target

def Meaning : Pattern → Type
  | .apply "MIL.Rel" [source, target] => Reach source target
  | _ => Empty

/-- The base calculus language has no rules, so its proof-relevant semantics is
vacuous.  Impossibility is obtained from executable rule lookup rather than by
extracting data hidden inside the proposition-valued application witness. -/
def baseSemantics : CalculusLanguageSemantics MILCheckedChain.base Meaning where
  ruleMeaning := by
    intro ruleInstance premises conclusion application _premiseEvidence
    have noRules : MILCheckedChain.base.1.rules = [] := rfl
    have impossible : False := by
      rcases application with ⟨rule, lookup, _⟩
      unfold CalculusLanguageDef.lookupRule? at lookup
      rw [noRules] at lookup
      simp at lookup
    exact False.elim impossible

/-- The learned facts and chain receive independent `Type`-valued meanings.
The executable instantiation equality fixes the exact premise and conclusion
indices before ordered premise evidence is inspected. -/
def learnedSemantics :
    SemanticExtension MILCheckedChain.base MILCheckedChain.learned Meaning where
  baseSemantics := baseSemantics
  addedRuleMeaning := by
    intro rule member ruleInstance premises conclusion lookup application
      premiseEvidence
    simp only [MILCheckedChain.learned, MILCheckedChain.learnedDelta, List.mem_cons,
      List.not_mem_nil, or_false] at member
    have instantiated :=
      instantiateRule?_eq_some_iff_application.mpr application
    by_cases mother : rule = MILCheckedChain.motherRule
    · subst rule
      rcases ruleInstance with ⟨ruleId, arguments⟩
      cases arguments with
      | cons argument arguments =>
          simp [instantiateRule?, lookup, MILCheckedChain.motherRule,
            argumentsValidAt] at instantiated
      | nil =>
          simp [instantiateRule?, lookup, MILCheckedChain.motherRule,
            instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
            instantiateSchemasAt?, MILCheckedChain.relates, MILCheckedChain.alice,
            MILCheckedChain.bob] at instantiated
          rcases instantiated with ⟨_, rfl, rfl⟩
          exact Reach.mother
    · by_cases father : rule = MILCheckedChain.fatherRule
      · subst rule
        rcases ruleInstance with ⟨ruleId, arguments⟩
        cases arguments with
        | cons argument arguments =>
            simp [instantiateRule?, lookup, MILCheckedChain.fatherRule,
              argumentsValidAt] at instantiated
        | nil =>
            simp [instantiateRule?, lookup, MILCheckedChain.fatherRule,
              instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
              instantiateSchemasAt?, MILCheckedChain.relates, MILCheckedChain.bob,
              MILCheckedChain.carol] at instantiated
            rcases instantiated with ⟨_, rfl, rfl⟩
            exact Reach.father
      · have chain : rule = MILCheckedChain.chainRule := by
          rcases member with motherMember | fatherMember | chainMember
          · exact False.elim (mother motherMember)
          · exact False.elim (father fatherMember)
          · exact chainMember
        subst rule
        rcases ruleInstance with ⟨ruleId, arguments⟩
        cases arguments with
        | nil =>
            simp [instantiateRule?, lookup, MILCheckedChain.chainRule,
              argumentsValidAt] at instantiated
        | cons source remaining =>
          cases remaining with
          | nil =>
              simp [instantiateRule?, lookup, MILCheckedChain.chainRule,
                argumentsValidAt] at instantiated
          | cons middle remaining =>
            cases remaining with
            | nil =>
                simp [instantiateRule?, lookup, MILCheckedChain.chainRule,
                  argumentsValidAt] at instantiated
            | cons target remaining =>
              cases remaining with
              | cons extra tail =>
                  simp [instantiateRule?, lookup, MILCheckedChain.chainRule,
                    argumentsValidAt] at instantiated
              | nil =>
                  simp [instantiateRule?, lookup, MILCheckedChain.chainRule,
                    instantiateSchema?, instantiateSchemaAt?,
                    instantiateSchemas?, instantiateSchemasAt?,
                    lookupArgumentAt?, MILCheckedChain.relates] at instantiated
                  rcases instantiated with ⟨_, rfl, rfl⟩
                  cases premiseEvidence with
                  | cons earlier rest =>
                    cases rest with
                    | cons later rest =>
                      cases rest
                      exact Reach.chain earlier later

noncomputable def grandparentDerivation :
    Derivation MILCheckedChain.learned.target
      (MILCheckedChain.relates MILCheckedChain.alice MILCheckedChain.carol) :=
  Classical.choose
    (G2_checkRaw_iff_exists_derivation_erases_to.mp
      MILCheckedChain.grandparentProof_checked)

@[simp] theorem grandparentDerivation_erase :
    grandparentDerivation.erase = MILCheckedChain.grandparentProof :=
  Classical.choose_spec
    (G2_checkRaw_iff_exists_derivation_erases_to.mp
      MILCheckedChain.grandparentProof_checked)

/-- The accepted proof program constructs a proof-relevant chain, not merely
endpoint reachability. -/
noncomputable def grandparentEvidence :
    Reach MILCheckedChain.alice MILCheckedChain.carol :=
  learnedSemantics.interpret grandparentDerivation

theorem grandparent_retains_middle_and_both_derivations :
    Nonempty
      (Sigma fun middle : Pattern =>
        Reach MILCheckedChain.alice middle × Reach middle MILCheckedChain.carol) :=
  ⟨⟨MILCheckedChain.bob, Reach.mother, Reach.father⟩⟩

/-! ## Interpretation as an intrinsic Prime hypothesis -/

inductive Primitive : Unit → Unit → Type where
  | mother : Primitive () ()
  | father : Primitive () ()

inductive MotherEvidence : Pattern → Pattern → Type where
  | fact : MotherEvidence MILCheckedChain.alice MILCheckedChain.bob

inductive FatherEvidence : Pattern → Pattern → Type where
  | fact : FatherEvidence MILCheckedChain.bob MILCheckedChain.carol

def vocabulary : MILSchemaElaboration.Semantic.Vocabulary where
  SortCode := Unit
  Carrier := fun _ => Pattern
  Primitive := Primitive
  meaning := by
    intro source target symbol
    cases symbol with
    | mother => exact ⟨MotherEvidence⟩
    | father => exact ⟨FatherEvidence⟩

abbrev onlySort : vocabulary.SortCode := ()

/-- A learned checker witness is reified as an ordinary intrinsic hypothesis
together with evidence in that hypothesis's proof-relevant denotation. -/
structure IntrinsicWitness (source target : Pattern) where
  hypothesis : MILSchemaElaboration.Semantic.Hypothesis vocabulary onlySort onlySort
  evidence : hypothesis.denote.evidence source target

def Reach.toIntrinsic {source target : Pattern} :
    Reach source target → IntrinsicWitness source target
  | .mother => ⟨.primitive Primitive.mother, MotherEvidence.fact⟩
  | .father => ⟨.primitive Primitive.father, FatherEvidence.fact⟩
  | .chain earlier later =>
      let earlierWitness := earlier.toIntrinsic
      let laterWitness := later.toIntrinsic
      ⟨.chain earlierWitness.hypothesis laterWitness.hypothesis,
        ⟨_, earlierWitness.evidence, laterWitness.evidence⟩⟩

noncomputable def intrinsicGrandparent :
    IntrinsicWitness MILCheckedChain.alice MILCheckedChain.carol :=
  grandparentEvidence.toIntrinsic

/-- The intrinsic image retains a concrete inhabitant of the denotation fibre
constructed from the checked learned proof. -/
theorem intrinsicGrandparent_carries_evidence :
    Nonempty
      (intrinsicGrandparent.hypothesis.denote.evidence
        MILCheckedChain.alice MILCheckedChain.carol) :=
  ⟨intrinsicGrandparent.evidence⟩

/-- Every typed quotation of this vocabulary turns the checked learned proof
into an ordinary program of Prime's native indexed hypothesis family. -/
noncomputable def intrinsicGrandparentProgram
    {context : Tower.Ctx n}
    (quotation : IntrinsicMILHypothesis.TypedVocabularyQuotation vocabulary
      context) :=
  IntrinsicMILSemanticAdequacy.Program.ofHypothesis quotation
    intrinsicGrandparent.hypothesis

theorem intrinsicGrandparentProgram_hasType
    {context : Tower.Ctx n}
    (quotation : IntrinsicMILHypothesis.TypedVocabularyQuotation vocabulary
      context) :
    IntrinsicMILHypothesis.HasType context
      (IntrinsicMILHypothesis.quoteHypothesis quotation
        intrinsicGrandparent.hypothesis)
      (IntrinsicMILHypothesis.hypothesisApp quotation.sorts
        quotation.primitives (quotation.sortCode onlySort)
        (quotation.sortCode onlySort)) :=
  (intrinsicGrandparentProgram quotation).hasType

theorem intrinsicGrandparent_has_chain_shape :
    ∃ middle : Pattern,
      Nonempty (MotherEvidence MILCheckedChain.alice middle) ∧
        Nonempty (FatherEvidence middle MILCheckedChain.carol) := by
  exact ⟨MILCheckedChain.bob, ⟨MotherEvidence.fact⟩, ⟨FatherEvidence.fact⟩⟩

/-! ## Revision-indexed NIK composition -/

def dependencies : DependencySystem where
  Revision := Bool
  Dependency := Unit
  Value := Bool
  read revision _ := revision

noncomputable def checkedGrandparent : CheckedState MILCheckedChain.learned.target :=
  ⟨MILCheckedChain.relates MILCheckedChain.alice MILCheckedChain.carol, grandparentDerivation⟩

noncomputable def activeInterpretation :=
  (admitInterpretationAt learnedSemantics dependencies false).activate
    (dependencies.sameDependencies_refl false)

/-- Once currentness is established, the active NIK map retains the exact
checked artifact and constructs the proof-relevant learned meaning directly. -/
theorem active_interpretation_retains_proof_and_evidence :
    let result := activeInterpretation.run ⟨checkedGrandparent⟩
    result.checked.derivation.erase = MILCheckedChain.grandparentProof ∧
      Nonempty (Meaning result.checked.goal) := by
  dsimp [activeInterpretation, admitInterpretationAt,
    IndexedObservedAdmittedAt.Active.run, interpretRefinement,
    checkedGrandparent]
  constructor
  · exact grandparentDerivation_erase
  · exact ⟨learnedSemantics.interpret grandparentDerivation⟩

/-- A relevant revision change prevents activation of the stored semantic
interpretation.  The checked derivation remains independently inhabited. -/
theorem relevant_change_prevents_activation :
    ¬ (admitInterpretationAt learnedSemantics dependencies false).Active true := by
  rintro ⟨current⟩
  have changed := current ()
  simp [dependencies] at changed

/-- Negative control inherited from the exact checker boundary: an ill-shared
middle occurrence is rejected before it can acquire semantic evidence. -/
theorem wrong_middle_has_no_checked_derivation :
    ¬ ∃ derivation : Derivation MILCheckedChain.learned.target
        (MILCheckedChain.relates MILCheckedChain.alice MILCheckedChain.bob),
      derivation.erase = MILCheckedChain.wrongMiddleProof := by
  rintro ⟨derivation, erases⟩
  have accepted := checkRaw_erase derivation
  rw [erases, MILCheckedChain.wrongMiddleProof_rejected] at accepted
  contradiction

#print axioms grandparent_retains_middle_and_both_derivations
#print axioms intrinsicGrandparent_carries_evidence
#print axioms intrinsicGrandparentProgram_hasType
#print axioms intrinsicGrandparent_has_chain_shape
#print axioms active_interpretation_retains_proof_and_evidence
#print axioms relevant_change_prevents_activation
#print axioms wrong_middle_has_no_checked_derivation

end MILLearnedProofRelevantAdmission
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
