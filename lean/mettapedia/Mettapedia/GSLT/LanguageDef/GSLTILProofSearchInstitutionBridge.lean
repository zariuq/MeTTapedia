import Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
import Mettapedia.GSLT.LanguageDef.CertificateGSLTAmbient
import Mettapedia.GSLT.LanguageDef.GSLTILSemanticPredicateInstitution

/-!
# Proof-search sentences in the GSLT-IL semantic institution

An admitted proof calculus already has an operational GSLT: states are
ordered outstanding goals and one step applies one authored rule.  This
module places its reachability-to-completion predicate in the semantic
Pi-institution and proves exact agreement with proof-relevant derivations.

The bridge is intentionally one-way at proof identity.  Sentence membership
records that a derivation exists; it does not recover the derivation, its
occurrences, or its cost.  A concrete two-route calculus proves this loss
rather than relying only on the fact that semantic consequence is
proposition-valued.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.ProofSearchInstitutionBridge

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.GSLTIL.SemanticPredicateInstitution
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## One admitted calculus as an institutional signature -/

/-- The generated proof-search GSLT regarded as an object of the bounded
modal signature category.  No modal translation is asserted by this object
constructor; it only chooses the underlying operational theory. -/
def proofSearchSignature (definition : ValidatedCalculusLanguageDef) :
    ModallyCoveredTheory :=
  { theory := proofSearchGSLT definition }

/-- The semantic sentence true exactly at goal lists that can reach the empty
obligation state through the authored proof-search GSLT. -/
def derivabilitySentence (definition : ValidatedCalculusLanguageDef) :
    Set GoalState :=
  { goals | (proofSearchGSLT definition).MultiStep goals [] }

/-- The same set at the exact sentence type supplied by the institutional
functor.  This bridge is definitionally transparent but is named so instance
search need not unfold a functor object to recognize ordinary set membership. -/
def derivabilityInstitutionSentence
    (definition : ValidatedCalculusLanguageDef) :
    predicateSentence.obj (Opposite.op (proofSearchSignature definition)) := by
  change Set GoalState
  exact derivabilitySentence definition

/-- Operational sentence membership is exactly proof-relevant derivability
of the same ordered goal list. -/
@[simp] theorem mem_derivabilitySentence_iff
    (definition : ValidatedCalculusLanguageDef) (goals : GoalState) :
    goals ∈ derivabilitySentence definition ↔
      Nonempty (DerivationList definition goals) := by
  simpa [derivabilitySentence] using
    (derivationList_nonempty_iff_proofSearch definition goals).symm

/-- Singleton form: the generated sentence recognizes exactly the closed
derivation fibre of one judgment. -/
@[simp] theorem singleton_mem_derivabilitySentence_iff
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    [goal] ∈ derivabilitySentence definition ↔
      Nonempty (Derivation definition goal) := by
  simpa [derivabilitySentence] using
    (derivation_nonempty_iff_proofSearch definition goal).symm

/-- Every concrete derivation projects to truth of the generated semantic
sentence at its singleton proof-search state. -/
def derivationToSentenceTruth
    {definition : ValidatedCalculusLanguageDef} {goal : Pattern}
    (derivation : Derivation definition goal) :
    [goal] ∈ derivabilitySentence definition :=
  (singleton_mem_derivabilitySentence_iff definition goal).2 ⟨derivation⟩

/-- If the proof fibre is empty, the corresponding operational state is not
in the derivability sentence.  Failure to construct a proof remains absence
of membership; it is not replaced by a fabricated negative derivation. -/
theorem not_mem_derivabilitySentence_of_no_derivation
    {definition : ValidatedCalculusLanguageDef} {goals : GoalState}
    (unprovable : ¬ Nonempty (DerivationList definition goals)) :
    goals ∉ derivabilitySentence definition := by
  intro member
  exact unprovable ((mem_derivabilitySentence_iff definition goals).1 member)

/-! ## The sentence is not automatically an institutional theorem -/

/-- Derivability is a predicate on proof-search states.  It is derivable from
no semantic premises exactly in the degenerate case where every ordered goal
list has a proof.  Merely embedding the sentence in the institution therefore
does not declare every object-language judgment true. -/
theorem institution_derives_derivabilitySentence_iff_all_goals
    (definition : ValidatedCalculusLanguageDef) :
    institution.Derives (Opposite.op (proofSearchSignature definition)) ∅
        (derivabilityInstitutionSentence definition) ↔
      ∀ goals : GoalState,
        Nonempty (DerivationList definition goals) := by
  change derivabilitySentence definition ∈
      semanticConsequence GoalState ∅ ↔ _
  rw [mem_semanticConsequence_empty_iff]
  constructor
  · intro universal goals
    exact (mem_derivabilitySentence_iff definition goals).1 (universal goals)
  · intro allGoals goals
    exact (mem_derivabilitySentence_iff definition goals).2 (allGoals goals)

/-! ## Concrete proof-identity and cost obstruction -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.CertificateGSLT.Ambient

/-- Positive control: the short authored proof puts its goal state in the
generated derivability sentence. -/
theorem ambient_goal_is_in_derivabilitySentence :
    [goalJ target] ∈ derivabilitySentence ambientValidated :=
  derivationToSentenceTruth shortProof

/-- The sentence projection is not injective on concrete derivations.  The
short and long authored routes prove the same judgment and hence give equal
sentence-truth evidence, while their proof trees have different sizes. -/
theorem sentence_truth_does_not_recover_derivation :
    ¬ Function.Injective
      (derivationToSentenceTruth
        (definition := ambientValidated) (goal := goalJ target)) := by
  intro injective
  have proofsEqual : shortProof = longProof :=
    injective (Subsingleton.elim _ _)
  have sizesEqual : derivationSize shortProof = derivationSize longProof := by
    rw [proofsEqual]
  rw [shortProof_size, longProof_size] at sizesEqual
  cases sizesEqual

/-- Trace cost still cannot be reconstructed after the operational proof has
been projected to semantic sentence truth. -/
theorem cost_does_not_factor_through_sentence_truth :
    ¬ ∃ measure :
        ([goalJ target] ∈ derivabilitySentence ambientValidated) → Nat,
      ∀ derivation : Derivation ambientValidated (goalJ target),
        measure (derivationToSentenceTruth derivation) =
          derivationSize derivation := by
  rintro ⟨measure, agrees⟩
  have shortValue := agrees shortProof
  have longValue := agrees longProof
  have truthsEqual :
      derivationToSentenceTruth shortProof =
        derivationToSentenceTruth longProof :=
    Subsingleton.elim _ _
  rw [truthsEqual, longValue] at shortValue
  rw [shortProof_size, longProof_size] at shortValue
  cases shortValue

end Canary

#print axioms mem_derivabilitySentence_iff
#print axioms singleton_mem_derivabilitySentence_iff
#print axioms not_mem_derivabilitySentence_of_no_derivation
#print axioms institution_derives_derivabilitySentence_iff_all_goals
#print axioms Canary.ambient_goal_is_in_derivabilitySentence
#print axioms Canary.sentence_truth_does_not_recover_derivation
#print axioms Canary.cost_does_not_factor_through_sentence_truth

end Mettapedia.GSLT.LanguageDef.GSLTIL.ProofSearchInstitutionBridge
