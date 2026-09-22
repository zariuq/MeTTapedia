import Mettapedia.TypeTheory.AuthorityOutcomeViews
import Mettapedia.GSLT.LanguageDef.NIKPropositionBranching

/-!
# Consumer views of actual finite SAT attempts

The existing assignment sampler has no outside-fragment outcome. Its public
status can therefore be recovered from its Boolean answer view. In contrast,
the empty candidate list and a rejected singleton list have the same answer
and status but different retained submissions. Neither answer nor status can
recover even the submitted candidate count.

The retained local view supports that count, including at an explicit theory
and query. This instantiates consumer requirements on the actual NIK-backed
sampler; it adds no checker, branch evaluator, global search, or storage policy.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NIKOutcomeViewControls

open Mettapedia.TypeTheory.AuthorityTheory
open Mettapedia.TypeTheory.AuthorityOutcomeViews
open NIKPropositionBranching
open NIKPropositionBranching.Controls
open CompletenessSpectrum.SAT
open CompletenessSpectrum.SAT.Canary

/-- A public-status consumer is possible for this producer: its only
no-answer constructor is incomplete, not outside-fragment. -/
theorem sample_publicStatus_factors (theory query : CNF OneVar) :
    ∃ decode : Option Bool → Outcome.PublicStatus,
      ∀ candidates : List (Assignment OneVar),
        decode (sampleAssignments theory query candidates).asBool =
          (sampleAssignments theory query candidates).publicStatus := by
  obtain ⟨decode, agrees⟩ :=
    (publicStatus_factors_asBool_iff
      (Established := (serviceAuthority.{0, 0, 0} meaning theory).Evidence query)
      (Refuted := (serviceAuthority.{0, 0, 0} meaning theory).Obstruction query)
      (Boundary := PEmpty.{1}) (Incomplete := List (Assignment OneVar))).mpr
      (by rintro ⟨⟨impossible⟩, _⟩; cases impossible)
  exact ⟨decode, fun candidates => agrees (sampleAssignments theory query candidates)⟩

def sampledReceiptSize (theory query : CNF OneVar) (candidates : List (Assignment OneVar)) :
    Option Nat :=
  (incompleteReceipt (sampleAssignments theory query candidates)).map List.length

/-- Both controls are real runs of the existing sampler on a satisfiable
query. The observable difference is submitted work, not a truth verdict. -/
theorem samples_same_answer_and_status_different_receipts :
    (sampleAssignments [] positiveFormula []).asBool =
        (sampleAssignments [] positiveFormula [falseAssignment]).asBool ∧
      (sampleAssignments [] positiveFormula []).publicStatus =
        (sampleAssignments [] positiveFormula [falseAssignment]).publicStatus ∧
      sampledReceiptSize [] positiveFormula [] = some 0 ∧
      sampledReceiptSize [] positiveFormula [falseAssignment] = some 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem sample_receiptSize_not_factors_asBool :
    ¬ ∃ decode : Option Bool → Option Nat,
      ∀ candidates : List (Assignment OneVar),
        decode (sampleAssignments [] positiveFormula candidates).asBool =
          sampledReceiptSize [] positiveFormula candidates := by
  rintro ⟨decode, agrees⟩
  have impossible : (some 0 : Option Nat) = some 1 :=
    (agrees []).symm.trans (agrees [falseAssignment])
  cases impossible

theorem sample_receiptSize_not_factors_publicStatus :
    ¬ ∃ decode : Outcome.PublicStatus → Option Nat,
      ∀ candidates : List (Assignment OneVar),
        decode (sampleAssignments [] positiveFormula candidates).publicStatus =
          sampledReceiptSize [] positiveFormula candidates := by
  rintro ⟨decode, agrees⟩
  have impossible : (some 0 : Option Nat) = some 1 :=
    (agrees []).symm.trans (agrees [falseAssignment])
  cases impossible

theorem retained_sample_supports_receiptSize (theory query : CNF OneVar)
    (candidates : List (Assignment OneVar)) :
    (retainedIncompleteReceipt (retainedView (sampleAssignments theory query candidates))).map
        List.length = sampledReceiptSize theory query candidates := by
  rw [retainedView_supports_incompleteReceipt]
  rfl

/-- A theory/query-indexed presentation carries the actual submitted list.
The index is explicit even though this example's receipt type is constant. -/
def scopedSampleView (theory query : CNF OneVar) (candidates : List (Assignment OneVar)) :
    IndexedView (fun _ : CNF OneVar × CNF OneVar => PEmpty.{1})
      (fun _ => List (Assignment OneVar)) :=
  indexedView (theory, query) (sampleAssignments theory query candidates)

theorem scoped_failed_sample_retains_submission :
    indexedIncompleteReceipt (scopedSampleView [] positiveFormula [falseAssignment]) =
      some ((⟨([], positiveFormula), [falseAssignment]⟩) :
        Σ _ : CNF OneVar × CNF OneVar, List (Assignment OneVar)) := rfl

/-- Successful search has a checked positive answer and no incomplete
receipt; the retained view does not invent an unresolved submission. -/
theorem successful_sample_has_no_incomplete_receipt :
    (retainedView
      (sampleAssignments [] positiveFormula [falseAssignment, trueAssignment])).1 = some true ∧
      indexedIncompleteReceipt
        (scopedSampleView [] positiveFormula [falseAssignment, trueAssignment]) = none :=
  ⟨rfl, rfl⟩

#print axioms sample_publicStatus_factors
#print axioms sample_receiptSize_not_factors_asBool
#print axioms sample_receiptSize_not_factors_publicStatus
#print axioms retained_sample_supports_receiptSize
#print axioms scoped_failed_sample_retains_submission

end Mettapedia.GSLT.LanguageDef.NIKOutcomeViewControls
