import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsWorldModelRules
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsWorldModelControls

/-!
# Revision, deduction and budgeted counts on concrete evidence

## Revision at the end of the raven run

The revision firing reads the evidence space where the raven run ends and makes the row of the
counts `(4, 1)` at the fresh identity `20`.

* It is admitted (`revision_fires`), and its row is the overlap revision of the two submissions,
  `(3, 0) + (2, 1) - (1, 0)` (`revision_is_overlap_revision`).
* A predicate query that saw only the first submission is refused (`partial_query_refused`).

## Budgeted counts of the same ledger

* Budget `0` finds nothing and is incomplete: it is not "no evidence", while the evidence is
  `(4, 1)` (`exhausted_not_no_evidence`).
* Budget `3` finds the first submission and reports `(3, 0)` as a lower bound
  (`partial_scan_lower_bound`).
* Budget `7` finishes and counts `(4, 1)` (`full_scan_counts`).

## Deduction on bags of worlds

* A bag of eight worlds over `A`, `B`, `C` screens off; the deduction formula and the world-model
  answer are both `1/2` (`screened_deduction`).
* The bag of `EvidenceContracts.Controls.deduction_fails_without_screening` does not screen off, so
  the deduction guard refuses it (`unscreened_refused`), where the formula would give `1/4` against
  the answer `0`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

namespace WorldModelRuns

namespace RuleControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open RavenControls (label space black isBlack empty ravenRun final_ledger union_evidence
  first_evidence second_evidence cited_first cited_second ledger_eq_union submitSecond_valid
  ledger_row)
open Mettapedia.PLN.WorldModel.EvidenceSpaces
open Mettapedia.PLN.WorldModel.EvidenceContracts
open Mettapedia.PLN.WorldModel.EvidenceContracts.Controls (World3 unscreened)
open AnnotatedRunCandidates (Status)

/-- Rows of counts, outside the evidence space. -/
def row (e : Evidence ℕ) : Term signature :=
  ConstraintMultisetRewriting.Controls.f (.const (Nat.pair e.pos e.neg))

/-- Where the raven run ends. -/
abbrev finalConfig : Configuration (Term signature) Nat := follow label empty ravenRun

theorem final_consistent : A.Consistent finalConfig.equations :=
  submitSecond_valid.firing.consistent

/-- **The revision firing is admitted where the raven run ends.** -/
theorem revision_fires :
    (revisionFiring (S := Subst signature) label space black isBlack row {1, 2, 3, 4, 5} 20).Valid
      A label finalConfig := by
  rw [revisionFiring_valid_iff]
  refine ⟨final_ledger, by decide, ?_, final_consistent⟩
  rw [union_evidence]
  rfl

/-- **Its row is the overlap revision of the two submissions.** -/
theorem revision_is_overlap_revision :
    label 20 = row (⟨3, 0⟩ + ⟨2, 1⟩ - ⟨1, 0⟩) := by
  have union := revision_adequate_union A label space black revision_fires ledger_eq_union
  have overlap :
      ledgerEvidence (recorded label black) isBlack ({1, 2, 3} ∩ {3, 4, 5}) = ⟨1, 0⟩ := by
    ext <;> decide
  rw [cited_first, cited_second, first_evidence, second_evidence, overlap] at union
  exact union

/-- **A predicate query that saw only the first submission is refused.** -/
theorem partial_query_refused :
    ¬ (revisionFiring (S := Subst signature) label space black isBlack row {1, 2, 3} 20).Valid
      A label finalConfig :=
  revisionFiring_refused A label space black isBlack row 20 (by rw [final_ledger]; decide)

/-- The scan list: the occurrences present where the raven run ends. -/
def contents : List Nat := [1, 2, 3, 4, 5, 11, 12]

theorem final_present : finalConfig.present = {1, 2, 3, 4, 5, 11, 12} := by decide

theorem contents_cover : Covers contents finalConfig := by
  intro o
  rw [final_present]
  simp [contents]

/-- **An exhausted scan is not "no evidence"**: budget `0` finds nothing and is incomplete, while
the evidence is `(4, 1)`. -/
theorem exhausted_not_no_evidence :
    scanStatus contents 0 = .incomplete ∧
      budgetedCount label space black isBlack contents 0 = .incomplete 0 ∧
      ¬ NoEvidence (budgetedCount label space black isBlack contents 0) ∧
      readout label space black isBlack finalConfig = ⟨4, 1⟩ := by
  have incomplete : scanStatus contents 0 = .incomplete := by decide
  have found : scanFound label space contents 0 = ∅ := by decide
  refine ⟨incomplete, ?_, incomplete_never_noEvidence label space black isBlack incomplete,
    ledger_row.1⟩
  unfold budgetedCount
  rw [incomplete, found]
  simp [ledgerEvidence]

/-- **A partial scan is a lower bound**: budget `3` finds the first submission. -/
theorem partial_scan_lower_bound :
    budgetedCount label space black isBlack contents 3 = .incomplete ⟨3, 0⟩ ∧
      (⟨3, 0⟩ : Evidence ℕ) ≤ readout label space black isBlack finalConfig := by
  have incomplete : scanStatus contents 3 = .incomplete := by decide
  have found : scanFound label space contents 3 = {1, 2, 3} := by decide
  have reported : budgetedCount label space black isBlack contents 3 = .incomplete ⟨3, 0⟩ := by
    unfold budgetedCount
    rw [incomplete, found, first_evidence]
  exact ⟨reported, incomplete_lower_bound label space black isBlack contents_cover reported⟩

/-- **A finished scan counts the ledger.** -/
theorem full_scan_counts :
    budgetedCount label space black isBlack contents 7 = .counted ⟨4, 1⟩ := by
  rw [complete_counts label space black isBlack contents_cover (by decide), ledger_row.1]

/-! ## Deduction on bags of worlds -/

/-- The antecedent, the middle term and the conclusion. -/
def pa : World3 → Bool := fun w => w.1
def pb : World3 → Bool := fun w => w.2.1
def pc : World3 → Bool := fun w => w.2.2

/-- Eight worlds in which `B` screens `C` off from `A`. -/
def screenedBag : Multiset World3 :=
  {(true, true, true), (true, true, true), (true, true, false), (false, true, true),
    (false, true, true), (false, true, false), (true, false, false), (false, false, false)}

theorem screenedBag_screened : Screened pa pb pc screenedBag := by decide

/-- **Positive control**: the deduction formula is the world-model answer, `1/2`. -/
theorem screened_deduction :
    deductionValue pa pb pc screenedBag = 1 / 2 ∧ linkValue pa pc screenedBag = 1 / 2 := by
  have link : linkValue pa pc screenedBag = 1 / 2 := by
    have ac : count screenedBag (fun w => pa w && pc w) = 2 := by decide
    have a : count screenedBag pa = 4 := by decide
    unfold linkValue
    rw [ac, a]
    norm_num
  exact ⟨(deductionValue_eq_linkValue pa pb pc screenedBag_screened).trans link, link⟩

/-- **Negative control**: the bag on which the formula fails does not screen off, so the guard
refuses deduction there. -/
theorem unscreened_refused : ¬ Screened pa pb pc unscreened := by decide

end RuleControls

end WorldModelRuns

open WorldModelRuns

#print axioms RuleControls.revision_fires
#print axioms RuleControls.revision_is_overlap_revision
#print axioms RuleControls.partial_query_refused
#print axioms RuleControls.contents_cover
#print axioms RuleControls.exhausted_not_no_evidence
#print axioms RuleControls.partial_scan_lower_bound
#print axioms RuleControls.full_scan_counts
#print axioms RuleControls.screenedBag_screened
#print axioms RuleControls.screened_deduction
#print axioms RuleControls.unscreened_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
