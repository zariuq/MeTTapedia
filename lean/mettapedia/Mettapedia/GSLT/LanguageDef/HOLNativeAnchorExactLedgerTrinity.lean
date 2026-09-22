import Mettapedia.GSLT.LanguageDef.HOLNativeSourceAdequacy
import Mettapedia.GSLT.LanguageDef.CertificateGSLTLedgerDependentFamily

/-!
# HOL kernel anchors in the exact-ledger displayed family

The existing HOL Light `EQ_MP` and HOL4 `DISCH` source anchors each have an
independent source derivation, an admitted checked certificate, and exact raw
proof erasure. Their already-checked certificates become proof-bearing points
of the generic exact-ledger displayed family; OSLF observes their completion
without replacing or identifying the certificates. This is confined to the
two selected source fragments, not a general HOL embedding.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.HOLNativeAnchorExactLedgerTrinity

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.HOLNativeGSLTSlice
open Mettapedia.GSLT.LanguageDef.HOLNativeSourceAdequacy
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenSearchMachine
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

noncomputable def holLightChecked :
    Derivation holLightAdmittedSource.definition holLightGoal :=
  Classical.choose holLight_checked_native_anchor

theorem holLightChecked_certificate :
    HOLLightAnchorCertificate holLightChecked :=
  Classical.choose_spec holLight_checked_native_anchor

/-- The selected HOL Light checked proof, not an arbitrary inhabitance proof,
is the displayed certificate. -/
noncomputable def holLightExactReceipt :
    exactDerivationFibre holLightAdmittedSource.definition ⟨[]⟩
      holLightGoal [] :=
  closedExactDerivationFibre holLightChecked

theorem holLightExactReceipt_erases :
    holLightExactReceipt.val.close.erase = holLightEqMpProof := by
  simpa only [holLightExactReceipt, closedExactDerivationFibre_close] using
    holLightChecked_certificate.erasure

/-- The checked HOL Light proof supplies its operational route and computed
discharge ledger without choosing another certificate. -/
noncomputable def holLightOperationalReceipt :=
  exactDerivationRouteReceipt holLightExactReceipt

theorem holLightOperationalReceipt_recovers :
    (derivationOfCompleteRoute holLightOperationalReceipt.2).close.erase =
      holLightEqMpProof := by
  rw [holLightOperationalReceipt, exactDerivationRouteReceipt_reconstruct]
  exact holLightExactReceipt_erases

/-- The source-rule proof and the checked displayed proof have the same
encoded theorem, while their proof representations remain distinct. -/
theorem holLight_source_checked_alignment :
    Nonempty (HOLLightSource.Derives [propositionP] propositionP) ∧
      holLightExactReceipt.val.close.erase = holLightEqMpProof ∧
      holLightGoal = holLightNativeProfile.derived
        (encodeTheorem [propositionP] propositionP) :=
  ⟨holLightChecked_certificate.sourceDerivation,
    holLightExactReceipt_erases,
    holLightChecked_certificate.goalEncoding⟩

theorem holLight_operational_source_alignment :
    Nonempty (HOLLightSource.Derives [propositionP] propositionP) ∧
      (derivationOfCompleteRoute holLightOperationalReceipt.2).close.erase =
        holLightEqMpProof ∧
      holLightGoal = holLightNativeProfile.derived
        (encodeTheorem [propositionP] propositionP) :=
  ⟨holLightChecked_certificate.sourceDerivation,
    holLightOperationalReceipt_recovers,
    holLightChecked_certificate.goalEncoding⟩

noncomputable def holLightDisplayedPoint :
    (exactDerivationDisplayedFamily holLightAdmittedSource.definition).Elements :=
  closedExactDisplayedPoint holLightChecked

theorem holLightClosureCompletion :
    gsltDiamond
      (CertificateGSLT.OpenSearchModalAdequacy.theory
        holLightAdmittedSource.definition []).closure
      (fun candidate => candidate =
        (⟨[], []⟩ : State []))
      ⟨[holLightGoal], []⟩ :=
  (exactDerivationFibre_nonempty_iff_closureDiamond
    holLightAdmittedSource.definition ⟨[]⟩ holLightGoal []).mp
      ⟨holLightExactReceipt⟩

noncomputable def hol4Checked :
    Derivation hol4AdmittedSource.definition hol4Goal :=
  Classical.choose hol4_checked_native_anchor

theorem hol4Checked_certificate :
    HOL4AnchorCertificate hol4Checked :=
  Classical.choose_spec hol4_checked_native_anchor

noncomputable def hol4ExactReceipt :
    exactDerivationFibre hol4AdmittedSource.definition ⟨[]⟩
      hol4Goal [] :=
  closedExactDerivationFibre hol4Checked

theorem hol4ExactReceipt_erases :
    hol4ExactReceipt.val.close.erase = hol4DischProof := by
  simpa only [hol4ExactReceipt, closedExactDerivationFibre_close] using
    hol4Checked_certificate.erasure

noncomputable def hol4OperationalReceipt :=
  exactDerivationRouteReceipt hol4ExactReceipt

theorem hol4OperationalReceipt_recovers :
    (derivationOfCompleteRoute hol4OperationalReceipt.2).close.erase =
      hol4DischProof := by
  rw [hol4OperationalReceipt, exactDerivationRouteReceipt_reconstruct]
  exact hol4ExactReceipt_erases

theorem hol4_source_checked_alignment :
    Nonempty
        (HOL4Source.Derives ∅ (.implication propositionP propositionP)) ∧
      hol4ExactReceipt.val.close.erase = hol4DischProof ∧
      hol4Goal = hol4NativeProfile.derived
        (encodeTheorem [] (.implication propositionP propositionP)) :=
  ⟨hol4Checked_certificate.sourceDerivation,
    hol4ExactReceipt_erases,
    hol4Checked_certificate.goalEncoding⟩

theorem hol4_operational_source_alignment :
    Nonempty
        (HOL4Source.Derives ∅ (.implication propositionP propositionP)) ∧
      (derivationOfCompleteRoute hol4OperationalReceipt.2).close.erase =
        hol4DischProof ∧
      hol4Goal = hol4NativeProfile.derived
        (encodeTheorem [] (.implication propositionP propositionP)) :=
  ⟨hol4Checked_certificate.sourceDerivation,
    hol4OperationalReceipt_recovers,
    hol4Checked_certificate.goalEncoding⟩

noncomputable def hol4DisplayedPoint :
    (exactDerivationDisplayedFamily hol4AdmittedSource.definition).Elements :=
  closedExactDisplayedPoint hol4Checked

theorem hol4ClosureCompletion :
    gsltDiamond
      (CertificateGSLT.OpenSearchModalAdequacy.theory
        hol4AdmittedSource.definition []).closure
      (fun candidate => candidate =
        (⟨[], []⟩ : State []))
      ⟨[hol4Goal], []⟩ :=
  (exactDerivationFibre_nonempty_iff_closureDiamond
    hol4AdmittedSource.definition ⟨[]⟩ hol4Goal []).mp
      ⟨hol4ExactReceipt⟩

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
/-- Swapping the two HOL Light theorem children does not supply a checked
proof, even though each child separately has a valid source derivation. -/
theorem holLight_wrong_child_order_rejected :
    holLightAdmittedSource.checkRaw holLightGoal
      holLightWrongChildOrderProof = false := by
  decide +kernel

theorem holLight_wrong_child_order_no_exact_receipt :
    ¬ ∃ receipt : exactDerivationFibre
        holLightAdmittedSource.definition ⟨[]⟩ holLightGoal [],
      receipt.val.close.erase = holLightWrongChildOrderProof := by
  rintro ⟨receipt, erases⟩
  have accepted :=
    Mettapedia.GSLT.LanguageDef.CheckedSource.CheckedGSLT.checkRaw_erase
      (checked := holLightAdmittedSource) receipt.val.close
  rw [erases, holLight_wrong_child_order_rejected] at accepted
  contradiction

/-- HOL4 discharge fails if the context-removal evidence is missing; this
cannot be repaired by forgetting the proof into a modal completion fact. -/
theorem hol4_missing_removal_rejected :
    hol4AdmittedSource.checkRaw hol4Goal
      hol4MissingRemovalProof = false := by
  decide +kernel

theorem hol4_missing_removal_no_exact_receipt :
    ¬ ∃ receipt : exactDerivationFibre
        hol4AdmittedSource.definition ⟨[]⟩ hol4Goal [],
      receipt.val.close.erase = hol4MissingRemovalProof := by
  rintro ⟨receipt, erases⟩
  have accepted :=
    Mettapedia.GSLT.LanguageDef.CheckedSource.CheckedGSLT.checkRaw_erase
      (checked := hol4AdmittedSource) receipt.val.close
  rw [erases, hol4_missing_removal_rejected] at accepted
  contradiction

end Mettapedia.GSLT.LanguageDef.HOLNativeAnchorExactLedgerTrinity

#print axioms Mettapedia.GSLT.LanguageDef.HOLNativeAnchorExactLedgerTrinity.holLight_source_checked_alignment
#print axioms Mettapedia.GSLT.LanguageDef.HOLNativeAnchorExactLedgerTrinity.holLightOperationalReceipt_recovers
#print axioms Mettapedia.GSLT.LanguageDef.HOLNativeAnchorExactLedgerTrinity.holLight_operational_source_alignment
#print axioms Mettapedia.GSLT.LanguageDef.HOLNativeAnchorExactLedgerTrinity.holLightClosureCompletion
#print axioms Mettapedia.GSLT.LanguageDef.HOLNativeAnchorExactLedgerTrinity.hol4_source_checked_alignment
#print axioms Mettapedia.GSLT.LanguageDef.HOLNativeAnchorExactLedgerTrinity.hol4OperationalReceipt_recovers
#print axioms Mettapedia.GSLT.LanguageDef.HOLNativeAnchorExactLedgerTrinity.hol4_operational_source_alignment
#print axioms Mettapedia.GSLT.LanguageDef.HOLNativeAnchorExactLedgerTrinity.hol4ClosureCompletion
#print axioms Mettapedia.GSLT.LanguageDef.HOLNativeAnchorExactLedgerTrinity.holLight_wrong_child_order_no_exact_receipt
#print axioms Mettapedia.GSLT.LanguageDef.HOLNativeAnchorExactLedgerTrinity.hol4_missing_removal_no_exact_receipt
