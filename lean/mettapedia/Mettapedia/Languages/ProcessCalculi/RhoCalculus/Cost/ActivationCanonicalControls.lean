import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationCanonicalSubstitution
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Runtime

/-!
# Controls for canonical communication and exact authority observations

A nonempty receiver copies signed payload code. An open quoted name shows why
whole-object quotation scope is required. Raw key collisions from unsorted
signature lists are distinguished from distinct literal authority atoms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationCanonicalControls

def nilLocation : RawCostName := .quote .nil

def copiedReceiver : RawCostTerm :=
  .par (.drop (.bvar 0))
    (.signed (.send nilLocation (.drop (.bvar 0))) ["continuation-seal"])

def signedPayload : RawCostTerm :=
  .signed (.send nilLocation .nil) ["payload-seal"]

theorem copied_receiver_scope : copiedReceiver.runtimeBinderSafeAt 1 = true := rfl

theorem signed_payload_closed : signedPayload.runtimeBinderSafeAt 0 = true := rfl

theorem copied_receiver_canonical_communication :
    (copiedReceiver.normalize.commSubst signedPayload.normalize).normalize.StructurallyEquivalent
      (copiedReceiver.commSubst signedPayload).normalize :=
  RawCostTerm.commSubst_normalize_structural 1 copied_receiver_scope signed_payload_closed

theorem copied_receiver_real_result : copiedReceiver.commSubst signedPayload =
    .par signedPayload (.signed (.send nilLocation signedPayload) ["continuation-seal"]) := rfl

theorem copied_receiver_seal_change_observed :
    ¬(copiedReceiver.commSubst signedPayload).StructurallyEquivalent
      (copiedReceiver.commSubst (.signed (.send nilLocation .nil) ["other-payload-seal"])) := by
  decide +kernel

def openQuotedReceiver : RawCostTerm := .drop (.quote (.drop (.bvar 0)))

theorem open_quoted_receiver_rejected : openQuotedReceiver.runtimeBinderSafeAt 1 = false := rfl

theorem open_quoted_normalization_communication_changes :
    ¬(openQuotedReceiver.normalize.commSubst signedPayload.normalize).normalize.StructurallyEquivalent
      (openQuotedReceiver.commSubst signedPayload).normalize := by
  decide +kernel

def openQuotedFundedSource : RawCostTerm :=
  .par (.signed (.par (.recv nilLocation openQuotedReceiver) (.send nilLocation signedPayload)) ["outer-seal"])
    (.purse nilLocation [["outer-seal"]])

theorem open_quoted_funded_source_rejected_by_actual_runtime :
    runtimeCostCandidates openQuotedFundedSource = none := rfl

theorem raw_signature_order_key_collision :
    RawCostName.signature ["alice", "bob"] ≠ RawCostName.signature ["bob", "alice"] ∧
    (RawCostName.signature ["alice", "bob"]).key =
      (RawCostName.signature ["bob", "alice"]).key := by
  decide +kernel

theorem raw_signature_order_collision_is_normalization :
    (RawCostName.signature ["alice", "bob"]).normalize =
      (RawCostName.signature ["bob", "alice"]).normalize := by
  decide +kernel

theorem authority_atom_punctuation_not_split :
    (RawCostName.signature ["alice,bob"]).key ≠
      (RawCostName.signature ["alice", "bob"]).key ∧
    ¬(RawCostName.signature ["alice,bob"]).StructurallyEquivalent
      (.signature ["alice", "bob"]) := by
  simp only [RawCostName.StructurallyEquivalent, RawCostName.structuralDenote,
    rawStructuralMultisetFrame, Multiset.coe_sort]
  have sorted : (["alice", "bob"] : List String).mergeSort
      (fun left right => decide (left ≤ right)) = ["alice", "bob"] :=
    List.mergeSort_eq_self _ (by decide +kernel)
  rw [sorted]
  simp only [List.mergeSort_singleton]
  decide +kernel

theorem ordered_purse_tail_change_observed :
    ¬(RawCostTerm.purse nilLocation [["alice"], ["bob"]]).StructurallyEquivalent
      (.purse nilLocation [["bob"], ["alice"]]) := by
  decide +kernel

theorem purse_location_change_observed :
    ¬(RawCostTerm.purse nilLocation [["alice"]]).StructurallyEquivalent
      (.purse (.quote (.signed .nil ["location-seal"])) [["alice"]]) := by
  decide +kernel

theorem parallel_occurrence_multiplicity_observed :
    ¬(RawCostTerm.par signedPayload signedPayload).StructurallyEquivalent signedPayload := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationCanonicalControls
