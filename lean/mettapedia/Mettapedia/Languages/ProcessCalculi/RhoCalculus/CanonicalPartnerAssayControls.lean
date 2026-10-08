import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalPartnerAssays
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalPartnerControls

/-!
# Complete COMM assays retain inventories and addressed firing origins
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalPartnerAssayControls

open Mettapedia.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open CanonicalBag CanonicalPartnerCoalgebra CanonicalPartnerObservations
open CanonicalPartnerAssays CanonicalReactionControls
open LanguageDefGSLT HennessyMilnerRho
open LanguageDefRewriteSystem

def multiplicity (bag : Bag) : Nat := bag.val.card

def firstObserved : AssayedReceipt multiplicity rule.redex oneOutput :=
  assayReceipt multiplicity rule.redex oneOutput CanonicalPartnerControls.first

def secondObserved : AssayedReceipt multiplicity rule.redex oneOutput :=
  assayReceipt multiplicity rule.redex oneOutput CanonicalPartnerControls.second

theorem first_actual_occurrence :
    firstObserved.occurrence = CanonicalPartnerControls.first := rfl

theorem both_complete_successors :
    firstObserved.targetObservation ∈ FiniteActionTree.Tree.step
        (certificateObservation Nat multiplicity rule.redex) oneOutput ∧
      secondObserved.targetObservation ∈ FiniteActionTree.Tree.step
        (certificateObservation Nat multiplicity rule.redex) oneOutput :=
  ⟨firstObserved.successor, secondObserved.successor⟩

theorem actual_inventory_multiplicity :
    FiniteActionTree.Tree.root firstObserved.targetObservation = 2 := by
  rw [firstObserved.target_root]
  change multiplicity CanonicalPartnerControls.first.target = 2
  rw [multiplicity, CanonicalPartnerControls.duplicate_complete_inventory]
  rfl

theorem no_origin_erasure : firstObserved.occurrence ≠ secondObserved.occurrence :=
  CanonicalReactionControls.different_occurrences

theorem exact_same_whole_assay :
    firstObserved.targetObservation = secondObserved.targetObservation :=
  congrArg (certificateObservation Nat multiplicity) CanonicalReactionControls.same_endpoint

/-- Every future assay still describes a state. Even a complete supplied Bag
readout cannot reconstruct which duplicate addressed COMM occurrence fired. -/
theorem no_whole_assay_origin_decoder (Colours : Type) (readout : Bag → Colours) :
    ¬ ∃ decode : FiniteActionTree.Tree Bag Colours → Receipt rule.redex oneOutput,
      ∀ receipt, decode (certificateObservation Colours readout receipt.target) = receipt := by
  rintro ⟨decode, exactOrigins⟩
  apply CanonicalReactionControls.different_occurrences
  exact (exactOrigins CanonicalPartnerControls.first).symm.trans
    ((congrArg decode (congrArg (certificateObservation Colours readout)
      CanonicalReactionControls.same_endpoint)).trans
        (exactOrigins CanonicalPartnerControls.second))

theorem bare_reduction_is_insufficient :
    (HennessyMilnerInstance.rhoSystem PEmpty.{1} (fun atom => atom.elim)).Bisimilar
        ParallelContextAdequacy.waitingInput closedNil ∧
      ¬ CanonicalPartnerAssays.Bisimilar multiplicity
        (fromProcess ParallelContextAdequacy.waitingInput) (fromProcess closedNil) := by
  refine ⟨ParallelContextAdequacy.waitingInput_reduction_bisimilar_nil, ?_⟩
  intro assayed
  exact ParallelContextAdequacy.waitingInput_not_partner_bisimilar_nil
    (CanonicalPartnerObservations.public_bisimilar_of_canonical
      (CanonicalPartnerAssays.interaction_of_assay multiplicity assayed))

theorem actual_partner_origin_is_reassayed
    (receipt : Receipt rule.redex oneOutput) :
    certificateObservation Nat multiplicity receipt.target ∈
      FiniteActionTree.Tree.step (certificateObservation Nat multiplicity rule.redex) oneOutput :=
  (assayReceipt multiplicity rule.redex oneOutput receipt).successor

theorem supplied_inventory_kernel (first second : Bag) :
    certificateObservation (Multiset Pattern) Subtype.val first =
        certificateObservation (Multiset Pattern) Subtype.val second ↔
      CanonicalPartnerAssays.Bisimilar Subtype.val first second :=
  future_assay_iff_bisimilar Subtype.val first second

theorem full_inventory_is_nonconstant :
    (certificateObservation (Multiset Pattern) Subtype.val
      CanonicalPartnerControls.first.target) ≠
        certificateObservation (Multiset Pattern) Subtype.val empty := by
  intro same
  have inventories := congrArg FiniteActionTree.Tree.root same
  have readings : CanonicalPartnerControls.first.target.val = empty.val :=
    (certificate_root (Multiset Pattern) Subtype.val CanonicalPartnerControls.first.target).symm.trans
      (inventories.trans (certificate_root (Multiset Pattern) Subtype.val empty))
  rw [CanonicalPartnerControls.duplicate_complete_inventory] at readings
  have sizes := congrArg Multiset.card readings
  simp [empty] at sizes

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalPartnerAssayControls
