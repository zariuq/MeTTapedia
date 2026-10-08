import Mettapedia.OSLF.Framework.ScopedFundedAssays
import Mettapedia.OSLF.Syntax.ParallelScopeDecisionControls

/-!
# Actual quotient payloads through funded scope assays

Repeated output occurrences survive the complete verdict payload. Reordering
the authored parallel syntax yields the same accepted payload class. A name
outside both scopes earns a refutation, while an underfunded delivered
payload earns neither verdict. Distinct origins remain in the receipts.
The selected price is the classifier-query fee, not a complete predicate
evaluation account.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ParallelFragment.ScopeAssayControls

open Mettapedia.GSLT.Causality ResourceInteraction ComplementaryAssay
open ScopeControls

def membershipTest : ParallelClass → Bool := decideCompositeQ classify leftScope rightScope
def classifierFee (value : ParallelClass) : Nat := (inventoryQ value).card

def expected : Multiset (Nat × Verdict × Nat × ParallelClass) :=
  { (10, .confirm, 7, classOf ordered) }

theorem positive_complete_readout :
    observed membershipTest classifierFee 10 7 (some (classOf ordered)) 5 = expected := by decide

theorem reordered_same_complete_readout :
    observed membershipTest classifierFee 10 7 (some (classOf reversed)) 5 = expected := by
  rw [← authored_reordering_same_class]
  exact positive_complete_readout

theorem query_fee_is_five : classifierFee (classOf ordered) = 5 := by decide

theorem full_received_multiplicities :
    (inventoryQ (classOf ordered)).count 0 = 2 ∧
      (inventoryQ (classOf ordered)).count 2 = 3 := by decide

theorem negative_complete_readout :
    observed membershipTest classifierFee 10 7 (some (classOf (parT ordered (u 1)))) 6 =
      { (10, .refute, 7, classOf (parT ordered (u 1))) } := by decide

theorem negative_certificate :
    ¬ CompositeScopeQ leftScope rightScope leftInvariant rightInvariant
      (classOf (parT ordered (u 1))) :=
  (decideCompositeQ_false_iff leftInvariant rightInvariant leftSupported rightSupported _).1
    rejects_unadmitted_channel

theorem positive_firing_supplies_original_membership :
    ScopeCertificate leftInvariant rightInvariant .confirm (classOf ordered) :=
  scope_firing_certificate leftInvariant rightInvariant leftSupported rightSupported
    (selected membershipTest 10 (7 : Nat) (classOf ordered))

theorem underfunded_keeps_the_actual_message :
    observed membershipTest classifierFee 10 7 (some (classOf ordered)) 4 = 0 ∧
      Multiset.Mem
        ((execute membershipTest classifierFee 10 (7 : Nat) (some (classOf ordered)) 4).1)
        (Sum.inl (Resource.message 10 (classOf ordered)) : Resource ParallelClass Nat ⊕ Unit) := by
  constructor
  · decide
  · change (Sum.inl (Resource.message 10 (classOf ordered)) : Resource ParallelClass Nat ⊕ Unit) ∈
      marking (ready 10 7 (classOf ordered)) (purse 4)
    decide

theorem no_response_no_verdict :
    observed membershipTest classifierFee 10 7 none 5 = 0 := observed_none _ _ _ _ _

theorem equal_public_membership_different_origins :
    observed membershipTest classifierFee 10 7 (some (classOf ordered)) 5 ≠
      observed membershipTest classifierFee 10 8 (some (classOf ordered)) 5 := by decide

theorem paid_query_account :
    5 = (rightPart (completed membershipTest classifierFee 10 (7 : Nat) (classOf ordered) 5)).card +
      (inventoryQ (classOf ordered)).card :=
  paidRun_conserved membershipTest classifierFee 10 7 (classOf ordered) 5 (by decide)

end Mettapedia.OSLF.Binding.ParallelFragment.ScopeAssayControls
