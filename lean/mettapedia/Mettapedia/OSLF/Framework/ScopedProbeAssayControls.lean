import Mettapedia.OSLF.Framework.ScopedProbeAssays
import Mettapedia.OSLF.Framework.ScopedFundedAssayControls

/-!
# Quotient scope probe controls with retained multiplicities

These controls declare the existing classifier-query fee as their inspection
schedule. It does not assert a complete cost for both raw scope predicates.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ParallelFragment.ScopeProbeControls

open Mettapedia.GSLT.Causality ResourceInteraction OccurrenceHistory
open ComplementaryAssay (Verdict)
open ScopeControls ScopeAssayControls

def deliveryCost (_ : ParallelClass) : Nat := 2

theorem actual_quotient_delivery_confirmed :
    AssayProbeDelivery.observed membershipTest deliveryCost classifierFee
      10 (3 : Nat) (7 : Nat) (some (classOf ordered)) 7 = expected := by
  rw [AssayProbeDelivery.observed_some]
  decide

theorem authored_reordering_preserves_probe :
    AssayProbeDelivery.observed membershipTest deliveryCost classifierFee
      10 (3 : Nat) (7 : Nat) (some (classOf reversed)) 7 = expected := by
  rw [← authored_reordering_same_class]
  exact actual_quotient_delivery_confirmed

theorem outside_scope_refuted_after_delivery :
    AssayProbeDelivery.observed membershipTest deliveryCost classifierFee
      10 (3 : Nat) (7 : Nat) (some (classOf (parT ordered (u 1)))) 8 =
      { (10, Verdict.refute, 7, classOf (parT ordered (u 1))) } := by
  rw [AssayProbeDelivery.observed_some]
  decide

theorem delivered_class_retains_multiplicity :
    (inventoryQ (classOf ordered)).count 0 = 2 ∧
      (inventoryQ (classOf ordered)).count 2 = 3 ∧
      rightPart (leftPart
        (AssayProbeDelivery.execute membershipTest deliveryCost classifierFee
          10 (3 : Nat) (7 : Nat) (some (classOf ordered)) 6).1) =
        {AssayProbeDelivery.ProbeResource.delivered 10 3 7 (classOf ordered)} := by
  refine ⟨by decide, by decide, ?_⟩
  change rightPart (leftPart (AssayProbeDelivery.paidReceived 10 (3 : Nat) (7 : Nat) (classOf ordered) 4)) = _
  rw [AssayProbeDelivery.paidReceived, leftPart_marking,
    AssayProbeDelivery.received, rightPart_marking]

theorem actual_complete_probe_earns_original_membership :
    ScopeCertificate leftInvariant rightInvariant .confirm (classOf ordered) := by
  have result := maximal_probed_scope leftInvariant rightInvariant leftSupported rightSupported
    deliveryCost classifierFee 10 (3 : Nat) (7 : Nat) (classOf ordered) 7 (by decide)
    (AssayProbeDelivery.completeRun membershipTest deliveryCost classifierFee
      10 (3 : Nat) (7 : Nat) (classOf ordered) 7 (by decide) (by decide))
    (AssayProbeDelivery.paid_tested_stuck membershipTest deliveryCost classifierFee
      10 (3 : Nat) (7 : Nat) (classOf ordered) 0)
  exact result.2.1

end Mettapedia.OSLF.Binding.ParallelFragment.ScopeProbeControls
