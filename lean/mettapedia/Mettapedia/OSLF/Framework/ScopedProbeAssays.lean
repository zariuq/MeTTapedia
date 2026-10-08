import Mettapedia.GSLT.Causality.ProbeAssayExecution
import Mettapedia.OSLF.Framework.ScopedFundedAssays

/-!
# Actual probe deliveries checked against quotient scopes

The delivered payload is an actual parallel equation class. The independent
composite-scope decision supplies the complementary guard, and every maximal
affordable execution earns the original quotient predicate or its negation.
The response's provider, requester and class survive in its receipt. Delivery
and scope-testing prices are declared schedules; predicate queries do not by
themselves price either raw scope implementation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ParallelFragment

open Mettapedia.Algebra.SupportSeparatedDecomposition
open Mettapedia.GSLT.Causality ResourceInteraction OccurrenceHistory
open ComplementaryAssay (verdictOf)

universe v w

variable {Providers : Type v} {Clients : Type w} [DecidableEq Providers] [DecidableEq Clients]
variable {classify : Fin 3 → Bool}
variable {left right : Term psig [] PSrt.proc → Prop}
variable [DecidablePred left] [DecidablePred right]

theorem maximal_probed_scope
    (leftInvariant : ScopeInvariant left) (rightInvariant : ScopeInvariant right)
    (leftSupported : LeftSupported classify (inventoryScope left))
    (rightSupported : RightSupported classify (inventoryScope right))
    (deliveryCost inspectionCost : ParallelClass → Nat)
    (session : Nat) (provider : Providers) (client : Clients) (value : ParallelClass) (budget : Nat)
    (affordable : deliveryCost value + inspectionCost value ≤ budget)
    {target : Multiset (AssayProbeDelivery.Resources ParallelClass Providers Clients ⊕ Unit)}
    (path : OccurrencePath
      (AssayProbeDelivery.paid (decideCompositeQ classify left right) deliveryCost inspectionCost).presentation
      (AssayProbeDelivery.paidOffered session provider client value budget) target)
    (maximal : AssayProbeDelivery.Maximal
      (decideCompositeQ classify left right) deliveryCost inspectionCost target) :
    AssayProbeDelivery.outputs (leftPart target) =
        { (session, verdictOf (decideCompositeQ classify left right value), client, value) } ∧
      ScopeCertificate leftInvariant rightInvariant
        (verdictOf (decideCompositeQ classify left right value)) value ∧
      ((AssayProbeDelivery.paid (decideCompositeQ classify left right)
        deliveryCost inspectionCost).pathEntries path).length = 2 ∧
      rightPart (leftPart target) =
        {AssayProbeDelivery.ProbeResource.delivered session provider client value} ∧
      budget = (rightPart target).card + deliveryCost value + inspectionCost value := by
  obtain ⟨verdict, entries, receipt, account⟩ := AssayProbeDelivery.maximal_affordable_verdict
    (decideCompositeQ classify left right) deliveryCost inspectionCost
    session provider client value budget affordable path maximal
  exact ⟨verdict, scope_firing_certificate leftInvariant rightInvariant leftSupported rightSupported
    (ComplementaryAssay.selected (decideCompositeQ classify left right) session client value),
      entries, receipt, account⟩

end Mettapedia.OSLF.Binding.ParallelFragment
