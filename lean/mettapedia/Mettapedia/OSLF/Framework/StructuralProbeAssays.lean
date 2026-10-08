import Mettapedia.GSLT.Causality.ProbeAssayExecution
import Mettapedia.OSLF.Framework.StructuralInspectionAssays

/-!
# Structural inspection after an actual funded probe delivery

The probe protocol delivers a whole structural tree. Its complementary guard
uses the computed inspection answer and price. Every supplied maximal,
affordable two-stage execution returns the actual tree, earns its independently
defined structural certificate and keeps the provider's delivery receipt.
The purse pays separately for delivery and for complete inspection.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.InstrumentObservations

open Mettapedia.GSLT.Causality ResourceInteraction OccurrenceHistory
open ComplementaryAssay (Verdict verdictOf)

universe u v w

variable {Symbols : Type u} {arity : Symbols → Nat} [DecidableEq Symbols]
variable {Providers : Type v} {Clients : Type w} [DecidableEq Providers] [DecidableEq Clients]

theorem maximal_probed_inspection (formula : Formula Symbols arity)
    (deliveryCost : Tree Symbols arity → Nat)
    (session : Nat) (provider : Providers) (client : Clients) (tree : Tree Symbols arity) (budget : Nat)
    (affordable : deliveryCost tree + (inspect formula tree).2 ≤ budget)
    {target : Multiset (AssayProbeDelivery.Resources (Tree Symbols arity) Providers Clients ⊕ Unit)}
    (path : OccurrencePath
      (AssayProbeDelivery.paid (fun value => (inspect formula value).1)
        deliveryCost (fun value => (inspect formula value).2)).presentation
      (AssayProbeDelivery.paidOffered session provider client tree budget) target)
    (maximal : AssayProbeDelivery.Maximal (fun value => (inspect formula value).1)
      deliveryCost (fun value => (inspect formula value).2) target) :
    AssayProbeDelivery.outputs (leftPart target) =
        { (session, verdictOf (inspect formula tree).1, client, tree) } ∧
      TestCertificate formula (verdictOf (inspect formula tree).1) tree ∧
      ((AssayProbeDelivery.paid (fun value => (inspect formula value).1)
        deliveryCost (fun value => (inspect formula value).2)).pathEntries path).length = 2 ∧
      rightPart (leftPart target) =
        {AssayProbeDelivery.ProbeResource.delivered session provider client tree} ∧
      budget = (rightPart target).card + deliveryCost tree + traversalWork formula tree := by
  obtain ⟨verdict, entries, receipt, account⟩ := AssayProbeDelivery.maximal_affordable_verdict
    (fun value => (inspect formula value).1) deliveryCost (fun value => (inspect formula value).2)
    session provider client tree budget affordable path maximal
  exact ⟨verdict, inspection_firing_certificate formula
    (ComplementaryAssay.selected (fun value => (inspect formula value).1) session client tree),
      entries, receipt, by simpa only [inspect_work] using account⟩

theorem probed_inspection_observed (formula : Formula Symbols arity)
    (deliveryCost : Tree Symbols arity → Nat)
    (session : Nat) (provider : Providers) (client : Clients) (tree : Tree Symbols arity) (budget : Nat) :
    AssayProbeDelivery.observed (fun value => (inspect formula value).1)
      deliveryCost (fun value => (inspect formula value).2) session provider client (some tree) budget =
      if deliveryCost tree + traversalWork formula tree ≤ budget then
        { (session, verdictOf (evaluate formula tree), client, tree) } else 0 := by
  rw [AssayProbeDelivery.observed_some, inspect_work, inspect_readout]

end Mettapedia.OSLF.Framework.InstrumentObservations
