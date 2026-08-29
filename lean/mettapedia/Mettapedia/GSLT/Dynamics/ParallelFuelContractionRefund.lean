import Mettapedia.GSLT.Core.ObservationResidualDisposition
import Mettapedia.GSLT.Dynamics.ParallelFuelLease

/-!
# Refunding a contracted branch's unspent fuel

Finite-demand observation may deliberately contract an owned residual search.
When that search owns an additive work lease, contraction returns its entire
unspent balance to the parent.  The refund is an ordinary conservative
transfer; it does not prove that execution closed and it grants no authority
to commit effects or prune shared state.

The receipt stored by `ResidualDisposition.contracted` is deliberately tiny.
It contains only an erased admission proof for one exact refund transfer, and
is a subsingleton.  A runtime may retain the stop reason and resulting balances
without retaining the worker's execution history.  Rich audit histories remain
an optional, separate instrument.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ParallelFuelContractionRefund

open Mettapedia.GSLT.Core.ObservationResidualDisposition
open Mettapedia.GSLT.Core.ObservationScopeCompletion
open Mettapedia.GSLT.Dynamics.ParallelFuelLease

universe uOwner uOccurrence uResidual uRevision uCoverage uBound uReceipt
  uFault

noncomputable section

/-! ## A compact refund witness -/

/-- A contraction refund carries no trace.  Its only field is an erased proof
that the exact full-balance transfer was admitted. -/
structure RefundToken {Owner : Type uOwner} (ledger : Ledger Owner)
    (child parent : Owner) (distinct : child ≠ parent) : Type where
  certified : Transfer.Receipt
    (refundTransfer ledger child parent distinct) ledger

namespace RefundToken

variable {Owner : Type uOwner} {ledger : Ledger Owner}
  {child parent : Owner} {distinct : child ≠ parent}

/-- Valid ledgers always provide a compact full-refund token. -/
def ofNonnegative (valid : ledger.Nonnegative) :
    RefundToken ledger child parent distinct where
  certified := refundReceipt ledger valid child parent distinct

/-- The ledger after the token's exact transfer.  It is independent of the
proof term stored in the token. -/
def after (_token : RefundToken ledger child parent distinct) : Ledger Owner :=
  (refundTransfer ledger child parent distinct).apply ledger

/-- The compact token cannot distinguish or reconstruct execution histories. -/
instance : Subsingleton (RefundToken ledger child parent distinct) where
  allEq left right := by
    cases left
    cases right
    rfl

@[simp]
theorem total_after (token : RefundToken ledger child parent distinct) :
    token.after.total = ledger.total := by
  exact Transfer.total_apply
    (refundTransfer ledger child parent distinct) ledger

@[simp]
theorem child_balance_after
    (token : RefundToken ledger child parent distinct) :
    token.after.balances child = 0 := by
  change
    ((refundTransfer ledger child parent distinct).apply ledger).balances child =
      0
  simpa [refundTransfer] using
    (Transfer.balance_at_source
      (refundTransfer ledger child parent distinct) ledger)

@[simp]
theorem parent_balance_after
    (token : RefundToken ledger child parent distinct) :
    token.after.balances parent =
      ledger.balances parent + ledger.balances child := by
  change
    ((refundTransfer ledger child parent distinct).apply ledger).balances parent =
      ledger.balances parent + ledger.balances child
  simpa [refundTransfer] using
    (Transfer.balance_at_target
      (refundTransfer ledger child parent distinct) ledger)

end RefundToken

/-! ## Observation contraction with refund -/

variable
    {Occurrence : Type uOccurrence}
    {Residual : Type uResidual} {Revision : Type uRevision}
    {Coverage : Type uCoverage} {Bound : Type uBound}
    {Receipt : Type uReceipt} {Fault : Type uFault}
    {CaptureAdmitted : Residual → Revision → Prop}
    {scope : ScopedObservation Occurrence Residual Revision Coverage Bound
      Receipt Fault CaptureAdmitted}
    {Owner : Type uOwner} {ledger : Ledger Owner}
    {child parent : Owner} {distinct : child ≠ parent}

/-- Satisfying a finite observation demand may contract the owned residual and
attach the exact refund token.  Neither premise nor result claims execution
closure. -/
def contractWithRefund
    (valid : ledger.Nonnegative)
    (satisfied : scope.DemandSatisfied)
    (notExported : scope.observation.resumable = none) :
    ResidualDisposition scope
      (RefundToken ledger child parent distinct) :=
  .contracted satisfied (RefundToken.ofNonnegative valid) notExported

@[simp]
theorem contractWithRefund_isContracted
    (valid : ledger.Nonnegative)
    (satisfied : scope.DemandSatisfied)
    (notExported : scope.observation.resumable = none) :
    (contractWithRefund (scope := scope) (child := child) (parent := parent)
      (distinct := distinct) valid satisfied notExported).IsContracted :=
  trivial

/-- The combined construction both records contraction and preserves the one
global additive total. -/
theorem contractWithRefund_contracts_and_conserves
    (valid : ledger.Nonnegative)
    (satisfied : scope.DemandSatisfied)
    (notExported : scope.observation.resumable = none) :
    (contractWithRefund (scope := scope) (child := child) (parent := parent)
        (distinct := distinct) valid satisfied notExported).IsContracted ∧
      (RefundToken.ofNonnegative (child := child) (parent := parent)
        (distinct := distinct) valid).after.total = ledger.total :=
  ⟨trivial, RefundToken.total_after _⟩

/-! ## Positive and negative controls -/

namespace Canary

namespace Fuel

open Mettapedia.GSLT.Dynamics.ParallelFuelLease.Canary

def token : RefundToken afterSpend
    ParallelFuelLease.Canary.Owner.worker
    ParallelFuelLease.Canary.Owner.root (by decide) :=
  .ofNonnegative afterSpendNonnegative

theorem exact_refund :
    token.after.balances .worker = 0 ∧
      token.after.balances .root = 7 ∧
      token.after.total = afterSpend.total := by
  constructor
  · exact token.child_balance_after
  · constructor
    · change ParallelFuelLease.Canary.final.balances .root = 7
      exact ParallelFuelLease.Canary.grant_spend_refund_exact.1
    · exact token.total_after

end Fuel

open Mettapedia.GSLT.Core.ObservationResidualDisposition.Canary

/-- The existing first-result scope contracts with the compact fuel refund. -/
def firstContractedWithRefund :
    ResidualDisposition firstUncapturedAfterOne
      (RefundToken ParallelFuelLease.Canary.afterSpend
        ParallelFuelLease.Canary.Owner.worker
        ParallelFuelLease.Canary.Owner.root (by decide)) :=
  contractWithRefund
    ParallelFuelLease.Canary.afterSpendNonnegative
    first_uncaptured_satisfies_demand
    first_uncaptured_exports_no_residual

theorem contraction_refunds_without_claiming_closure :
    firstContractedWithRefund.IsContracted ∧
      ¬ firstUncapturedAfterOne.ExecutionClosed :=
  ⟨trivial, first_uncaptured_is_not_execution_closed⟩

/-- Whole-bag observation still cannot use contraction as an early-stop and
refund shortcut. -/
theorem complete_bag_cannot_contract_with_refund
    (disposition : ResidualDisposition
      Mettapedia.GSLT.Core.ObservationScopeCompletion.Canary.completeBagAfterOne
      (RefundToken ParallelFuelLease.Canary.afterSpend
        ParallelFuelLease.Canary.Owner.worker
        ParallelFuelLease.Canary.Owner.root (by decide))) :
    ¬ disposition.IsContracted :=
  disposition.completeBag_not_isContracted rfl

end Canary

/-! ## Axiom audit -/

#print axioms RefundToken.total_after
#print axioms RefundToken.child_balance_after
#print axioms RefundToken.parent_balance_after
#print axioms contractWithRefund_isContracted
#print axioms contractWithRefund_contracts_and_conserves
#print axioms Canary.Fuel.exact_refund
#print axioms Canary.contraction_refunds_without_claiming_closure
#print axioms Canary.complete_bag_cannot_contract_with_refund

end


end Mettapedia.GSLT.Dynamics.ParallelFuelContractionRefund
