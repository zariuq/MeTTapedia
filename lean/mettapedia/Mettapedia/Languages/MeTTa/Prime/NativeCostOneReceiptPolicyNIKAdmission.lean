import Mettapedia.Languages.MeTTa.Prime.NativeCostOneReceiptObservation
import Mettapedia.Languages.MeTTa.Prime.CostTwoPolicyKeyNIKAdmission
import Mettapedia.GSLT.Dynamics.ObservationPolicyFamilyUniversal

/-!
# NIK receipt-key admission for Cost₁ histories

The exact Cost₁ observation factorization retains a chronological list of
proof-relevant wave events and only then computes `WorkSpan`.  This module
turns that strict information loss into a revision-current NIK admission
boundary.

Two dependent policies are declared over retained histories:

* the `WorkSpan` valuation; and
* the chronological list of funded-occurrence receipts.

The `WorkSpan` key realizes the first policy but cannot realize the second:
two valid Prime schedules collide at `WorkSpan` while their receipt orders
differ.  The canonical vector of requested policy answers realizes both and
is the least informative sufficient key by the generic policy-vector theorem.
Retaining the complete history is also sufficient, but is not prescribed as
the runtime representation.

This is a displayed observation capability over Cost₁ execution.  It does
not construct a semantic normalization event, an operational realization, or
a second execution authority.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.NativeCostOneReceiptPolicyNIKAdmission

open Mettapedia.Algebra
open Mettapedia.GSLT.Core
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CostScheduleObservation
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.Languages.MeTTa.Prime.CostTwoCacheReplayBoundary
open Mettapedia.Languages.MeTTa.Prime.CostTwoObservationKeyOrder
open Mettapedia.Languages.MeTTa.Prime.CostTwoPolicyKeyNIKAdmission
open Mettapedia.Languages.MeTTa.Prime.NativeCostOneReceiptObservation
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFamilyFibration
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe uGround

abbrev History (Ground : Type uGround) := List (WaveEvent Ground)

/-- The ordered receipt of every operational wave.  Unlike the schedule's
total receipt bag, this observation retains chronological wave boundaries. -/
def receiptChronology {Ground : Type uGround} (history : History Ground) :
    List (Multiset (SpendEvent Ground (CostName Ground))) :=
  history.map WaveEvent.receipt

inductive ReceiptPolicy where
  | workSpan
  | chronology
  deriving DecidableEq, Repr

/-- The heterogeneous policy family requested from one retained Cost₁
history. -/
def receiptPolicies (Ground : Type uGround) :
    PolicyFamily.{uGround, 0, uGround} (History Ground) where
  Policy := ReceiptPolicy
  Result
    | .workSpan => ULift.{uGround} WorkSpan
    | .chronology => List (Multiset (SpendEvent Ground (CostName Ground)))
  decide
    | .workSpan => fun history => ULift.up (historyWorkSpan history)
    | .chronology => receiptChronology

/-- The subrequest which asks only for the scalar scheduler valuation. -/
def workOnlyPolicies (Ground : Type uGround) :
    PolicyFamily.{uGround, 0, uGround} (History Ground) :=
  (receiptPolicies Ground).reindex (fun _ : Unit => ReceiptPolicy.workSpan)

/-- A WorkSpan key is exactly sufficient for the WorkSpan-only request. -/
theorem workSpan_supports_workOnlyPolicies (Ground : Type uGround) :
    (workOnlyPolicies Ground).SupportsReadout
      (historyWorkSpan : History Ground → WorkSpan) := by
  refine ⟨{
    run := fun _ observed => ULift.up observed
    agrees := ?_ }⟩
  intro policy history
  cases policy
  rfl

/-- Retaining the complete history realizes both declared policies. -/
theorem retainedHistory_supports_receiptPolicies (Ground : Type uGround) :
    (receiptPolicies Ground).SupportsReadout
      (id : History Ground → History Ground) := by
  refine ⟨{
    run := fun
      | .workSpan => fun history => ULift.up (historyWorkSpan history)
      | .chronology => receiptChronology
    agrees := ?_ }⟩
  intro policy history
  cases policy <;> rfl

/-! ## Concrete policy collision on valid schedules -/

namespace Examples

open NativeCostOneReceiptObservation.Examples
open NativeInteractionFibration.Examples

/-- The two concrete schedules with their history type exposed rather than
through the abstract observation-container projection. -/
abbrev forwardEventHistory : History Ground :=
  Schedule.events forwardSchedule

abbrev reverseEventHistory : History Ground :=
  Schedule.events reverseSchedule

theorem two_event_orders_same_workSpan :
    historyWorkSpan forwardEventHistory =
      historyWorkSpan reverseEventHistory := by
  exact NativeCostOneReceiptObservation.Examples.two_orders_same_workSpan

/-- Reversing the two valid singleton waves reverses their chronological
receipt observation. -/
theorem two_orders_distinct_receiptChronologies :
    receiptChronology forwardEventHistory ≠
      receiptChronology reverseEventHistory := by
  intro equalChronologies
  have firstReceipts := congrArg List.head? equalChronologies
  change some NativeInteractionFamilyFibration.Examples.leftSingleton.receipt =
    some NativeCostOneReceiptObservation.Examples.rightSingleton.receipt
      at firstReceipts
  exact singleton_receipts_ne (Option.some.inj firstReceipts)

/-- The WorkSpan key cannot support the full real Cost₁ policy family. -/
theorem workSpan_refuses_receiptPolicies :
    Not ((receiptPolicies Ground).SupportsReadout
      (historyWorkSpan : History Ground → WorkSpan)) := by
  apply (receiptPolicies Ground).not_supportsReadout_of_policy_collision
    historyWorkSpan
    (first := forwardEventHistory) (second := reverseEventHistory)
    two_event_orders_same_workSpan .chronology
  exact two_orders_distinct_receiptChronologies

/-- Retained history strictly refines WorkSpan in the same information order
used by Cost² cache and replay keys. -/
theorem retainedHistory_strictlyRefines_workSpan :
    StrictlyRefines (id : History Ground → History Ground)
      (historyWorkSpan : History Ground → WorkSpan) := by
  constructor
  · exact ExactReplayKey.refines
      (⟨id, fun _ => rfl⟩ : ExactReplayKey
        (id : History Ground → History Ground))
      historyWorkSpan
  · intro workSpanRefinesHistory
    rcases workSpanRefinesHistory with ⟨recover, recovers⟩
    have historiesDifferent : forwardEventHistory ≠ reverseEventHistory := by
      intro historiesEqual
      exact two_orders_distinct_receiptChronologies
        (congrArg receiptChronology historiesEqual)
    apply historiesDifferent
    calc
      forwardEventHistory = recover (historyWorkSpan forwardEventHistory) :=
        by
          have recovered := congrFun recovers forwardEventHistory
          change forwardEventHistory =
            recover (historyWorkSpan forwardEventHistory) at recovered
          exact recovered
      _ = recover (historyWorkSpan reverseEventHistory) :=
        congrArg recover two_event_orders_same_workSpan
      _ = reverseEventHistory := by
        have recovered := congrFun recovers reverseEventHistory
        change reverseEventHistory =
          recover (historyWorkSpan reverseEventHistory) at recovered
        exact recovered.symm

end Examples

/-! ## Revision-current NIK key admission -/

/-- The complete request is policy-only: exact replay remains a separate
capability even though one requested policy is chronology-sensitive. -/
def receiptRequest (Ground : Type uGround) :
    PolicyRequest.{uGround, 0, uGround} (History Ground) where
  Policy := ReceiptPolicy
  Value
    | .workSpan => ULift.{uGround} WorkSpan
    | .chronology => List (Multiset (SpendEvent Ground (CostName Ground)))
  observe
    | .workSpan => fun history => ULift.up (historyWorkSpan history)
    | .chronology => receiptChronology
  requiresExactReplay := False

/-- The smaller request asks only for WorkSpan. -/
def workOnlyRequest (Ground : Type uGround) : PolicyRequest (History Ground) :=
  singlePolicyRequest
    (historyWorkSpan : History Ground → WorkSpan) False

/-- Executable WorkSpan admission for the WorkSpan-only request. -/
def workSpanAdmission
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (Ground : Type uGround) :
    PolicyKeyAdmission dependencies revision (workOnlyRequest Ground)
      (historyWorkSpan : History Ground → WorkSpan) where
  realize := fun _ =>
    { run := id
      agrees := by funext _; rfl }
  replay := fun impossible => False.elim impossible

/-- The canonical policy vector is an executable admission for the full
request and retains no distinction invisible to every requested policy. -/
def canonicalReceiptAdmission
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (Ground : Type uGround) :
    PolicyKeyAdmission dependencies revision (receiptRequest Ground)
      (policyVectorKey (receiptRequest Ground)) :=
  policyVectorAdmission dependencies revision (receiptRequest Ground) (by
    simp [receiptRequest])

/-- Retaining the exact history also admits the full policy family. -/
def retainedHistoryAdmission
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (Ground : Type uGround) :
    PolicyKeyAdmission dependencies revision (receiptRequest Ground)
      (id : History Ground → History Ground) :=
  identityKeyAdmission dependencies revision (receiptRequest Ground)

/-- The real schedule collision prevents any WorkSpan-key admission for the
chronology-sensitive request. -/
theorem no_workSpanAdmission_for_receiptRequest
    (dependencies : DependencySystem) (revision : dependencies.Revision) :
    ¬ Nonempty
      (PolicyKeyAdmission dependencies revision
        (receiptRequest NativeInteractionFibration.Examples.Ground)
        (historyWorkSpan :
          History NativeInteractionFibration.Examples.Ground → WorkSpan)) := by
  rintro ⟨admission⟩
  let realization := admission.realize ReceiptPolicy.chronology
  have forwardExact :
      realization.run
          (historyWorkSpan Examples.forwardEventHistory) =
        receiptChronology Examples.forwardEventHistory := by
    simpa [receiptRequest] using
      realization.run_encode Examples.forwardEventHistory
  have reverseExact :
      realization.run
          (historyWorkSpan Examples.reverseEventHistory) =
        receiptChronology Examples.reverseEventHistory := by
    simpa [receiptRequest] using
      realization.run_encode Examples.reverseEventHistory
  have runEqual :
      realization.run
          (historyWorkSpan Examples.forwardEventHistory) =
        realization.run
          (historyWorkSpan Examples.reverseEventHistory) :=
    congrArg realization.run Examples.two_event_orders_same_workSpan
  apply Examples.two_orders_distinct_receiptChronologies
  exact forwardExact.symm.trans (runEqual.trans reverseExact)

/-- Request scope determines admissibility: WorkSpan is valid for its own
consumer, invalid for the larger receipt request, while the canonical policy
vector and retained history both realize the larger request. -/
theorem request_scoped_key_boundary
    (dependencies : DependencySystem) (revision : dependencies.Revision) :
    Nonempty
        (PolicyKeyAdmission dependencies revision
          (workOnlyRequest NativeInteractionFibration.Examples.Ground)
          (historyWorkSpan :
            History NativeInteractionFibration.Examples.Ground → WorkSpan)) ∧
      ¬ Nonempty
        (PolicyKeyAdmission dependencies revision
          (receiptRequest NativeInteractionFibration.Examples.Ground)
          (historyWorkSpan :
            History NativeInteractionFibration.Examples.Ground → WorkSpan)) ∧
      Nonempty
        (PolicyKeyAdmission dependencies revision
          (receiptRequest NativeInteractionFibration.Examples.Ground)
          (policyVectorKey
            (receiptRequest NativeInteractionFibration.Examples.Ground))) ∧
      Nonempty
        (PolicyKeyAdmission dependencies revision
          (receiptRequest NativeInteractionFibration.Examples.Ground)
          (id : History NativeInteractionFibration.Examples.Ground →
            History NativeInteractionFibration.Examples.Ground)) :=
  ⟨⟨workSpanAdmission dependencies revision _⟩,
    no_workSpanAdmission_for_receiptRequest dependencies revision,
    ⟨canonicalReceiptAdmission dependencies revision _⟩,
    ⟨retainedHistoryAdmission dependencies revision _⟩⟩

/-! ## Current activation and stale fallback -/

namespace RevisionCanary

open NativeCostOneReceiptObservation.Examples
open NativeInteractionFibration.Examples

def dependencies : DependencySystem where
  Revision := Bool
  Dependency := Unit
  Value := Bool
  read revision _ := revision

def admission := canonicalReceiptAdmission dependencies false Ground

def current : admission.Active false :=
  admission.activate (dependencies.sameDependencies_refl false)

def prepared : admission.PreparedState :=
  admission.prepare forwardHistory

def chronologyPolicy : (receiptRequest Ground).Policy := .chronology

/-- Current execution reads the exact chronology from the retained canonical
policy vector without an interior checker. -/
theorem current_chronology_is_exact :
    current.runPrepared prepared chronologyPolicy =
      receiptChronology forwardHistory :=
  current.runPrepared_eq prepared chronologyPolicy

theorem relevant_change_is_stale : admission.StaleAt true := by
  intro sameDependencies
  have impossible := sameDependencies ()
  simp [dependencies] at impossible

/-- Staleness disables the derived key runner and preserves the complete
history for ordinary fallback. -/
theorem stale_refuses_activation_and_preserves_history :
    (¬ admission.Active true) ∧ prepared.fallback = forwardHistory :=
  ⟨admission.stale_prevents_activation relevant_change_is_stale,
    admission.stale_preserves_fallback relevant_change_is_stale prepared⟩

end RevisionCanary

#print axioms workSpan_supports_workOnlyPolicies
#print axioms retainedHistory_supports_receiptPolicies
#print axioms Examples.two_orders_distinct_receiptChronologies
#print axioms Examples.workSpan_refuses_receiptPolicies
#print axioms Examples.retainedHistory_strictlyRefines_workSpan
#print axioms no_workSpanAdmission_for_receiptRequest
#print axioms request_scoped_key_boundary
#print axioms RevisionCanary.current_chronology_is_exact
#print axioms RevisionCanary.stale_refuses_activation_and_preserves_history

end Mettapedia.Languages.MeTTa.Prime.NativeCostOneReceiptPolicyNIKAdmission
