import Mettapedia.GSLT.Core.ResourceAwareControl
import Mettapedia.GSLT.Dynamics.EventValuation

/-!
# From two-occurrence wave certificates to parallel revision authority

`CertifiedBatch` states whole-batch permutation invariance, while the generic
parallel backend interface consumes pairwise revision squares.  This module
connects the two abstractions for deterministic action semantics.

A certified two-occurrence batch supplies an observer-relative commuting
square.  Exact batch certificates can therefore define a conservative
`ParallelBackend`: it admits precisely the pairs for which such a certificate
exists at the source world.  The bridge supplies semantic authority only; an
executable backend still needs its independently replayable admission checker
and physical execution receipt.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.CertifiedBatchParallelBridge

open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ResourceAwareControl
open Mettapedia.GSLT.Dynamics.EventValuation
open Mettapedia.GSLT.Dynamics.QueryRevision

universe uItem uGuard uCandidateView uState uStateView uAccount

/-- Deterministic actions as a queryable revision theory with one declared
state observer. -/
def deterministicTheory
    {Item : Type uItem} {State : Type uState} {StateView : Type uStateView}
    (step : State → Item → State) (observe : State → StateView) : Theory where
  World := State
  Revision := Item
  Query := Unit
  Observation := StateView
  Step item source target := target = step source item
  query state _request := observe state

/-- The matching ordered-batch semantics. -/
def deterministicSemantics
    {Item : Type uItem} {State : Type uState} {StateView : Type uStateView}
    (step : State → Item → State) (observe : State → StateView) :
    ExecutionSemantics Item State StateView where
  run source batch target :=
    target = List.foldl step source batch
  observe := observe

/-- A certified two-occurrence batch supplies the exact query-relative square
expected by the generic parallel-event theory. -/
theorem certifiedPair_queryCoexecutible
    {Item : Type uItem} {Guard : Type uGuard}
    {CandidateView : Type uCandidateView}
    {State : Type uState} {StateView : Type uStateView}
    {Account : Type uAccount} [AddMonoid Account]
    {contract : Contract Item Guard CandidateView}
    {step : State → Item → State} {observe : State → StateView}
    {source referenceTarget : State}
    {demand : Item → Account} {inventory : Account}
    {first second : Item}
    (certified :
      CertifiedBatch contract (deterministicSemantics step observe)
        source referenceTarget Account demand inventory [first, second]) :
    (deterministicTheory step observe).QueryCoexecutible
      first second source := by
  obtain ⟨swappedTarget, swappedRun, sameObservation⟩ :=
    certified.executionSerializable.2 [second, first]
      (List.Perm.swap first second [])
  have referenceRun := certified.executionSerializable.1
  have observedOrdersAgree :
      observe (step (step source first) second) =
        observe (step (step source second) first) := by
    calc
      observe (step (step source first) second) =
          observe referenceTarget := by
        symm
        simpa [deterministicSemantics] using congrArg observe referenceRun
      _ = observe swappedTarget := sameObservation.symm
      _ = observe (step (step source second) first) := by
        simpa [deterministicSemantics] using congrArg observe swappedRun
  refine ⟨{
    afterFirst := step source first
    afterSecond := step source second
    firstThenSecond := step (step source first) second
    secondThenFirst := step (step source second) first
    firstFromSource := rfl
    secondFromSource := rfl
    secondAfterFirst := rfl
    firstAfterSecond := rfl
    observationAgrees := ?_ }⟩
  funext request
  cases request
  exact observedOrdersAgree

/-- Exact two-occurrence wave admission at one source state. -/
def PairAdmitted
    {Item : Type uItem} {Guard : Type uGuard}
    {CandidateView : Type uCandidateView}
    {State : Type uState} {StateView : Type uStateView}
    (contract : Contract Item Guard CandidateView)
    (step : State → Item → State) (observe : State → StateView)
    (Account : Type uAccount) [AddMonoid Account]
    (demand : Item → Account) (inventory : State → Account)
    (first second : Item) (source : State) : Prop :=
  ∃ referenceTarget,
    Nonempty
      (CertifiedBatch contract (deterministicSemantics step observe)
        source referenceTarget Account demand (inventory source)
        [first, second])

/-- A conservative semantic backend admitting exactly certified pairs.  The
event-count valuation is total; the substantive permission is the retained
wave certificate and its observer-relative square. -/
def certifiedPairBackend
    {Item : Type uItem} {Guard : Type uGuard}
    {CandidateView : Type uCandidateView}
    {State : Type uState} {StateView : Type uStateView}
    (contract : Contract Item Guard CandidateView)
    (step : State → Item → State) (observe : State → StateView)
    (Account : Type uAccount) [AddMonoid Account]
    (demand : Item → Account) (inventory : State → Account) :
    ParallelBackend (deterministicTheory step observe) where
  valuation := eventCount (deterministicTheory step observe)
  Admits := PairAdmitted contract step observe Account demand inventory
  sound := by
    intro first second source admitted
    obtain ⟨referenceTarget, ⟨certified⟩⟩ := admitted
    exact ⟨certifiedPair_queryCoexecutible certified,
      additive_compatible (fun _revision => 1) first second⟩

/-- If the selected query profile has no commuting square, no exact
two-occurrence wave certificate can authorize that pair. -/
theorem no_pair_admission_of_no_query_square
    {Item : Type uItem} {Guard : Type uGuard}
    {CandidateView : Type uCandidateView}
    {State : Type uState} {StateView : Type uStateView}
    {Account : Type uAccount} [AddMonoid Account]
    {contract : Contract Item Guard CandidateView}
    {step : State → Item → State} {observe : State → StateView}
    {demand : Item → Account} {inventory : State → Account}
    {first second : Item} {source : State}
    (noSquare :
      ¬ (deterministicTheory step observe).QueryCoexecutible
        first second source) :
    ¬ PairAdmitted contract step observe Account demand inventory
      first second source := by
  rintro ⟨referenceTarget, ⟨certified⟩⟩
  exact noSquare (certifiedPair_queryCoexecutible certified)

#print axioms certifiedPair_queryCoexecutible
#print axioms no_pair_admission_of_no_query_square

end Mettapedia.GSLT.Dynamics.CertifiedBatchParallelBridge
