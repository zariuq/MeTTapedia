import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.AtomicResourceJoinRuntimeBridge
import Mathlib.Data.List.Sort

/-!
# Canonical occurrence-lock order for atomic resource joins

The raw runtime already identifies every endpoint and selected purse
occurrence by its source index.  An enabled candidate therefore determines a
finite duplicate-free resource family.  Sorting that family by source index
gives a canonical acquisition order without changing which occurrences the
event consumes.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed

namespace RawRuntimeStep

/-- Exact source occurrences consumed by a raw event: communication
participants followed by its selected purse occurrences. -/
def consumedIndices (step : RawRuntimeStep) : List Nat :=
  step.participantIndices ++ step.selectedPurses.map RawIndexedPurse.index

/-- Canonical total acquisition order for the exact consumed occurrences. -/
def lockOrder (step : RawRuntimeStep) : List Nat :=
  step.consumedIndices.mergeSort (fun left right => left ≤ right)

end RawRuntimeStep

/-- Every enabled raw candidate consumes distinct source occurrences.  In
particular, no endpoint occurrence is also treated as a purse occurrence, and
the two endpoints of a split event are distinct. -/
theorem runtimeCostCandidate_consumedIndices_nodup
    {config : RawCostConfig} {step : RawRuntimeStep}
    (enabled : step ∈ runtimeCostCandidatesFromConfig config) :
    step.consumedIndices.Nodup := by
  have funding := runtimeCostCandidatesFromConfig_funding_valid enabled
  rcases runtimeCostCandidatesFromConfig_origin enabled with
    ⟨redex, source, _redex_member, source_mem, found, step_member⟩ |
      ⟨recv, send, recvSource, sendSource, _recv_member, _send_member,
        recv_mem, send_mem, recv_found, send_found, step_member⟩
  · simp only [wholeCandidates] at step_member
    obtain ⟨selected, _cover_member, rfl⟩ := List.mem_map.mp step_member
    simpa [RawRuntimeStep.consumedIndices, selectedSourceEntries,
      Function.comp_def] using
      wholePicked_indices_nodup source_mem found funding.selected_from_config
  · unfold splitCandidates at step_member
    split at step_member
    · obtain ⟨selected, _cover_member, rfl⟩ := List.mem_map.mp step_member
      simpa [RawRuntimeStep.consumedIndices, selectedSourceEntries,
        Function.comp_def] using
        splitPicked_indices_nodup recv_mem send_mem recv_found send_found
          funding.selected_from_config
    · contradiction

/-- Sorting changes only the presentation order of the consumed occurrence
family. -/
theorem RawRuntimeStep.lockOrder_perm (step : RawRuntimeStep) :
    step.lockOrder.Perm step.consumedIndices := by
  exact List.mergeSort_perm _ _

/-- An enabled event's canonical lock order remains duplicate-free. -/
theorem RawRuntimeStep.lockOrder_nodup
    {config : RawCostConfig} {step : RawRuntimeStep}
    (enabled : step ∈ runtimeCostCandidatesFromConfig config) :
    step.lockOrder.Nodup := by
  rw [RawRuntimeStep.lockOrder, List.nodup_mergeSort]
  exact runtimeCostCandidate_consumedIndices_nodup enabled

/-- The canonical lock plan is monotonically ordered by source occurrence
index. -/
theorem RawRuntimeStep.lockOrder_pairwise_le (step : RawRuntimeStep) :
    step.lockOrder.Pairwise (fun left right => left ≤ right) := by
  exact List.pairwise_mergeSort'
    (fun left right : Nat => left ≤ right) step.consumedIndices

/-- The canonical lock plan has exactly one entry per consumed occurrence. -/
theorem RawRuntimeStep.lockOrder_length (step : RawRuntimeStep) :
    step.lockOrder.length = step.consumedIndices.length := by
  exact step.lockOrder_perm.length_eq

/-! ## Ordered-wait invariant -/

namespace OrderedOccurrenceLocks

universe v

/-- Abstract state of a finite occurrence-lock protocol.  It contains only
ownership and the next occurrence each transaction is waiting to acquire. -/
structure State (Transaction : Type v) (resourceCount : Nat) where
  owner : Fin resourceCount → Option Transaction
  waiting : Transaction → Option (Fin resourceCount)

/-- A state respects ordered acquisition when every occurrence already held
by a waiting transaction has a smaller index than its next requested one. -/
def WellOrdered {Transaction : Type v} {resourceCount : Nat}
    (state : State Transaction resourceCount) : Prop :=
  ∀ transaction requested held,
    state.waiting transaction = some requested →
      state.owner held = some transaction → held < requested

/-- Transaction `waiting` is blocked on an occurrence owned by `holder`. -/
def WaitsFor {Transaction : Type v} {resourceCount : Nat}
    (state : State Transaction resourceCount)
    (waiting holder : Transaction) : Prop :=
  ∃ resource,
    state.waiting waiting = some resource ∧
      state.owner resource = some holder

/-- Waiting transactions are ranked by their next requested occurrence;
transactions not waiting receive the strict upper sentinel. -/
def waitRank {Transaction : Type v} {resourceCount : Nat}
    (state : State Transaction resourceCount) (transaction : Transaction) : Nat :=
  match state.waiting transaction with
  | some resource => resource.val
  | none => resourceCount

/-- Every wait edge in an ordered state strictly increases the wait rank. -/
theorem waitsFor_rank_lt
    {Transaction : Type v} {resourceCount : Nat}
    {state : State Transaction resourceCount}
    (ordered : WellOrdered state) {waiting holder : Transaction}
    (edge : WaitsFor state waiting holder) :
    waitRank state waiting < waitRank state holder := by
  obtain ⟨resource, waiting_eq, owner_eq⟩ := edge
  unfold waitRank
  rw [waiting_eq]
  cases holder_waiting_eq : state.waiting holder with
  | none =>
      exact resource.isLt
  | some next =>
      exact ordered holder next resource holder_waiting_eq owner_eq

/-- A nonempty chain of waits in an ordered state strictly increases rank. -/
theorem waitsFor_transGen_rank_lt
    {Transaction : Type v} {resourceCount : Nat}
    {state : State Transaction resourceCount}
    (ordered : WellOrdered state) {first last : Transaction}
    (path : Relation.TransGen (WaitsFor state) first last) :
    waitRank state first < waitRank state last := by
  induction path with
  | single edge =>
      exact waitsFor_rank_lt ordered edge
  | tail path edge ih =>
      exact lt_trans ih (waitsFor_rank_lt ordered edge)

/-- Globally ordered occurrence acquisition rules out finite wait cycles. -/
theorem no_wait_cycle
    {Transaction : Type v} {resourceCount : Nat}
    {state : State Transaction resourceCount}
    (ordered : WellOrdered state) (transaction : Transaction) :
    ¬Relation.TransGen (WaitsFor state) transaction transaction := by
  intro cycle
  exact (Nat.lt_irrefl _)
    (waitsFor_transGen_rank_lt ordered cycle)

end OrderedOccurrenceLocks

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed
