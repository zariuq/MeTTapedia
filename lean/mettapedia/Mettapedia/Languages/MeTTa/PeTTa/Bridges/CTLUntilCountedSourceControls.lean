import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCountedSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedCountControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilScopedRoundControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundAdmissionControls

/-!
The actual size/collapse fixture obtains its numeric prefix from initial
source evidence and usable capacity. Its child completion and copy receipt
are conclusions. An arbitrary older caller tail is retained unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCountedSource.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS.Destination
open ClosedOnceQueryFrame (FreshFor placed)
open NamedGuardedCandidateBatch (State)
open CTLUntilScopedRound.Controls (query query_template query_legs initial_decoded initial_known initial_next_frontier)
open CTLUntilRoundAdmission.Controls (fixture_guard)
open GuardedCountSource.Controls (base sourceRun capacity allocationStopped aliasOutput)
open ScopedQuerySource.Controls (call number)

def withTail (older : List Goal) : GuardedCountSource.Input Unit :=
  {base with caller := {base.caller with goals := older}}

theorem source_unchanged (older : List Goal) : (withTail older).source = base.source := rfl

/-- The principal solution is obtained from the initial equations. This
entry contains no child-run or collector-copy result. -/
theorem entry_with_tail (older : List Goal) :
    ∃ entry : Entry FlatQueryRowCodec.integers 10 20 0 query (withTail older),
      entry.initialKnown = [] ∧ entry.initialFrontier = [9] ∧
      entry.word.length = 8 ∧ entry.added = [1] ∧
      read entry.principal (withTail older).destination = .var "answer" := by
  obtain ⟨principal, resolved, readings⟩ := CTLUntilScopedRound.Controls.caller_principal
  let entry : Entry FlatQueryRowCodec.integers 10 20 0 query (withTail older) := {
    template := query_template.symm
    legs := query_legs.symm
    principal, resolved
    formula := readings.1
    holds := readings.2.1
    current := readings.2.2.1
    nextRound := readings.2.2.2
    nextFresh := CTLUntilScopedRound.Controls.next_fresh
    priorFresh := CTLUntilScopedRound.Controls.prior_fresh
    temporaryFresh := by
      change FreshFor query.names.temporary base.caller.bindings
      decide +kernel
    distinct := by decide +kernel
    profile := fixture_guard
    decoded := initial_decoded
    frontAtoms := CTLUntilMixedStore.Controls.atoms
    graphAtoms := CTLUntilMixedStore.Controls.atoms
    factAtoms := CTLUntilMixedStore.Controls.atoms
    fronts := CTLUntilMixedStore.Controls.rows
    graph := CTLUntilMixedStore.Controls.rows
    facts := CTLUntilMixedStore.Controls.rows
    frontRead := rfl
    frontDecode := CTLUntilMixedStore.Controls.raw_rows_decode_without_loss
    graphRead := rfl
    graphDecode := CTLUntilMixedStore.Controls.raw_rows_decode_without_loss
    factRead := rfl
    factDecode := CTLUntilMixedStore.Controls.raw_rows_decode_without_loss
    initialKnown := []
    initialFrontier := [9]
    knownRead := initial_known
    frontierRead := initial_next_frontier }
  refine ⟨entry, rfl, rfl, ?_, ?_, ?_⟩
  · change (Mettapedia.Machines.CTLUntilCandidateBag.candidates
      (CTLUntilMixedStore.graphView CTLUntilMixedStore.Controls.rows)
      (CTLUntilMixedStore.satisfactionView (20 : Int) CTLUntilMixedStore.Controls.rows)
      (CTLUntilMixedStore.Controls.rows.filterMap (CTLUntilMixedStore.frontSelect (10 : Int) 0))).length = 8
    decide +kernel
  · change Mettapedia.Machines.CTLUntilCandidateBag.fresh
      (Mettapedia.Machines.CTLUntilCandidateBag.candidates
        (CTLUntilMixedStore.graphView CTLUntilMixedStore.Controls.rows)
        (CTLUntilMixedStore.satisfactionView (20 : Int) CTLUntilMixedStore.Controls.rows)
        (CTLUntilMixedStore.Controls.rows.filterMap (CTLUntilMixedStore.frontSelect (10 : Int) 0)))
      (∅ : Finset Nat) = [1]
    decide +kernel
  · exact ClosedOnceQueryFrame.fresh_read (withTail older).caller.bindings "answer" principal
      (by
        change FreshFor "answer" base.caller.bindings
        decide +kernel) resolved

theorem base_entry : Nonempty (Entry FlatQueryRowCodec.integers 10 20 0 query base) := by
  obtain ⟨entry, _properties⟩ := entry_with_tail []
  exact ⟨entry⟩

/-- One new node is counted by the authored source, with the old caller
tail still pending. No completed child or successful copy is a premise. -/
theorem counted_prefix_with_tail (older : List Goal) :
    let input := withTail older
    ∃ (after : State Unit) (next : Allocator),
      CTLUntilRoundPublication.known FlatQueryRowCodec.integers 10 query after.world.state = some [1] ∧
      CTLUntilRoundPublication.frontier FlatQueryRowCodec.integers 10 0 query after.world.state = some [9, 1] ∧
      next.usableCount + 8 = input.state.allocator.usableCount ∧
      (ScopedQuerySource.machine .relational input.program).run (2 + input.childExecution.budget + 1 + 3) input.before =
        ([], .exhausted (placed next after.world input.state.scope input.state.parents
          (GuardedCountReturn.counted input.caller input.slot input.destination 1)
          input.context (input.origins ++ [0]) input.pending)) := by
  dsimp only
  obtain ⟨entry, knownShape, frontierShape, wordLength, added, unbound⟩ := entry_with_tail older
  have available : (withTail older).state.allocator.usableCount = 32 := by
    change base.state.allocator.usableCount = 32
    decide +kernel
  have reserve : entry.word.length ≤ (withTail older).state.allocator.usableCount := by omega
  obtain ⟨after, next, known, frontier, charged, returned⟩ :=
    counted_prefix entry (by decide) reserve "answer" unbound
  refine ⟨after, next, ?_, ?_, ?_, ?_⟩
  · simpa only [knownShape, added, List.nil_append] using known
  · simpa only [frontierShape, added, List.cons_append, List.nil_append] using frontier
  · simpa only [wordLength] using charged
  · simpa only [added, List.length_singleton] using returned

theorem base_counted_prefix :
    ∃ (after : State Unit) (next : Allocator),
      CTLUntilRoundPublication.known FlatQueryRowCodec.integers 10 query after.world.state = some [1] ∧
      CTLUntilRoundPublication.frontier FlatQueryRowCodec.integers 10 0 query after.world.state = some [9, 1] ∧
      (ScopedQuerySource.machine .relational base.program).run (2 + base.childExecution.budget + 1 + 3) base.before =
        ([], .exhausted (placed next after.world base.state.scope base.state.parents
          (GuardedCountReturn.counted base.caller base.slot base.destination 1)
          base.context (base.origins ++ [0]) base.pending)) := by
  obtain ⟨after, next, known, frontier, _charged, returned⟩ := counted_prefix_with_tail []
  exact ⟨after, next, known, frontier, returned⟩

#guard base.source == call "size-atom" [call "collapse"
  [ScopedNestedQueryExecution.source query.legs query.template.source]]
#guard (sourceRun base).1.map CollectedAnswer.value == [number 1]
#guard (sourceRun aliasOutput).1.map CollectedAnswer.value == [number 1]
#guard allocationStopped (capacity 7)
#guard (sourceRun (capacity 8)).1.map CollectedAnswer.value == [number 1]

def older : List Goal := [.evaluate (call "quote" [.symbol "retained"]) (.var "tail-result")]
#guard (sourceRun (withTail older)).1.map CollectedAnswer.value == [number 1]
#guard (sourceRun (withTail older)).1.head?.map
  (fun packet => packet.bindings.contains (.symbol "retained", .var "tail-result")) == some true

#print axioms entry_with_tail
#print axioms counted_prefix_with_tail
#print axioms base_counted_prefix
#print axioms CTLUntilCountedSource.counted_prefix

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCountedSource.Controls
