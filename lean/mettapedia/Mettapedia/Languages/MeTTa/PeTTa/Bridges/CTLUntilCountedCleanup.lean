import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedRemovalQuery
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CountedSourceEntry
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryCopyCapacity
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedCountReturn

/-!
# Counted current-frontier cleanup through actual source execution

The authored size/collapse entry creates its own child result slot. The live
query captures every current frontier occurrence, then removes each payload
against the evolving store. Actual Boolean packets are copied and counted;
the original caller continuation and all unrelated stored rows are retained.
The capacity premise is on the initial usable identities, not a successful
future copy receipt. Repeated producers remain repeated count contributions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCountedCleanup

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open NamedGuardedCandidateBatch (State)
open FlatQueryRowCodec (Codec)
open CountedSourceEntry (Input)
open ClosedOnceQueryFrame (FreshFor placed)
open CTLUntilMixedStore (Row render decodeRows frontSelect)
open CTLUntilSourceRows (number)

variable {Context Label : Type} [DecidableEq Label]

def body (handle : NamedSpaces.Handle) (formulaName roundName nodeName : String) : Atom :=
  let pattern := CTLUntilScopedCapture.frontierCode formulaName roundName nodeName
  ScopedMatchPreparation.source handle pattern (ScopedRemovalSource.source handle pattern)

structure Entry (codec : Codec Label) (label : Label) (round : Nat)
    (input : Input Context) (handle : NamedSpaces.Handle) (formulaName roundName nodeName : String) where
  written : input.body = body handle formulaName roundName nodeName
  principal : Environment
  resolved : resolve input.caller.bindings = some principal
  formula : read principal (.var formulaName) = codec.encode label
  current : read principal (.var roundName) = number round
  nodeFresh : FreshFor nodeName input.caller.bindings
  atoms : List Atom
  rows : List (Row Label)
  snapshot : input.state.world.state.read handle = some atoms
  decoded : decodeRows codec atoms = some rows

def childExecution (input : Input Context) (handle : NamedSpaces.Handle) (formulaName roundName nodeName : String) :
    ScopedNestedQueryExecution.Execution Context :=
  let pattern := CTLUntilScopedCapture.frontierCode formulaName roundName nodeName
  ScopedNestedQueryExecution.run input.program
    (ScopedRemovalExecution.leaf input.program input.childName handle pattern Context)
    [(handle, pattern)] input.childCaller input.childState input.context input.origins []

omit [DecidableEq Label] in
private theorem node_in_body (handle : NamedSpaces.Handle) (formulaName roundName nodeName : String) :
    nodeName ∈ (encode (body handle formulaName roundName nodeName)).freeVars := by
  rw [body, ScopedMatchPreparation.source, CapturedPatternSupport.mem_expression_names]
  refine ⟨CTLUntilScopedCapture.frontierCode formulaName roundName nodeName, by simp, ?_⟩
  rw [CTLUntilScopedCapture.frontierCode, CapturedPatternSupport.mem_expression_names]
  exact ⟨.var nodeName, by simp, by simp [encode, Mettapedia.Logic.LP.Term.freeVars]⟩

omit [DecidableEq Label] in
theorem child_name_apart (input : Input Context) (handle : NamedSpaces.Handle) (formulaName roundName nodeName : String)
    (written : input.body = body handle formulaName roundName nodeName) : input.childName ≠ nodeName := by
  intro same
  apply childName_fresh input.preparing input.boundary
  apply Finset.mem_union_left
  change input.childName ∈ input.preparing.support
  rw [same]
  apply GuardedInsertionPairSource.goal_atom_support input.preparing input.collection nodeName
  · simp [Input.preparing, Goal.atoms]
  · rw [Input.collection, CapturedPatternSupport.mem_expression_names]
    refine ⟨input.body, by simp, ?_⟩
    rw [written]
    exact node_in_body handle formulaName roundName nodeName

omit [DecidableEq Label] in
private theorem removal_preserves_ready (program : SpaceSemantics.Program) (result : String)
    (handle : NamedSpaces.Handle) (pattern : Atom) :
    ScopedNestedQueryExecution.Preserves GuardedQueryPackets.CollectedReady
      (ScopedRemovalExecution.leaf program result handle pattern Context).execute := by
  intro caller state context origins pending after valid completed
  have kept := ScopedRemovalExecution.completed_preserves_allocator program result handle pattern
    caller state context origins pending after completed
  intro packet member
  rw [kept.2] at member
  rcases List.mem_append.mp member with old | added
  · exact valid packet old
  · have same : packet = ScopedRemovalExecution.packet result handle pattern caller origins := List.mem_singleton.mp added
    subst packet
    exact ScopedRemovalExecution.packet_value result handle pattern caller origins

omit [DecidableEq Label] in
theorem completed_packets (input : Input Context) (handle : NamedSpaces.Handle) (formulaName roundName nodeName : String)
    (after : State Context) (completed : (childExecution input handle formulaName roundName nodeName).stop = .complete after) :
    GuardedQueryPackets.CollectedReady after := by
  apply ScopedNestedQueryExecution.run_preserves input.program
    (ScopedRemovalExecution.leaf input.program input.childName handle
      (CTLUntilScopedCapture.frontierCode formulaName roundName nodeName) Context)
    GuardedQueryPackets.CollectedReady
    (removal_preserves_ready input.program input.childName handle _) [(handle, _)]
    input.childCaller input.childState input.context input.origins [] after
  · intro packet member
    cases member
  · exact completed

theorem child_completed {codec : Codec Label} {label : Label} {round : Nat} {input : Input Context}
    {handle : NamedSpaces.Handle} {formulaName roundName nodeName : String}
    (entry : Entry codec label round input handle formulaName roundName nodeName) :
    ∃ after : State Context,
      (childExecution input handle formulaName roundName nodeName).stop = .complete after ∧
      after.world.state.read handle = some ((CTLUntilCleanup.remaining label round entry.rows).map (render codec)) ∧
      decodeRows codec ((CTLUntilCleanup.remaining label round entry.rows).map (render codec)) =
        some (CTLUntilCleanup.remaining label round entry.rows) ∧
      after.scope.collected.length = (entry.rows.filterMap (frontSelect label round)).length ∧
      (∀ other, other ≠ handle → after.world.state.read other = input.state.world.state.read other) ∧
      after.world.state.cells = input.state.world.state.cells ∧ after.allocator = input.state.allocator ∧
      after.scope.caller = some input.savedCaller ∧
      after.parents = {input.state.scope with frontier := input.pending} :: input.state.parents ∧
      (childExecution input handle formulaName roundName nodeName).events = [] := by
  obtain ⟨after, completed, reading, decoded, count, others, cells, allocator, saved, parents, silent⟩ :=
    ScopedRemovalQuery.frontier_complete codec label round input.program input.childName formulaName roundName nodeName handle
      input.childCaller input.childState input.context input.origins [] entry.principal entry.atoms entry.rows
      entry.resolved entry.formula entry.current entry.nodeFresh (CountedSourceEntry.child_result_fresh input)
      (child_name_apart input handle formulaName roundName nodeName entry.written) rfl rfl entry.snapshot entry.decoded
  refine ⟨after, completed, reading, decoded, ?_, others, cells, allocator, saved, parents, silent rfl⟩
  simpa only [Input.childState, List.length_nil, Nat.zero_add] using count

omit [DecidableEq Label] in
theorem child_prefix (input : Input Context) (handle : NamedSpaces.Handle) (formulaName roundName nodeName : String)
    (written : input.body = body handle formulaName roundName nodeName) :
    (ScopedQuerySource.machine .relational input.program).run
      (2 + (childExecution input handle formulaName roundName nodeName).budget) input.before =
      (childExecution input handle formulaName roundName nodeName).observation [] := by
  have child := ScopedNestedQueryExecution.run_exact input.program
    (ScopedRemovalExecution.leaf input.program input.childName handle
      (CTLUntilScopedCapture.frontierCode formulaName roundName nodeName) Context)
    [(handle, CTLUntilScopedCapture.frontierCode formulaName roundName nodeName)]
    input.childCaller input.childState input.context input.origins []
  change (ScopedQuerySource.machine .relational input.program).run
    (childExecution input handle formulaName roundName nodeName).budget
    (ScopedMatchEntry.entrance (body handle formulaName roundName nodeName) (.var input.childName)
      input.childCaller input.childState input.context input.origins []) = _ at child
  rw [← written] at child
  have joined := (ScopedQuerySource.machine .relational input.program).established_and_pending
    2 (childExecution input handle formulaName roundName nodeName).budget _ _ [] (CountedSourceEntry.entry_prefix input)
  change (ScopedQuerySource.machine .relational input.program).run
    (childExecution input handle formulaName roundName nodeName).budget input.childBefore = _ at child
  rw [child] at joined
  simpa only [List.nil_append, childExecution] using joined

/-- The numeric result is the original captured occurrence count, including
duplicates. Neither completed child execution nor successful allocation is
assumed. The reached caller still contains the original continuation. -/
theorem counted_prefix {codec : Codec Label} {label : Label} {round : Nat} {input : Input Context}
    {handle : NamedSpaces.Handle} {formulaName roundName nodeName : String}
    (entry : Entry codec label round input handle formulaName roundName nodeName)
    (reserve : (entry.rows.filterMap (frontSelect label round)).length ≤ input.state.allocator.usableCount)
    (representative : String) (unbound : read entry.principal input.destination = .var representative) :
    ∃ (after : State Context) (next : Allocator),
      after.world.state.read handle = some ((CTLUntilCleanup.remaining label round entry.rows).map (render codec)) ∧
      decodeRows codec ((CTLUntilCleanup.remaining label round entry.rows).map (render codec)) =
        some (CTLUntilCleanup.remaining label round entry.rows) ∧
      (∀ other, other ≠ handle → after.world.state.read other = input.state.world.state.read other) ∧
      after.world.state.cells = input.state.world.state.cells ∧
      next.usableCount + (entry.rows.filterMap (frontSelect label round)).length = input.state.allocator.usableCount ∧
      (ScopedQuerySource.machine .relational input.program).run
        (2 + (childExecution input handle formulaName roundName nodeName).budget + 1 + 3) input.before =
        ([], .exhausted (placed next after.world input.state.scope input.state.parents
          (GuardedCountReturn.counted input.caller input.slot input.destination (entry.rows.filterMap (frontSelect label round)).length)
          input.context (input.origins ++ [0]) input.pending)) := by
  obtain ⟨after, completed, reading, decoded, count, others, cells, allocator, saved, parents, silent⟩ := child_completed entry
  have boundary : after.cursor [] = GuardedQueryCollection.boundary after.allocator after.world after.scope.collected
      input.savedCaller {input.state.scope with frontier := input.pending} input.state.parents := by
    simp only [State.cursor, GuardedQueryCollection.boundary, parents]
    congr 2
    cases scope : after.scope
    simp_all
  have ready := completed_packets input handle formulaName roundName nodeName after completed
  have capacity : after.scope.collected.length ≤ after.allocator.usableCount := by rw [count, allocator]; exact reserve
  obtain ⟨next, returned, balance⟩ := GuardedQueryCopyCapacity.return_with_capacity input.program after.allocator
    after.world after.scope.collected input.savedCaller {input.state.scope with frontier := input.pending} input.state.parents ready capacity
  rw [← boundary] at returned
  change (ScopedQuerySource.machine .relational input.program).run 1 (after.cursor []) =
    ([], .exhausted (placed next after.world input.state.scope input.state.parents
      (GuardedCountReturn.tupleReturned input.caller input.slot input.destination after.scope.collected.length)
      input.context input.origins input.pending)) at returned
  have reached := child_prefix input handle formulaName roundName nodeName entry.written
  simp only [ScopedNestedQueryExecution.Execution.observation, completed, silent, ScopedNestedQueryExecution.Stop.outcome] at reached
  have collected := (ScopedQuerySource.machine .relational input.program).established_and_pending
    (2 + (childExecution input handle formulaName roundName nodeName).budget) 1 _ _ [] reached
  rw [returned] at collected
  simp only [List.nil_append] at collected
  have numeric := GuardedCountReturn.count_prefix input.program next after.world input.state.scope input.state.parents
    input.caller input.context input.origins input.pending input.slot input.destination after.scope.collected.length
    entry.principal representative entry.resolved unbound (CountedSourceEntry.slot_fresh input) (CountedSourceEntry.slot_apart input)
  have joined := (ScopedQuerySource.machine .relational input.program).established_and_pending
    (2 + (childExecution input handle formulaName roundName nodeName).budget + 1) 3 _ _ [] collected
  rw [numeric] at joined
  rw [count] at joined balance
  rw [allocator] at balance
  exact ⟨after, next, reading, decoded, others, cells, balance, by simpa only [List.nil_append] using joined⟩

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCountedCleanup

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCountedCleanup.counted_prefix
