import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCountedSource

/-!
# Data preserved by the actual EU round

Publication appends only the output-label satisfaction row and next-frontier
row. Graph and distinct operand-label views therefore survive even when all
handles alias. The proof follows actual completed publication receipts and
the existing nested source traversal, including all duplicate occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundData

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS.Destination
open ClosedOnceQueryFrame (FreshFor placed)
open NamedGuardedCandidateBatch (State)
open CTLUntilScopedRound (Query Frame Fixed Resolved Decoded)
open FlatQueryRowCodec (Codec)
open CTLUntilMixedStore (Row graphView satisfactionView decodeRows frontSelect)
open CTLUntilRoundPublication (observe)

variable {Context Label : Type} [DecidableEq Label]

def graph (codec : Codec Label) (handle : NamedSpaces.Handle) (state : Effects.State) : Option (List (Nat × Nat)) :=
  observe codec graphView handle state

def operand (codec : Codec Label) (label : Label) (handle : NamedSpaces.Handle) (state : Effects.State) : Option (List Nat) :=
  observe codec (satisfactionView label) handle state

structure Preserved (codec : Codec Label) (holds : Label) (query : Query) (before after : Effects.State) : Prop where
  graph : graph codec query.edgeHandle after = graph codec query.edgeHandle before
  operand : operand codec holds query.operandHandle after = operand codec holds query.operandHandle before
  cells : after.cells = before.cells
  outside : ∀ handle, handle ≠ query.satisfactionHandle → handle ≠ query.nextFrontierHandle →
    after.read handle = before.read handle

theorem Preserved.refl (codec : Codec Label) (holds : Label) (query : Query) (state : Effects.State) :
    Preserved codec holds query state state := ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩

theorem Preserved.trans {codec : Codec Label} {holds : Label} {query : Query} {first middle last : Effects.State}
    (earlier : Preserved codec holds query first middle) (later : Preserved codec holds query middle last) :
    Preserved codec holds query first last :=
  ⟨later.graph.trans earlier.graph, later.operand.trans earlier.operand, later.cells.trans earlier.cells,
    fun handle firstApart secondApart => (later.outside handle firstApart secondApart).trans
      (earlier.outside handle firstApart secondApart)⟩

omit [DecidableEq Label] in
theorem graph_append (label : Label) (round node : Nat)
    (satisfactionHandle frontierHandle observed : NamedSpaces.Handle) (rows : List (Row Label)) :
    graphView (rows ++ CTLUntilPublicationSource.additions label round node satisfactionHandle frontierHandle observed) =
      graphView rows := by
  unfold graphView CTLUntilPublicationSource.additions
  split_ifs <;> simp

omit [DecidableEq Label] in
theorem completed_leaf_cells (program : SpaceSemantics.Program) (template : GuardedNestedQuerySource.Template)
    (caller : Control) (before after : State Context) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context))
    (completed : (GuardedNestedQuerySource.invoke program template caller before context origins pending).execution.stop = .complete after) :
    after.world.state.cells = before.world.state.cells := by
  obtain ⟨principal, request, advance, resolved, requested, advanced, rfl⟩ :=
    GuardedNestedQuerySource.completed_origin program template caller before context origins pending after completed
  have publication := NamedGuardedCandidateExecution.execute_publication
    ((template.candidate caller context origins request).input program before pending) template.body advance advanced
  change advance.state.cells = before.world.state.cells
  cases publication with
  | held rows snapshot present copied unchanged noPacket =>
    exact congrArg NamedSpaces.Store.cells unchanged
  | fresh guard evidence rows middle snapshot absent first second allocator packet =>
    exact (Effects.insert_preserves_cells second).trans (Effects.insert_preserves_cells first)

theorem receipt_views (codec : Codec Label) (label holds : Label) (separate : label ≠ holds)
    (round node : Nat) (query : Query) (before after : State Context)
    (receipt : CTLUntilLeafPublication.Refinement codec label round node query.template before after)
    (valid : Decoded codec query.handles before) :
    graph codec query.edgeHandle after.world.state = graph codec query.edgeHandle before.world.state ∧
      operand codec holds query.operandHandle after.world.state = operand codec holds query.operandHandle before.world.state ∧
      (∀ handle, handle ≠ query.satisfactionHandle → handle ≠ query.nextFrontierHandle →
        after.world.state.read handle = before.world.state.read handle) := by
  obtain ⟨graphAtoms, graphRows, graphRead, graphDecode⟩ := valid query.edgeHandle (by simp [Query.handles])
  obtain ⟨operandAtoms, operandRows, operandRead, operandDecode⟩ := valid query.operandHandle (by simp [Query.handles])
  obtain ⟨graphAfter, graphDecoded⟩ := receipt.decoded_after query.edgeHandle graphAtoms graphRows graphRead graphDecode
  obtain ⟨operandAfter, operandDecoded⟩ := receipt.decoded_after query.operandHandle operandAtoms operandRows operandRead operandDecode
  refine ⟨?_, ?_, ?_⟩
  · unfold graph
    rw [CTLUntilRoundPublication.observe_decoded codec graphView _ _ _ _ graphAfter graphDecoded,
      CTLUntilRoundPublication.observe_decoded codec graphView _ _ _ _ graphRead graphDecode]
    cases receipt.fresh <;> simp [graph_append]
  · unfold operand
    rw [CTLUntilRoundPublication.observe_decoded codec (satisfactionView holds) _ _ _ _ operandAfter operandDecoded,
      CTLUntilRoundPublication.observe_decoded codec (satisfactionView holds) _ _ _ _ operandRead operandDecode]
    cases receipt.fresh <;> simp [CTLUntilPublicationSource.operand_view_append, separate]
  · intro handle firstApart secondApart
    rw [receipt.reads]
    simp [CTLUntilPublicationSource.additions, Query.template, firstApart, secondApart]

theorem leaf_preserved (codec : Codec Label) (label holds : Label) (separate : label ≠ holds)
    (round : Nat) (query : Query) (program : SpaceSemantics.Program)
    (caller : Control) (before after : State Context) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context))
    (frame : Frame codec label holds round query [] caller) (valid : Decoded codec query.handles before)
    (completed : ((GuardedNestedQuerySource.leaf program query.template Context).execute
      caller before context origins pending).stop = .complete after) :
    Preserved codec holds query before.world.state after.world.state := by
  cases frame with
  | publish _ resolved fixed node bound =>
    obtain ⟨principal, resolved⟩ := resolved
    have readings := fixed principal (resolve_sound resolved)
    have payload := CTLUntilCandidateAdmission.payload_readings codec label round node query.names principal
      readings.1 readings.2.2.2 (bound principal (resolve_sound resolved))
    obtain ⟨receipt⟩ := CTLUntilLeafPublication.completed_refinement codec label round node program query.template
      caller before after context origins pending principal resolved payload.1 payload.2 completed
    obtain ⟨graph, operand, outside⟩ := receipt_views codec label holds separate round node query before after receipt valid
    exact ⟨graph, operand, completed_leaf_cells program query.template caller before after context origins pending completed, outside⟩

/-- The decoded input views are conclusions about the same actual completed
round, not additional hypotheses about its final store. -/
theorem completed_preserved (codec : Codec Label) (label holds : Label) (separate : label ≠ holds)
    (round : Nat) (query : Query) (apart : query.names.prior ≠ query.names.next)
    (program : SpaceSemantics.Program) (caller : Control) (before after : State Context)
    (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (resolved : Resolved caller) (fixed : Fixed codec label holds round query caller)
    (nextFresh : FreshFor query.names.next caller.bindings) (priorFresh : FreshFor query.names.prior caller.bindings)
    (valid : Decoded codec query.handles before)
    (completed : (ScopedNestedQueryExecution.run program (GuardedNestedQuerySource.leaf program query.template Context)
      query.legs caller before context origins pending).stop = .complete after) :
    Decoded codec query.handles after ∧ Preserved codec holds query before.world.state after.world.state := by
  let invariant : State Context → Prop := fun current =>
    Decoded codec query.handles current ∧ Preserved codec holds query before.world.state current.world.state
  have atLeaf : ScopedNestedQueryExecution.PreservesOn (Frame codec label holds round query []) invariant
      (GuardedNestedQuerySource.leaf program query.template Context).execute := by
    intro currentCaller current currentContext currentOrigins currentPending next frame admitted done
    exact ⟨CTLUntilScopedRound.leaf_preserves codec label holds round query program query.handles
        currentCaller current currentContext currentOrigins currentPending next frame admitted.1 done,
      admitted.2.trans (leaf_preserved codec label holds separate round query program
        currentCaller current next currentContext currentOrigins currentPending frame admitted.1 done)⟩
  exact ScopedNestedQueryExecution.run_preserves_family program
    (GuardedNestedQuerySource.leaf program query.template Context) (Frame codec label holds round query) invariant atLeaf
    (fun leg rest currentCaller current currentContext currentOrigins currentPending selected frame admitted captured =>
      CTLUntilScopedRound.capture_frame codec label holds round query apart program leg rest currentCaller current
        currentContext currentOrigins currentPending selected frame admitted.1 captured) query.legs
    caller before context origins pending after (Frame.frontier caller resolved fixed nextFresh priorFresh)
    ⟨valid, Preserved.refl codec holds query before.world.state⟩ completed

theorem counted_child_preserved {codec : Codec Label} {label holds : Label} {round : Nat} {query : Query}
    {input : GuardedCountSource.Input Context}
    (entry : CTLUntilCountedSource.Entry codec label holds round query input) (separate : label ≠ holds)
    (after : State Context) (completed : input.childExecution.stop = .complete after) :
    Decoded codec query.handles after ∧ Preserved codec holds query input.state.world.state after.world.state := by
  let childQuery := CTLUntilCountedFrame.childQuery input query
  have execution : (ScopedNestedQueryExecution.run input.program
      (GuardedNestedQuerySource.leaf input.program childQuery.template Context)
      childQuery.legs input.childCaller input.childState input.context input.origins []).stop = .complete after := by
    dsimp only [childQuery]
    simpa only [CTLUntilCountedFrame.child_template input query entry.template,
      CTLUntilCountedFrame.child_legs, entry.legs, GuardedCountSource.Input.childExecution] using completed
  have apart : childQuery.names.prior ≠ childQuery.names.next := by
    have distinct := entry.distinct
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at distinct
    exact Ne.symm distinct.1.1
  obtain ⟨decoded, preserved⟩ := completed_preserved codec label holds separate round childQuery apart input.program input.childCaller
    input.childState after input.context input.origins [] ⟨entry.principal, entry.resolved⟩
    (CTLUntilScopedRound.fixed_of_readings codec label holds round childQuery input.childCaller entry.principal
      entry.resolved entry.formula entry.holds entry.current entry.nextRound)
    entry.nextFresh entry.priorFresh entry.decoded execution
  exact ⟨decoded, ⟨preserved.graph, preserved.operand, preserved.cells, preserved.outside⟩⟩

/-- Completion, preserved input data, output count and copying share one
actual child receipt and one returned source cursor. -/
theorem counted_prefix_data {codec : Codec Label} {label holds : Label} {round : Nat} {query : Query}
    {input : GuardedCountSource.Input Context}
    (entry : CTLUntilCountedSource.Entry codec label holds round query input) (separate : label ≠ holds)
    (reserve : entry.word.length ≤ input.state.allocator.usableCount) (representative : String)
    (unbound : read entry.principal input.destination = .var representative) :
    ∃ (after : State Context) (next : Allocator),
      Decoded codec query.handles after ∧ Preserved codec holds query input.state.world.state after.world.state ∧
      CTLUntilRoundPublication.known codec label query after.world.state = some (entry.initialKnown ++ entry.added) ∧
      CTLUntilRoundPublication.frontier codec label round query after.world.state = some (entry.initialFrontier ++ entry.added) ∧
      next.usableCount + entry.word.length = input.state.allocator.usableCount ∧
      (ScopedQuerySource.machine .relational input.program).run (2 + input.childExecution.budget + 1 + 3) input.before =
        ([], .exhausted (placed next after.world input.state.scope input.state.parents
          (GuardedCountReturn.counted input.caller input.slot input.destination entry.added.length)
          input.context (input.origins ++ [0]) input.pending)) := by
  obtain ⟨after, next, copies, completed, copied, count, known, frontier, capacity⟩ :=
    CTLUntilCountedSource.child_completed entry separate reserve
  obtain ⟨decoded, preserved⟩ := counted_child_preserved entry separate after completed
  have returned := GuardedCountSource.counted_prefix input after next copies entry.principal representative
    entry.resolved unbound completed copied
  rw [GuardedQuerySilence.childExecution_events input, count] at returned
  exact ⟨after, next, decoded, preserved, known, frontier, capacity, returned⟩

/-- Every other round of the output label is unchanged at every handle,
including handles outside the query and aliased publication targets. -/
def OtherFrontiers (codec : Codec Label) (label : Label) (round : Nat) (before after : Effects.State) : Prop :=
  ∀ handle step, step ≠ round + 1 →
    observe codec (List.filterMap (frontSelect label step)) handle after =
      observe codec (List.filterMap (frontSelect label step)) handle before

theorem other_frontier_append (label : Label) (round node step : Nat) (different : step ≠ round + 1)
    (satisfactionHandle frontierHandle observed : NamedSpaces.Handle) (rows : List (Row Label)) :
    (rows ++ CTLUntilPublicationSource.additions label round node satisfactionHandle frontierHandle observed).filterMap
      (frontSelect label step) = rows.filterMap (frontSelect label step) := by
  unfold CTLUntilPublicationSource.additions
  split_ifs <;> simp [frontSelect, Ne.symm different]

theorem receipt_other_frontiers (codec : Codec Label) (label : Label) (round node : Nat)
    (query : Query) (before after : State Context)
    (receipt : CTLUntilLeafPublication.Refinement codec label round node query.template before after)
    (valid : Decoded codec query.handles before) : OtherFrontiers codec label round before.world.state after.world.state := by
  have preserved (handle : NamedSpaces.Handle) (member : handle ∈ query.handles)
      (step : Nat) (different : step ≠ round + 1) :
      observe codec (List.filterMap (frontSelect label step)) handle after.world.state =
        observe codec (List.filterMap (frontSelect label step)) handle before.world.state := by
    obtain ⟨atoms, rows, snapshot, decoded⟩ := valid handle member
    obtain ⟨afterRead, afterDecode⟩ := receipt.decoded_after handle atoms rows snapshot decoded
    rw [CTLUntilRoundPublication.observe_decoded codec _ _ _ _ _ afterRead afterDecode,
      CTLUntilRoundPublication.observe_decoded codec _ _ _ _ _ snapshot decoded]
    cases receipt.fresh <;> simp [other_frontier_append label round node step different]
  intro handle step different
  by_cases satisfaction : handle = query.satisfactionHandle
  · exact preserved handle (by rw [satisfaction]; simp [Query.handles]) step different
  by_cases frontier : handle = query.nextFrontierHandle
  · exact preserved handle (by rw [frontier]; simp [Query.handles]) step different
  unfold observe
  rw [receipt.reads]
  simp [CTLUntilPublicationSource.additions, Query.template, satisfaction, frontier]

theorem leaf_other_frontiers (codec : Codec Label) (label holds : Label) (round : Nat) (query : Query)
    (program : SpaceSemantics.Program) (caller : Control) (before after : State Context) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (frame : Frame codec label holds round query [] caller) (valid : Decoded codec query.handles before)
    (completed : ((GuardedNestedQuerySource.leaf program query.template Context).execute
      caller before context origins pending).stop = .complete after) :
    OtherFrontiers codec label round before.world.state after.world.state := by
  cases frame with
  | publish _ resolved fixed node bound =>
    obtain ⟨principal, resolved⟩ := resolved
    have readings := fixed principal (resolve_sound resolved)
    have payload := CTLUntilCandidateAdmission.payload_readings codec label round node query.names principal
      readings.1 readings.2.2.2 (bound principal (resolve_sound resolved))
    obtain ⟨receipt⟩ := CTLUntilLeafPublication.completed_refinement codec label round node program query.template
      caller before after context origins pending principal resolved payload.1 payload.2 completed
    exact receipt_other_frontiers codec label round node query before after receipt valid

theorem completed_other_frontiers (codec : Codec Label) (label holds : Label) (round : Nat)
    (query : Query) (apart : query.names.prior ≠ query.names.next) (program : SpaceSemantics.Program)
    (caller : Control) (before after : State Context) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context)) (resolved : Resolved caller)
    (fixed : Fixed codec label holds round query caller) (nextFresh : FreshFor query.names.next caller.bindings)
    (priorFresh : FreshFor query.names.prior caller.bindings) (valid : Decoded codec query.handles before)
    (completed : (ScopedNestedQueryExecution.run program (GuardedNestedQuerySource.leaf program query.template Context)
      query.legs caller before context origins pending).stop = .complete after) :
    OtherFrontiers codec label round before.world.state after.world.state := by
  let invariant : State Context → Prop := fun current =>
    Decoded codec query.handles current ∧ OtherFrontiers codec label round before.world.state current.world.state
  have atLeaf : ScopedNestedQueryExecution.PreservesOn (Frame codec label holds round query []) invariant
      (GuardedNestedQuerySource.leaf program query.template Context).execute := by
    intro currentCaller current currentContext currentOrigins currentPending next frame admitted done
    refine ⟨CTLUntilScopedRound.leaf_preserves codec label holds round query program query.handles
      currentCaller current currentContext currentOrigins currentPending next frame admitted.1 done, ?_⟩
    have step := leaf_other_frontiers codec label holds round query program currentCaller current next
      currentContext currentOrigins currentPending frame admitted.1 done
    exact fun handle time different => (step handle time different).trans (admitted.2 handle time different)
  have final := ScopedNestedQueryExecution.run_preserves_family program
    (GuardedNestedQuerySource.leaf program query.template Context) (Frame codec label holds round query) invariant atLeaf
    (fun leg rest currentCaller current currentContext currentOrigins currentPending selected frame admitted captured =>
      CTLUntilScopedRound.capture_frame codec label holds round query apart program leg rest currentCaller current
        currentContext currentOrigins currentPending selected frame admitted.1 captured) query.legs caller before context origins pending after
    (Frame.frontier caller resolved fixed nextFresh priorFresh) ⟨valid, fun _ _ _ => rfl⟩ completed
  exact final.2

theorem counted_child_other_frontiers {codec : Codec Label} {label holds : Label} {round : Nat} {query : Query}
    {input : GuardedCountSource.Input Context} (entry : CTLUntilCountedSource.Entry codec label holds round query input)
    (after : State Context) (completed : input.childExecution.stop = .complete after) :
    OtherFrontiers codec label round input.state.world.state after.world.state := by
  let childQuery := CTLUntilCountedFrame.childQuery input query
  have execution : (ScopedNestedQueryExecution.run input.program
      (GuardedNestedQuerySource.leaf input.program childQuery.template Context)
      childQuery.legs input.childCaller input.childState input.context input.origins []).stop = .complete after := by
    dsimp only [childQuery]
    simpa only [CTLUntilCountedFrame.child_template input query entry.template,
      CTLUntilCountedFrame.child_legs, entry.legs, GuardedCountSource.Input.childExecution] using completed
  have apart : childQuery.names.prior ≠ childQuery.names.next := by
    have distinct := entry.distinct
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at distinct
    exact Ne.symm distinct.1.1
  exact completed_other_frontiers codec label holds round childQuery apart input.program input.childCaller input.childState after
    input.context input.origins [] ⟨entry.principal, entry.resolved⟩
    (CTLUntilScopedRound.fixed_of_readings codec label holds round childQuery input.childCaller entry.principal
      entry.resolved entry.formula entry.holds entry.current entry.nextRound)
    entry.nextFresh entry.priorFresh entry.decoded execution

theorem counted_prefix_data_frontier {codec : Codec Label} {label holds : Label} {round : Nat} {query : Query}
    {input : GuardedCountSource.Input Context}
    (entry : CTLUntilCountedSource.Entry codec label holds round query input) (separate : label ≠ holds)
    (reserve : entry.word.length ≤ input.state.allocator.usableCount) (representative : String)
    (unbound : read entry.principal input.destination = .var representative) :
    ∃ (after : State Context) (next : Allocator),
      Decoded codec query.handles after ∧ Preserved codec holds query input.state.world.state after.world.state ∧
      OtherFrontiers codec label round input.state.world.state after.world.state ∧
      CTLUntilRoundPublication.known codec label query after.world.state = some (entry.initialKnown ++ entry.added) ∧
      CTLUntilRoundPublication.frontier codec label round query after.world.state = some (entry.initialFrontier ++ entry.added) ∧
      next.usableCount + entry.word.length = input.state.allocator.usableCount ∧
      (ScopedQuerySource.machine .relational input.program).run (2 + input.childExecution.budget + 1 + 3) input.before =
        ([], .exhausted (placed next after.world input.state.scope input.state.parents
          (GuardedCountReturn.counted input.caller input.slot input.destination entry.added.length)
          input.context (input.origins ++ [0]) input.pending)) := by
  obtain ⟨after, next, copies, completed, copied, count, known, frontier, capacity⟩ :=
    CTLUntilCountedSource.child_completed entry separate reserve
  obtain ⟨decoded, preserved⟩ := counted_child_preserved entry separate after completed
  have other := counted_child_other_frontiers entry after completed
  have returned := GuardedCountSource.counted_prefix input after next copies entry.principal representative
    entry.resolved unbound completed copied
  rw [GuardedQuerySilence.childExecution_events input, count] at returned
  exact ⟨after, next, decoded, preserved, other, known, frontier, capacity, returned⟩

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundData
