import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilScopedRound
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilQueryGrowth

/-!
# Stable live query views of completed EU rounds

The source world changes during the nested traversal. Its current-round
frontier, reverse-edge, and distinct operand-label query views do not change.
The statements quantify over actual captured callers and retain physical row
ordinals, duplicate occurrences, missing handles, and capture refusal.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundViews

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open NamedGuardedCandidateBatch (State)
open FlatQueryRowCodec (Codec)
open CTLUntilMixedStore (Row decodeRows)
open CTLUntilScopedRound

variable {Context Label : Type} [DecidableEq Label]

def CaptureView (state : Effects.State) (handle : NamedSpaces.Handle) (caller : Control)
    (pattern body destination : Atom) (older : List Goal) (offset : Nat) :=
  (state.read handle).bind (ScopedQuerySource.capture caller pattern body destination older offset)

structure Stable (codec : Codec Label) (label operand : Label) (round : Nat) (query : Query)
    (before after : Effects.State) : Prop where
  frontier : ∀ caller body destination older offset,
    CaptureView after query.frontierHandle caller
      (CTLUntilMixedStore.frontierPattern codec label round query.names.next) body destination older offset =
    CaptureView before query.frontierHandle caller
      (CTLUntilMixedStore.frontierPattern codec label round query.names.next) body destination older offset
  edge : ∀ next caller body destination older offset,
    CaptureView after query.edgeHandle caller (CTLUntilSourceCapture.preparedEdge next query.names.prior) body destination older offset =
    CaptureView before query.edgeHandle caller (CTLUntilSourceCapture.preparedEdge next query.names.prior) body destination older offset
  operand : ∀ prior caller body destination older offset,
    CaptureView after query.operandHandle caller (CTLUntilMixedCapture.preparedSatisfaction codec operand prior) body destination older offset =
    CaptureView before query.operandHandle caller (CTLUntilMixedCapture.preparedSatisfaction codec operand prior) body destination older offset

omit [DecidableEq Label] in
theorem Stable.refl (codec : Codec Label) (label operand : Label) (round : Nat) (query : Query) (state : Effects.State) :
    Stable codec label operand round query state state :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

omit [DecidableEq Label] in
theorem Stable.trans {codec : Codec Label} {label operand : Label} {round : Nat} {query : Query}
    {first middle last : Effects.State}
    (earlier : Stable codec label operand round query first middle)
    (later : Stable codec label operand round query middle last) : Stable codec label operand round query first last :=
  ⟨fun caller body destination older offset => (later.frontier caller body destination older offset).trans
      (earlier.frontier caller body destination older offset),
    fun next caller body destination older offset => (later.edge next caller body destination older offset).trans
      (earlier.edge next caller body destination older offset),
    fun prior caller body destination older offset => (later.operand prior caller body destination older offset).trans
      (earlier.operand prior caller body destination older offset)⟩

theorem leaf_stable (codec : Codec Label) (label operand : Label) (distinct : label ≠ operand)
    (round : Nat) (query : Query) (program : SpaceSemantics.Program)
    (caller : Control) (before after : State Context) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context))
    (frame : Frame codec label operand round query [] caller)
    (completed : ((GuardedNestedQuerySource.leaf program query.template Context).execute
      caller before context origins pending).stop = .complete after) :
    Stable codec label operand round query before.world.state after.world.state := by
  cases frame with
  | publish _ resolved fixed prior bound =>
    obtain ⟨principal, resolved⟩ := resolved
    have readings := fixed principal (resolve_sound resolved)
    have payload := CTLUntilCandidateAdmission.payload_readings codec label round prior query.names principal
      readings.1 readings.2.2.2 (bound principal (resolve_sound resolved))
    obtain ⟨receipt⟩ := CTLUntilLeafPublication.completed_refinement codec label round prior program query.template
      caller before after context origins pending principal resolved payload.1 payload.2 completed
    constructor
    · intro selectedCaller body destination older offset
      exact receipt.capture_preserved query.frontierHandle selectedCaller _ body destination older offset
        (CTLUntilMixedCapture.publication_frontier_unmatched codec label round prior query.names.next)
    · intro next selectedCaller body destination older offset
      exact receipt.capture_preserved query.edgeHandle selectedCaller _ body destination older offset
        (CTLUntilMixedCapture.publication_edge_unmatched codec label round prior next query.names.prior)
    · intro node selectedCaller body destination older offset
      exact receipt.capture_preserved query.operandHandle selectedCaller _ body destination older offset
        (CTLUntilMixedCapture.publication_operand_unmatched codec label operand distinct round prior node)

/-- Actual completed nested execution preserves all three query views even
when their handles alias either write target. No initial frozen-world
execution replaces the live source run in this theorem. -/
theorem completed_stable (codec : Codec Label) (label operand : Label) (distinct : label ≠ operand)
    (round : Nat) (query : Query) (apart : query.names.prior ≠ query.names.next)
    (program : SpaceSemantics.Program) (caller : Control) (before after : State Context)
    (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (resolved : Resolved caller) (fixed : Fixed codec label operand round query caller)
    (nextFresh : ClosedOnceQueryFrame.FreshFor query.names.next caller.bindings)
    (priorFresh : ClosedOnceQueryFrame.FreshFor query.names.prior caller.bindings)
    (valid : Decoded codec query.handles before)
    (completed : (ScopedNestedQueryExecution.run program (GuardedNestedQuerySource.leaf program query.template Context)
      query.legs caller before context origins pending).stop = .complete after) :
    Decoded codec query.handles after ∧ Stable codec label operand round query before.world.state after.world.state := by
  let invariant : State Context → Prop := fun current =>
    Decoded codec query.handles current ∧ Stable codec label operand round query before.world.state current.world.state
  have atLeaf : ScopedNestedQueryExecution.PreservesOn (Frame codec label operand round query []) invariant
      (GuardedNestedQuerySource.leaf program query.template Context).execute := by
    intro currentCaller current currentContext currentOrigins currentPending next frame admitted done
    exact ⟨leaf_preserves codec label operand round query program query.handles
        currentCaller current currentContext currentOrigins currentPending next frame admitted.1 done,
      admitted.2.trans (leaf_stable codec label operand distinct round query program
        currentCaller current next currentContext currentOrigins currentPending frame done)⟩
  exact ScopedNestedQueryExecution.run_preserves_family program
    (GuardedNestedQuerySource.leaf program query.template Context) (Frame codec label operand round query) invariant atLeaf
    (fun leg rest currentCaller current currentContext currentOrigins currentPending selected frame admitted captured =>
      capture_frame codec label operand round query apart program leg rest currentCaller current currentContext
        currentOrigins currentPending selected frame admitted.1 captured) query.legs
    caller before context origins pending after (Frame.frontier caller resolved fixed nextFresh priorFresh)
    ⟨valid, Stable.refl codec label operand round query before.world.state⟩ completed

/-- Count correspondence no longer requires a caller-provided final decode.
This counts all formula labels. Identifying it with output-label-only growth
requires a separate fixed-label growth law. -/
theorem completed_pair_count (codec : Codec Label) (label operand : Label) (round : Nat) (query : Query)
    (apart : query.names.prior ≠ query.names.next) (program : SpaceSemantics.Program)
    (caller : Control) (before after : State Context) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context)) (resolved : Resolved caller)
    (fixed : Fixed codec label operand round query caller)
    (nextFresh : ClosedOnceQueryFrame.FreshFor query.names.next caller.bindings)
    (priorFresh : ClosedOnceQueryFrame.FreshFor query.names.prior caller.bindings)
    (valid : Decoded codec query.handles before) (empty : before.scope.collected = [])
    (completed : (ScopedNestedQueryExecution.run program (GuardedNestedQuerySource.leaf program query.template Context)
      query.legs caller before context origins pending).stop = .complete after) :
    ∃ initialAtoms initialRows finalAtoms finalRows,
      before.world.state.read query.satisfactionHandle = some initialAtoms ∧ decodeRows codec initialAtoms = some initialRows ∧
      after.world.state.read query.satisfactionHandle = some finalAtoms ∧ decodeRows codec finalAtoms = some finalRows ∧
      (CTLUntilQueryGrowth.pairs finalRows).toFinset.card =
        (CTLUntilQueryGrowth.pairs initialRows).toFinset.card + after.scope.collected.length := by
  have final := completed_decoded codec label operand round query apart program caller before after context origins pending
    resolved fixed nextFresh priorFresh valid completed
  obtain ⟨initialAtoms, initialRows, initialRead, initialDecode⟩ := valid query.satisfactionHandle (by simp [Query.handles])
  obtain ⟨finalAtoms, finalRows, finalRead, finalDecode⟩ := final query.satisfactionHandle (by simp [Query.handles])
  refine ⟨initialAtoms, initialRows, finalAtoms, finalRows, initialRead, initialDecode, finalRead, finalDecode, ?_⟩
  exact CTLUntilQueryGrowth.completed_pair_count codec program query.template _ rfl query.legs caller before after
    context origins pending initialAtoms finalAtoms initialRows finalRows initialRead initialDecode finalRead finalDecode empty completed

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundViews
