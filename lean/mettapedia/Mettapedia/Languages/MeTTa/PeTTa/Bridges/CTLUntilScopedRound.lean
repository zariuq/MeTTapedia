import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLeafPublication
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilScopedCapture
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCandidateAdmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilScopedFrame

/-!
# Typed store preservation through a live EU query round

The phase invariant describes the reached source controls, including every
query's handle preparation. Query snapshots are read from the current world.
Completed leaves derive typed writes from their actual receipts; a suspended
or reference result is not treated as a completed round.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilScopedRound

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open NamedGuardedCandidateBatch (State)
open FlatQueryRowCodec (Codec)
open CTLUntilMixedStore (Row render decodeRows)
open CTLUntilSourceRows (number)
open ClosedOnceQueryFrame (FreshFor)
open NestedQuerySource (Leg)

structure Query where
  names : CTLUntilCandidateAdmission.Names
  operand : String
  currentRound : String
  frontierHandle : NamedSpaces.Handle
  edgeHandle : NamedSpaces.Handle
  operandHandle : NamedSpaces.Handle
  satisfactionHandle : NamedSpaces.Handle
  nextFrontierHandle : NamedSpaces.Handle

def Query.template (query : Query) : GuardedNestedQuerySource.Template :=
  ⟨query.names.formula, query.names.prior, query.satisfactionHandle,
    ⟨query.names.result, query.names.temporary, query.nextFrontierHandle,
      CTLUntilCandidateAdmission.satisfactionCode query.names,
      CTLUntilCandidateAdmission.frontierCode query.names⟩⟩

def Query.frontier (query : Query) : Leg :=
  (query.frontierHandle, CTLUntilScopedCapture.frontierCode query.names.formula query.currentRound query.names.next)

def Query.edge (query : Query) : Leg :=
  (query.edgeHandle, CTLUntilSourceRows.reversePattern query.names.next query.names.prior)

def Query.satisfaction (query : Query) : Leg :=
  (query.operandHandle, NamedPresenceSource.patternCode query.operand query.names.prior)

def Query.legs (query : Query) : List Leg := [query.frontier, query.edge, query.satisfaction]

def Query.handles (query : Query) : List NamedSpaces.Handle :=
  [query.frontierHandle, query.edgeHandle, query.operandHandle, query.satisfactionHandle, query.nextFrontierHandle]

variable {Context Label : Type}

/-- Fixed readings hold in every solution of the actual caller equations. -/
def Fixed (codec : Codec Label) (label operand : Label) (round : Nat) (query : Query) (caller : Control) : Prop :=
  ∀ environment, Solves environment caller.bindings →
    read environment (.var query.names.formula) = codec.encode label ∧
    read environment (.var query.operand) = codec.encode operand ∧
    read environment (.var query.currentRound) = number round ∧
    read environment (.var query.names.nextRound) = number (round + 1)

def Bound (caller : Control) (name : String) (node : Nat) : Prop :=
  ∀ environment, Solves environment caller.bindings → read environment (.var name) = number node

def Resolved (caller : Control) : Prop := ∃ principal, resolve caller.bindings = some principal

theorem fixed_of_readings (codec : Codec Label) (label operand : Label) (round : Nat) (query : Query)
    (caller : Control) (principal : Environment) (resolved : resolve caller.bindings = some principal)
    (formula : read principal (.var query.names.formula) = codec.encode label)
    (holds : read principal (.var query.operand) = codec.encode operand)
    (current : read principal (.var query.currentRound) = number round)
    (next : read principal (.var query.names.nextRound) = number (round + 1)) :
    Fixed codec label operand round query caller := by
  intro environment solved
  exact ⟨CapturedQueryOperands.resolved_forces resolved _ _ formula
      (LiteralQuerySource.read_literal _ (codec.literal label)) environment solved,
    CapturedQueryOperands.resolved_forces resolved _ _ holds
      (LiteralQuerySource.read_literal _ (codec.literal operand)) environment solved,
    CapturedQueryOperands.resolved_forces resolved _ _ current
      (CTLUntilSourceCapture.number_closed round) environment solved,
    CapturedQueryOperands.resolved_forces resolved _ _ next
      (CTLUntilSourceCapture.number_closed (round + 1)) environment solved⟩

theorem Fixed.inherited {codec : Codec Label} {label operand : Label} {round : Nat} {query : Query}
    {before after : Control} (fixed : Fixed codec label operand round query before)
    (inherited : ∀ environment, Solves environment after.bindings → Solves environment before.bindings) :
    Fixed codec label operand round query after := fun environment solved => fixed environment (inherited environment solved)

theorem Bound.inherited {before after : Control} {name : String} {node : Nat}
    (bound : Bound before name node)
    (inherited : ∀ environment, Solves environment after.bindings → Solves environment before.bindings) :
    Bound after name node := fun environment solved => bound environment (inherited environment solved)

theorem bound_of_reading (caller : Control) (name : String) (node : Nat) (principal : Environment)
    (resolved : resolve caller.bindings = some principal) (reading : read principal (.var name) = number node) :
    Bound caller name node := fun environment solved =>
  CapturedQueryOperands.resolved_forces resolved _ _ reading (CTLUntilSourceCapture.number_closed node) environment solved

/-- Each constructor describes one suffix of the authored three-query body.
No final solution or successful query capture is a premise. -/
inductive Frame (codec : Codec Label) (label operand : Label) (round : Nat) (query : Query) : List Leg → Control → Prop
  | frontier (caller : Control) (resolved : Resolved caller) (fixed : Fixed codec label operand round query caller)
      (nextFresh : FreshFor query.names.next caller.bindings) (priorFresh : FreshFor query.names.prior caller.bindings) :
      Frame codec label operand round query query.legs caller
  | edge (caller : Control) (resolved : Resolved caller) (fixed : Fixed codec label operand round query caller)
      (next : Nat) (bound : Bound caller query.names.next next) (priorFresh : FreshFor query.names.prior caller.bindings) :
      Frame codec label operand round query [query.edge, query.satisfaction] caller
  | satisfaction (caller : Control) (resolved : Resolved caller) (fixed : Fixed codec label operand round query caller)
      (prior : Nat) (bound : Bound caller query.names.prior prior) :
      Frame codec label operand round query [query.satisfaction] caller
  | publish (caller : Control) (resolved : Resolved caller) (fixed : Fixed codec label operand round query caller)
      (prior : Nat) (bound : Bound caller query.names.prior prior) :
      Frame codec label operand round query [] caller

def Decoded (codec : Codec Label) (handles : List NamedSpaces.Handle) (state : State Context) : Prop :=
  ∀ handle ∈ handles, ∃ atoms rows,
    state.world.state.read handle = some atoms ∧ decodeRows codec atoms = some rows

theorem leaf_preserves (codec : Codec Label) (label operand : Label) (round : Nat) (query : Query)
    (program : SpaceSemantics.Program) (handles : List NamedSpaces.Handle) :
    ScopedNestedQueryExecution.PreservesOn (Frame codec label operand round query []) (Decoded codec handles)
      (GuardedNestedQuerySource.leaf program query.template Context).execute := by
  intro caller before context origins pending after frame valid completed
  cases frame with
  | publish _ resolved fixed prior bound =>
    obtain ⟨principal, resolved⟩ := resolved
    have readings := fixed principal (resolve_sound resolved)
    have payload := CTLUntilCandidateAdmission.payload_readings codec label round prior query.names principal
      readings.1 readings.2.2.2 (bound principal (resolve_sound resolved))
    obtain ⟨receipt⟩ := CTLUntilLeafPublication.completed_refinement codec label round prior program query.template
      caller before after context origins pending principal resolved payload.1 payload.2 completed
    intro observed member
    obtain ⟨atoms, rows, snapshot, decoded⟩ := valid observed member
    exact ⟨_, _, receipt.decoded_after observed atoms rows snapshot decoded⟩

variable [DecidableEq Label]

/-- Every selected child satisfies the next phase invariant. The selection
is recovered from the live decoder and the actual matcher, including every
physical duplicate; no two-capture replacement frame is used. -/
theorem capture_frame (codec : Codec Label) (label operand : Label) (round : Nat) (query : Query)
    (apart : query.names.prior ≠ query.names.next) (program : SpaceSemantics.Program)
    (leg : Leg) (rest : List Leg) (caller : Control) (state : State Context)
    (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (selected : ScopedMatchEntry.Selection (ScopedNestedQueryExecution.source rest query.template.source)
      (.var query.names.result) caller.goals)
    (frame : Frame codec label operand round query (leg :: rest) caller)
    (valid : Decoded codec query.handles state)
    (captured : (ScopedMatchEntry.execute program leg.1 leg.2
      (ScopedNestedQueryExecution.source rest query.template.source) (.var query.names.result)
      caller state context origins pending).result = .captured selected) :
    ∀ entry ∈ selected.choices, Frame codec label operand round query rest {entry.2 with goals := caller.goals} := by
  cases frame with
  | frontier _ resolved fixed nextFresh priorFresh =>
    obtain ⟨principal, resolved⟩ := resolved
    have readings := fixed principal (resolve_sound resolved)
    obtain ⟨atoms, rows, snapshot, decoded⟩ := valid query.frontierHandle (by simp [Query.handles])
    let body := ScopedNestedQueryExecution.source [query.edge, query.satisfaction] query.template.source
    obtain ⟨_, actual, actualCaptured, choices⟩ := CTLUntilScopedCapture.frontier_capture codec program
      query.frontierHandle label round query.names.formula query.currentRound query.names.next body (.var query.names.result)
      caller state context origins pending principal atoms rows resolved readings.1 readings.2.2.1 nextFresh rfl snapshot decoded
    have same := ScopedMatchEntry.Result.captured.inj (captured.symm.trans actualCaptured)
    subst actual
    intro entry member
    rw [choices] at member
    obtain ⟨⟨position, next⟩, _member, rfl⟩ := List.mem_map.mp member
    have nextRetained := CTLUntilScopedCapture.pattern_name_retained caller (.var query.names.result)
      query.frontierHandle query.frontier.2 body query.names.next (by
        rw [Query.frontier, CTLUntilScopedCapture.frontierCode, CapturedPatternSupport.mem_expression_names]
        exact ⟨.var query.names.next, by simp, by simp [encode, Mettapedia.Logic.LP.Term.freeVars]⟩)
    have priorRetained := CTLUntilScopedCapture.body_name_retained caller (.var query.names.result)
      query.frontierHandle query.frontier.2 body query.names.prior (by
        change query.names.prior ∈ (encode (.expression [.symbol "match", Effects.handleValue query.edgeHandle,
          query.edge.2, ScopedNestedQueryExecution.source [query.satisfaction] query.template.source])).freeVars
        rw [CapturedPatternSupport.mem_expression_names]
        refine ⟨query.edge.2, by simp, ?_⟩
        rw [Query.edge, CTLUntilSourceRows.reversePattern, CapturedPatternSupport.mem_expression_names]
        exact ⟨.var query.names.prior, by simp, by simp [encode, Mettapedia.Logic.LP.Term.freeVars]⟩)
    obtain ⟨after, afterResolved⟩ := CTLUntilScopedFrame.number_capture_resolves caller (.var query.names.result)
      query.frontierHandle query.frontier.2 body query.names.next next principal resolved nextFresh nextRetained
    refine Frame.edge _ ?_ ?_ next ?_ ?_
    · exact ⟨after, afterResolved⟩
    · intro environment solved
      exact fixed environment (CTLUntilScopedFrame.capture_inherited caller (.var query.names.result)
        query.frontierHandle query.frontier.2 body _ environment solved)
    · exact bound_of_reading _ query.names.next next after afterResolved
        (CTLUntilScopedFrame.number_capture_read caller (.var query.names.result) query.frontierHandle
          query.frontier.2 body query.names.next next after afterResolved)
    · exact CTLUntilScopedFrame.number_capture_fresh caller (.var query.names.result) query.frontierHandle
        query.frontier.2 body query.names.next query.names.prior next priorFresh priorRetained apart
  | edge _ resolved fixed next bound priorFresh =>
    obtain ⟨principal, resolved⟩ := resolved
    obtain ⟨atoms, rows, snapshot, decoded⟩ := valid query.edgeHandle (by simp [Query.handles])
    let body := ScopedNestedQueryExecution.source [query.satisfaction] query.template.source
    obtain ⟨_, actual, actualCaptured, choices⟩ := CTLUntilScopedCapture.edge_capture codec program
      query.edgeHandle next query.names.next query.names.prior body (.var query.names.result)
      caller state context origins pending principal atoms rows resolved (bound principal (resolve_sound resolved))
      priorFresh rfl snapshot decoded
    have same := ScopedMatchEntry.Result.captured.inj (captured.symm.trans actualCaptured)
    subst actual
    intro entry member
    rw [choices] at member
    obtain ⟨⟨position, prior⟩, _member, rfl⟩ := List.mem_map.mp member
    have retained := CTLUntilScopedCapture.pattern_name_retained caller (.var query.names.result)
      query.edgeHandle query.edge.2 body query.names.prior (by
        rw [Query.edge, CTLUntilSourceRows.reversePattern, CapturedPatternSupport.mem_expression_names]
        exact ⟨.var query.names.prior, by simp, by simp [encode, Mettapedia.Logic.LP.Term.freeVars]⟩)
    obtain ⟨after, afterResolved⟩ := CTLUntilScopedFrame.number_capture_resolves caller (.var query.names.result)
      query.edgeHandle query.edge.2 body query.names.prior prior principal resolved priorFresh retained
    refine Frame.satisfaction _ ?_ ?_ prior ?_
    · exact ⟨after, afterResolved⟩
    · intro environment solved
      exact fixed environment (CTLUntilScopedFrame.capture_inherited caller (.var query.names.result)
        query.edgeHandle query.edge.2 body _ environment solved)
    · exact bound_of_reading _ query.names.prior prior after afterResolved
        (CTLUntilScopedFrame.number_capture_read caller (.var query.names.result) query.edgeHandle
          query.edge.2 body query.names.prior prior after afterResolved)
  | satisfaction _ resolved fixed prior bound =>
    obtain ⟨principal, resolved⟩ := resolved
    have readings := fixed principal (resolve_sound resolved)
    obtain ⟨atoms, rows, snapshot, decoded⟩ := valid query.operandHandle (by simp [Query.handles])
    obtain ⟨_, actual, actualCaptured, choices⟩ := CTLUntilScopedCapture.satisfaction_capture codec program
      query.operandHandle operand prior query.operand query.names.prior query.template.source (.var query.names.result)
      caller state context origins pending principal atoms rows resolved readings.2.1
      (bound principal (resolve_sound resolved)) rfl snapshot decoded
    have same := ScopedMatchEntry.Result.captured.inj (captured.symm.trans actualCaptured)
    subst actual
    intro entry member
    rw [choices] at member
    obtain ⟨⟨position, marker⟩, _member, rfl⟩ := List.mem_map.mp member
    have resolvedAfter := CTLUntilScopedFrame.empty_capture_resolves caller (.var query.names.result)
      query.operandHandle query.satisfaction.2 query.template.source principal resolved
    have inherited := CTLUntilScopedFrame.capture_inherited caller (.var query.names.result)
      query.operandHandle query.satisfaction.2 query.template.source []
    exact Frame.publish _ resolvedAfter (fixed.inherited inherited) prior (bound.inherited inherited)

/-- Concrete three-phase instantiation of the caller-aware traversal law.
Live worlds may grow between sibling queries. Final decoding is a derived
conclusion, not a second admission premise. -/
theorem completed_decoded (codec : Codec Label) (label operand : Label) (round : Nat) (query : Query)
    (apart : query.names.prior ≠ query.names.next) (program : SpaceSemantics.Program)
    (caller : Control) (before after : State Context) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context)) (resolved : Resolved caller)
    (fixed : Fixed codec label operand round query caller)
    (nextFresh : FreshFor query.names.next caller.bindings) (priorFresh : FreshFor query.names.prior caller.bindings)
    (valid : Decoded codec query.handles before)
    (completed : (ScopedNestedQueryExecution.run program (GuardedNestedQuerySource.leaf program query.template Context)
      query.legs caller before context origins pending).stop = .complete after) :
    Decoded codec query.handles after := by
  exact ScopedNestedQueryExecution.run_preserves_family program
    (GuardedNestedQuerySource.leaf program query.template Context)
    (Frame codec label operand round query) (Decoded codec query.handles)
    (leaf_preserves codec label operand round query program query.handles)
    (capture_frame codec label operand round query apart program) query.legs
    caller before context origins pending after (Frame.frontier caller resolved fixed nextFresh priorFresh) valid completed

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilScopedRound
