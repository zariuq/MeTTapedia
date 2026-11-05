import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilAdmissionFrame

/-!
# Admission through actual live EU captures

Typed reads construct each phase's complete capture. Every selected child
retains the real handle-preparation equation, fresh output and temporary
slots, and its collapse-child destination. No final execution or expected
capture list is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCaptureAdmission

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open NamedGuardedCandidateBatch (State)
open FlatQueryRowCodec (Codec)
open CTLUntilScopedRound
open CTLUntilAdmissionFrame (AdmissionFrame)
open ClosedOnceQueryFrame (FreshFor)
open NestedQuerySource (Leg)

variable {Context Label : Type} [DecidableEq Label]

/-- Every typed phase reaches capture; no source execution or capacity
assumption is needed for this finite preparation-and-matching component. -/
theorem phase_capture_exists (codec : Codec Label) (label operand : Label) (round : Nat) (query : Query)
    (program : SpaceSemantics.Program) (leg : Leg) (rest : List Leg) (caller : Control) (state : State Context)
    (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (framed : Frame codec label operand round query (leg :: rest) caller)
    (valid : Decoded codec query.handles state) :
    ∃ selected, (ScopedMatchEntry.execute program leg.1 leg.2
      (ScopedNestedQueryExecution.source rest query.template.source) (.var query.names.result)
      caller state context origins pending).result = .captured selected := by
  cases framed with
  | frontier _ resolved fixed nextFresh _ =>
      obtain ⟨principal, resolved⟩ := resolved
      have readings := fixed principal (resolve_sound resolved)
      obtain ⟨atoms, rows, snapshot, decoded⟩ := valid query.frontierHandle (by simp [Query.handles])
      obtain ⟨_, selected, captured, _⟩ := CTLUntilScopedCapture.frontier_capture codec program query.frontierHandle
        label round query.names.formula query.currentRound query.names.next
        (ScopedNestedQueryExecution.source [query.edge, query.satisfaction] query.template.source) (.var query.names.result)
        caller state context origins pending principal atoms rows resolved readings.1 readings.2.2.1 nextFresh rfl snapshot decoded
      exact ⟨selected, captured⟩
  | edge _ resolved _ next bound priorFresh =>
      obtain ⟨principal, resolved⟩ := resolved
      obtain ⟨atoms, rows, snapshot, decoded⟩ := valid query.edgeHandle (by simp [Query.handles])
      obtain ⟨_, selected, captured, _⟩ := CTLUntilScopedCapture.edge_capture codec program query.edgeHandle next
        query.names.next query.names.prior
        (ScopedNestedQueryExecution.source [query.satisfaction] query.template.source) (.var query.names.result)
        caller state context origins pending principal atoms rows resolved (bound principal (resolve_sound resolved))
        priorFresh rfl snapshot decoded
      exact ⟨selected, captured⟩
  | satisfaction _ resolved fixed prior bound =>
      obtain ⟨principal, resolved⟩ := resolved
      have readings := fixed principal (resolve_sound resolved)
      obtain ⟨atoms, rows, snapshot, decoded⟩ := valid query.operandHandle (by simp [Query.handles])
      obtain ⟨_, selected, captured, _⟩ := CTLUntilScopedCapture.satisfaction_capture codec program query.operandHandle
        operand prior query.operand query.names.prior query.template.source (.var query.names.result)
        caller state context origins pending principal atoms rows resolved readings.2.1
        (bound principal (resolve_sound resolved)) rfl snapshot decoded
      exact ⟨selected, captured⟩

omit [DecidableEq Label] in
private theorem destination_retained (caller : Control) (result : String) (handle : NamedSpaces.Handle)
    (pattern body : Atom) : result ∈ (ScopedMatchPreparation.entry caller (.var result) handle pattern body).support := by
  apply GuardedInsertionPairSource.goal_atom_support _ (.var result) result
  · simp [ScopedMatchPreparation.entry, Goal.atoms]
  · simp [encode, Mettapedia.Logic.LP.Term.freeVars]

omit [DecidableEq Label] in
private theorem nested_retains_body (legs : List Leg) (body : Atom) (name : String)
    (used : name ∈ (encode body).freeVars) :
    name ∈ (encode (ScopedNestedQueryExecution.source legs body)).freeVars := by
  induction legs with
  | nil => exact used
  | cons leg rest ih =>
      rw [ScopedNestedQueryExecution.source, ScopedMatchPreparation.source, CapturedPatternSupport.mem_expression_names]
      exact ⟨ScopedNestedQueryExecution.source rest body, by simp, ih⟩

omit [DecidableEq Label] in
private theorem temporary_in_template (query : Query) :
    query.names.temporary ∈ (encode query.template.source).freeVars := by
  rw [GuardedNestedQuerySource.Template.source, CapturedPatternSupport.mem_expression_names]
  refine ⟨ScopedInsertionSequence.source query.template.body.temporary query.template.satisfactionHandle
    query.template.body.secondHandle query.template.body.firstCode query.template.body.secondCode, by simp, ?_⟩
  rw [ScopedInsertionSequence.source, CapturedPatternSupport.mem_expression_names]
  exact ⟨.var query.names.temporary, by simp [Query.template], by simp [encode, Mettapedia.Logic.LP.Term.freeVars]⟩

omit [DecidableEq Label] in
private theorem temporary_retained (query : Query) (caller : Control) (handle : NamedSpaces.Handle)
    (pattern : Atom) (rest : List Leg) :
    query.names.temporary ∈ (ScopedMatchPreparation.entry caller (.var query.names.result) handle pattern
      (ScopedNestedQueryExecution.source rest query.template.source)).support :=
  CTLUntilScopedCapture.body_name_retained caller (.var query.names.result) handle pattern _ query.names.temporary
    (nested_retains_body rest query.template.source query.names.temporary (temporary_in_template query))

/-- Admission is transported through the selected controls themselves. Both
fresh slots survive preparation, numeric row binding and literal filtering. -/
theorem capture_admission_frame (codec : Codec Label) (label operand : Label) (round : Nat) (query : Query)
    (distinct : [query.names.next, query.names.prior, query.names.result, query.names.temporary].Nodup)
    (program : SpaceSemantics.Program) (leg : Leg) (rest : List Leg) (caller : Control) (state : State Context)
    (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (selected : ScopedMatchEntry.Selection (ScopedNestedQueryExecution.source rest query.template.source)
      (.var query.names.result) caller.goals)
    (admitted : AdmissionFrame codec label operand round query (leg :: rest) caller)
    (valid : Decoded codec query.handles state)
    (captured : (ScopedMatchEntry.execute program leg.1 leg.2
      (ScopedNestedQueryExecution.source rest query.template.source) (.var query.names.result)
      caller state context origins pending).result = .captured selected) :
    ∀ entry ∈ selected.choices,
      AdmissionFrame codec label operand round query rest {entry.2 with goals := caller.goals} := by
  have names := distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at names
  have children := capture_frame codec label operand round query (by tauto) program leg rest caller state context origins pending
    selected admitted.frame valid captured
  obtain ⟨framed, resultFresh, temporaryFresh, finished, output⟩ := admitted
  cases framed with
  | frontier _ resolved fixed nextFresh _ =>
      obtain ⟨principal, resolved⟩ := resolved
      have readings := fixed principal (resolve_sound resolved)
      obtain ⟨atoms, rows, snapshot, decoded⟩ := valid query.frontierHandle (by simp [Query.handles])
      let body := ScopedNestedQueryExecution.source [query.edge, query.satisfaction] query.template.source
      obtain ⟨_, actual, actualCaptured, choices⟩ := CTLUntilScopedCapture.frontier_capture codec program query.frontierHandle
        label round query.names.formula query.currentRound query.names.next body (.var query.names.result)
        caller state context origins pending principal atoms rows resolved readings.1 readings.2.2.1 nextFresh rfl snapshot decoded
      have same := ScopedMatchEntry.Result.captured.inj (captured.symm.trans actualCaptured)
      subst actual
      intro entry member
      have frame := children entry member
      rw [choices] at member
      obtain ⟨⟨position, next⟩, _, rfl⟩ := List.mem_map.mp member
      refine ⟨frame, ?_, ?_, finished, ?_⟩
      · exact CTLUntilScopedFrame.number_capture_fresh caller (.var query.names.result) query.frontierHandle
          query.frontier.2 body query.names.next query.names.result next resultFresh
          (destination_retained caller query.names.result query.frontierHandle query.frontier.2 body) (by tauto)
      · exact CTLUntilScopedFrame.number_capture_fresh caller (.var query.names.result) query.frontierHandle
          query.frontier.2 body query.names.next query.names.temporary next temporaryFresh
          (temporary_retained query caller query.frontierHandle query.frontier.2 [query.edge, query.satisfaction]) (by tauto)
      · exact output
  | edge _ resolved _ next bound priorFresh =>
      obtain ⟨principal, resolved⟩ := resolved
      obtain ⟨atoms, rows, snapshot, decoded⟩ := valid query.edgeHandle (by simp [Query.handles])
      let body := ScopedNestedQueryExecution.source [query.satisfaction] query.template.source
      obtain ⟨_, actual, actualCaptured, choices⟩ := CTLUntilScopedCapture.edge_capture codec program query.edgeHandle next
        query.names.next query.names.prior body (.var query.names.result)
        caller state context origins pending principal atoms rows resolved (bound principal (resolve_sound resolved))
        priorFresh rfl snapshot decoded
      have same := ScopedMatchEntry.Result.captured.inj (captured.symm.trans actualCaptured)
      subst actual
      intro entry member
      have frame := children entry member
      rw [choices] at member
      obtain ⟨⟨position, prior⟩, _, rfl⟩ := List.mem_map.mp member
      refine ⟨frame, ?_, ?_, finished, ?_⟩
      · exact CTLUntilScopedFrame.number_capture_fresh caller (.var query.names.result) query.edgeHandle
          query.edge.2 body query.names.prior query.names.result prior resultFresh
          (destination_retained caller query.names.result query.edgeHandle query.edge.2 body) (by tauto)
      · exact CTLUntilScopedFrame.number_capture_fresh caller (.var query.names.result) query.edgeHandle
          query.edge.2 body query.names.prior query.names.temporary prior temporaryFresh
          (temporary_retained query caller query.edgeHandle query.edge.2 [query.satisfaction]) (by tauto)
      · exact output
  | satisfaction _ resolved fixed prior bound =>
      obtain ⟨principal, resolved⟩ := resolved
      have readings := fixed principal (resolve_sound resolved)
      obtain ⟨atoms, rows, snapshot, decoded⟩ := valid query.operandHandle (by simp [Query.handles])
      obtain ⟨_, actual, actualCaptured, choices⟩ := CTLUntilScopedCapture.satisfaction_capture codec program query.operandHandle
        operand prior query.operand query.names.prior query.template.source (.var query.names.result)
        caller state context origins pending principal atoms rows resolved readings.2.1
        (bound principal (resolve_sound resolved)) rfl snapshot decoded
      have same := ScopedMatchEntry.Result.captured.inj (captured.symm.trans actualCaptured)
      subst actual
      intro entry member
      have frame := children entry member
      rw [choices] at member
      obtain ⟨⟨position, marker⟩, _, rfl⟩ := List.mem_map.mp member
      refine ⟨frame, ?_, ?_, finished, ?_⟩
      · exact CTLUntilScopedFrame.empty_capture_fresh caller (.var query.names.result) query.operandHandle
          query.satisfaction.2 query.template.source query.names.result resultFresh
          (destination_retained caller query.names.result query.operandHandle query.satisfaction.2 query.template.source)
      · exact CTLUntilScopedFrame.empty_capture_fresh caller (.var query.names.result) query.operandHandle
          query.satisfaction.2 query.template.source query.names.temporary temporaryFresh
          (temporary_retained query caller query.operandHandle query.satisfaction.2 [])
      · exact output

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCaptureAdmission

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCaptureAdmission.phase_capture_exists
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCaptureAdmission.capture_admission_frame
