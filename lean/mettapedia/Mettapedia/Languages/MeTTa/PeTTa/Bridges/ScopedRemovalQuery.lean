import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedRemovalExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCleanup
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilScopedFrame

/-!
# Live captured cleanup queries

The actual capture determines the ordered producer list. Each removal then
uses the current store left by the preceding producer. Readability and closed
candidate admission survive deletion by filtering, including repeated
payloads which have already disappeared from the target. Each packet carries
the reply of its own removal, so a repeated payload's later removals reply
false.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedRemovalQuery

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open NamedGuardedCandidateBatch (State)
open ScopedNestedQueryExecution (Execution Stop Leaf visit run)
open ClosedOnceQueryFrame (FreshFor)
open FlatQueryRowCodec (Codec)
open CTLUntilMixedStore (Row render decodeRows frontSelect)
open CTLUntilSourceRows (number located)

variable {Context : Type}

/-- State-independent facts retained by a captured source control. -/
structure Frame (result : String) (payloadCode : Atom) (caller : Control) (payload : Atom) : Prop where
  finished : caller.goals = []
  output : caller.destination = .var result
  fresh : FreshFor result caller.bindings
  resolved : ∃ principal, resolve caller.bindings = some principal ∧ read principal payloadCode = payload
  literal : SpaceSemantics.Literal payload
  ordinary : ScopedQuerySource.mutationPayload true payload = true

/-- The replies of successive removals of `payloads` from the target `rows`.
Each removal reads the rows its predecessors left. -/
def replies (rows : List Atom) : List Atom → List Bool
  | [] => []
  | payload :: payloads =>
      rows.any (Effects.removalMatches payload) ::
        replies (rows.filter fun row => !Effects.removalMatches payload row) payloads

@[simp] theorem replies_length (rows payloads : List Atom) : (replies rows payloads).length = payloads.length := by
  induction payloads generalizing rows with
  | nil => rfl
  | cons payload payloads ih => simp [replies, ih]

/-- The reply of one erasure, computed from the rows it reads. -/
theorem erasure_reply {before after : Effects.State} {handle : NamedSpaces.Handle} {payload : Atom}
    {rows : List Atom} (snapshot : before.read handle = some rows)
    (erased : Effects.erase before handle payload = some after) :
    Effects.erasureChanged before after handle = rows.any (Effects.removalMatches payload) :=
  Bool.eq_iff_iff.mpr ((Effects.erasureChanged_iff snapshot erased).trans List.any_eq_true.symm)

/-- The packets of the captured removals, each carrying the reply of its
erasure in the rows left by the preceding producers. -/
def packets (result : String) (handle : NamedSpaces.Handle) (payloadCode : Atom)
    (older : List Goal) (origins : List Nat) (selected : List (Nat × Control)) (payloads rows : List Atom) :
    List CollectedAnswer :=
  List.zipWith (fun entry changed => ScopedRemovalExecution.packet result handle payloadCode
    {entry.2 with goals := older} (origins ++ [entry.1]) changed) selected (replies rows payloads)

theorem packets_length (result : String) (handle : NamedSpaces.Handle) (payloadCode : Atom)
    (older : List Goal) (origins : List Nat) (selected : List (Nat × Control)) (payloads rows : List Atom)
    (same : selected.length = payloads.length) :
    (packets result handle payloadCode older origins selected payloads rows).length = selected.length := by
  simp [packets, same]

theorem packets_values (result : String) (handle : NamedSpaces.Handle) (payloadCode : Atom)
    (older : List Goal) (origins : List Nat) (selected : List (Nat × Control)) (payloads rows : List Atom)
    (same : selected.length = payloads.length) :
    (packets result handle payloadCode older origins selected payloads rows).map CollectedAnswer.value =
        (replies rows payloads).map Effects.boolean ∧
      ∀ packet ∈ packets result handle payloadCode older origins selected payloads rows,
        ∃ changed, packet.value = Effects.boolean changed ∧ packet.associated = [] := by
  induction selected generalizing payloads rows with
  | nil =>
      cases payloads with
      | nil => simp [packets, replies]
      | cons => simp at same
  | cons entry selected ih =>
      cases payloads with
      | nil => simp at same
      | cons payload payloads =>
          obtain ⟨values, rest⟩ := ih payloads (rows.filter fun row => !Effects.removalMatches payload row)
            (Nat.succ.inj same)
          refine ⟨by simpa [packets, replies, ScopedRemovalExecution.packet] using values, ?_⟩
          intro packet member
          simp only [packets, replies, List.zipWith_cons_cons, List.mem_cons] at member
          rcases member with rfl | later
          · exact ⟨_, rfl, rfl⟩
          · exact rest packet later

theorem framed_complete (program : SpaceSemantics.Program) (result : String) (handle : NamedSpaces.Handle)
    (payloadCode : Atom) (caller : Control) (state : State Context) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (payload : Atom) (rows : List Atom)
    (framed : Frame result payloadCode caller payload) (snapshot : state.world.state.read handle = some rows)
    (ready : ClosedQueryAdmission.rowsReady payload rows = true) :
    ∃ after, Effects.erase state.world.state handle payload = some after ∧
      (ScopedRemovalExecution.leaf program result handle payloadCode Context).execute caller state context origins pending =
        ⟨6, ScopedRemovalExecution.events result handle payloadCode caller origins state after,
          .complete (ScopedRemovalExecution.advance result handle payloadCode caller origins state after)⟩ := by
  obtain ⟨principal, resolved, reading⟩ := framed.resolved
  obtain ⟨evidence, prepared⟩ := ScopedRemovalExecution.prepare_complete result handle payloadCode caller state
    principal payload rows framed.finished framed.output framed.fresh resolved reading framed.literal framed.ordinary snapshot ready
  have samePrincipal : evidence.principal = principal := Option.some.inj (evidence.resolved.symm.trans resolved)
  have samePayload : evidence.payload = payload := by
    rw [← evidence.reading, samePrincipal, reading]
  obtain ⟨after, erased, executed⟩ := ScopedRemovalExecution.execute_prepared program result handle payloadCode
    caller state context origins pending evidence prepared
  rw [samePayload] at erased
  exact ⟨after, erased, executed⟩

private theorem ready_filter (payload : Atom) (rows : List Atom) (predicate : Atom → Bool)
    (ready : ClosedQueryAdmission.rowsReady payload rows = true) :
    ClosedQueryAdmission.rowsReady payload (rows.filter predicate) = true := by
  apply List.all_eq_true.mpr
  intro row member
  exact List.all_eq_true.mp ready row (List.mem_filter.mp member).1

/-- Completion is derived along the existing live traversal. The auxiliary
erasure fold describes its final store; it does not execute the source. -/
theorem visit_complete (program : SpaceSemantics.Program) (result : String) (handle : NamedSpaces.Handle)
    (payloadCode : Atom) (older : List Goal) (context : Context) (origins : List Nat)
    (selected : List (Nat × Control)) (payloads : List Atom)
    (frames : List.Forall₂ (fun entry payload => Frame result payloadCode {entry.2 with goals := older} payload) selected payloads)
    (state : State Context) (pending : List (CollectionWork Context)) (rows : List Atom)
    (snapshot : state.world.state.read handle = some rows)
    (ready : ∀ payload ∈ payloads, ClosedQueryAdmission.rowsReady payload rows = true) :
    ∃ after,
      (visit (ScopedRemovalExecution.leaf program result handle payloadCode Context).execute older context origins selected state pending).stop = .complete after ∧
      QueryBagErasure.eraseRows handle payloads state.world.state = some after.world.state ∧
      after.allocator = state.allocator ∧
      after.scope.collected = state.scope.collected ++ packets result handle payloadCode older origins selected payloads rows ∧
      after.scope.caller = state.scope.caller ∧ after.parents = state.parents ∧
      (visit (ScopedRemovalExecution.leaf program result handle payloadCode Context).execute older context origins selected state pending).events =
        (if state.scope.caller.isNone then packets result handle payloadCode older origins selected payloads rows else []) := by
  induction frames generalizing state pending rows with
  | nil => exact ⟨state, rfl, rfl, rfl, by simp [packets, replies], rfl, rfl, by simp [visit, packets, replies]⟩
  | @cons entry payload entries payloads framed frames ih =>
    let caller := {entry.2 with goals := older}
    let tail := ScopedQuerySource.work context origins entries ++ pending
    obtain ⟨erasedState, erased, executed⟩ := framed_complete program result handle payloadCode caller state context
      (origins ++ [entry.1]) tail payload rows framed snapshot (ready payload List.mem_cons_self)
    let middle := ScopedRemovalExecution.advance result handle payloadCode caller (origins ++ [entry.1]) state erasedState
    obtain ⟨oldRows, oldRead, nextRead⟩ := Effects.erase_reads_back erased
    have sameRows : oldRows = rows := Option.some.inj (oldRead.symm.trans snapshot)
    subst oldRows
    have reply := erasure_reply snapshot erased
    obtain ⟨after, completed, erasedRest, allocator, collected, saved, parents, emitted⟩ :=
      ih middle pending (rows.filter fun row => !Effects.removalMatches payload row) nextRead
        (fun value member => ready_filter value rows _ (ready value (List.mem_cons_of_mem _ member)))
    refine ⟨after, ?_, ?_, allocator, ?_, saved, parents, ?_⟩
    · simp only [visit, caller, tail] at executed ⊢
      rw [executed]
      exact completed
    · simp only [QueryBagErasure.eraseRows, erased, Option.bind_some]
      exact erasedRest
    · simpa only [middle, ScopedRemovalExecution.advance, packets, replies, reply, List.zipWith_cons_cons,
        List.append_assoc, List.singleton_append] using collected
    · simp only [visit, caller, tail] at executed ⊢
      rw [executed]
      dsimp only
      rw [emitted]
      simp only [middle, ScopedRemovalExecution.advance, ScopedRemovalExecution.events, packets, replies, reply,
        List.zipWith_cons_cons]
      split <;> simp_all only [List.singleton_append, List.nil_append]

private theorem destination_retained (caller : Control) (result : String) (handle : NamedSpaces.Handle)
    (pattern body : Atom) : result ∈ (ScopedMatchPreparation.entry caller (.var result) handle pattern body).support := by
  apply GuardedInsertionPairSource.goal_atom_support _ (.var result) result
  · simp [ScopedMatchPreparation.entry, Goal.atoms]
  · simp [encode, Mettapedia.Logic.LP.Term.freeVars]

private theorem node_retained (caller : Control) (result : String) (handle : NamedSpaces.Handle)
    (formulaName roundName nodeName : String) (body : Atom) :
    nodeName ∈ (ScopedMatchPreparation.entry caller (.var result) handle
      (CTLUntilScopedCapture.frontierCode formulaName roundName nodeName) body).support := by
  apply CTLUntilScopedCapture.pattern_name_retained
  rw [CTLUntilScopedCapture.frontierCode, CapturedPatternSupport.mem_expression_names]
  exact ⟨.var nodeName, by simp, by simp [encode, Mettapedia.Logic.LP.Term.freeVars]⟩

theorem frontier_frame {Label : Type} (codec : Codec Label) (label : Label) (round node : Nat)
    (result formulaName roundName nodeName : String) (handle : NamedSpaces.Handle) (caller : Control)
    (principal : Environment) (resolved : resolve caller.bindings = some principal)
    (formulaRead : read principal (.var formulaName) = codec.encode label)
    (roundRead : read principal (.var roundName) = number round)
    (nodeFresh : FreshFor nodeName caller.bindings) (resultFresh : FreshFor result caller.bindings)
    (apart : result ≠ nodeName) (finished : caller.goals = []) (output : caller.destination = .var result) :
    let pattern := CTLUntilScopedCapture.frontierCode formulaName roundName nodeName
    let body := ScopedRemovalSource.source handle pattern
    let ready := ScopedMatchPreparation.ready caller (.var result) handle pattern body
    Frame result pattern
      {ScopedQuerySource.bodyControl ready [(nodeName, number node)] body (.var result) caller.goals with goals := caller.goals}
      (render codec (.frontier label round node)) := by
  dsimp only
  let pattern := CTLUntilScopedCapture.frontierCode formulaName roundName nodeName
  let body := ScopedRemovalSource.source handle pattern
  obtain ⟨environment, found⟩ := CTLUntilScopedFrame.number_capture_resolves caller (.var result) handle pattern body
    nodeName node principal resolved nodeFresh (node_retained caller result handle formulaName roundName nodeName body)
  have formulaAfter := CTLUntilScopedFrame.capture_closed_reading caller (.var result) handle pattern body
    [(nodeName, number node)] principal environment (.var formulaName) (codec.encode label) resolved found formulaRead
    (LiteralQuerySource.read_literal _ (codec.literal label))
  have roundAfter := CTLUntilScopedFrame.capture_closed_reading caller (.var result) handle pattern body
    [(nodeName, number node)] principal environment (.var roundName) (number round) resolved found roundRead
    (CTLUntilSourceCapture.number_closed round)
  have nodeAfter := CTLUntilScopedFrame.number_capture_read caller (.var result) handle pattern body nodeName node environment found
  refine ⟨finished, output, ?_, ⟨environment, found, ?_⟩,
    CTLUntilPublicationSource.frontier_literal codec label round node, ?_⟩
  · exact CTLUntilScopedFrame.number_capture_fresh caller (.var result) handle pattern body nodeName result node
      resultFresh (destination_retained caller result handle pattern body) apart
  · simp only [read_eq_applyTypeValuation, HE.Spec.Type.RuntimeRefinement.applyTypeValuation] at formulaAfter roundAfter nodeAfter
    simp only [CTLUntilScopedCapture.frontierCode, render, read_eq_applyTypeValuation,
      HE.Spec.Type.RuntimeRefinement.applyTypeValuation, List.map_cons, List.map_nil, formulaAfter, roundAfter, nodeAfter]
  · exact CTLUntilPublicationSource.frontier_ordinary codec label round node

/-- The current frontier payloads, in capture order, including repeats. -/
def frontierPayloads {Label : Type} [DecidableEq Label] (codec : Codec Label) (label : Label) (round : Nat)
    (rows : List (Row Label)) : List Atom :=
  (rows.filterMap (frontSelect label round)).map fun node => render codec (.frontier label round node)

/-- The raw single-query cleanup completes through the actual live executor.
Its captured producer count, the replies its packets carry and its final
typed filter are all derived. -/
theorem frontier_complete {Label : Type} [DecidableEq Label] (codec : Codec Label) (label : Label) (round : Nat)
    (program : SpaceSemantics.Program) (result formulaName roundName nodeName : String) (handle : NamedSpaces.Handle)
    (caller : Control) (state : State Context) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (principal : Environment) (atoms : List Atom) (rows : List (Row Label))
    (resolved : resolve caller.bindings = some principal)
    (formulaRead : read principal (.var formulaName) = codec.encode label)
    (roundRead : read principal (.var roundName) = number round)
    (nodeFresh : FreshFor nodeName caller.bindings) (resultFresh : FreshFor result caller.bindings)
    (apart : result ≠ nodeName) (finished : caller.goals = []) (output : caller.destination = .var result)
    (snapshot : state.world.state.read handle = some atoms) (decoded : decodeRows codec atoms = some rows) :
    let pattern := CTLUntilScopedCapture.frontierCode formulaName roundName nodeName
    let worker := run program (ScopedRemovalExecution.leaf program result handle pattern Context) [(handle, pattern)]
    ∃ after,
      (worker caller state context origins pending).stop = .complete after ∧
      after.world.state.read handle = some ((CTLUntilCleanup.remaining label round rows).map (render codec)) ∧
      decodeRows codec ((CTLUntilCleanup.remaining label round rows).map (render codec)) =
        some (CTLUntilCleanup.remaining label round rows) ∧
      after.scope.collected.length = state.scope.collected.length + (rows.filterMap (frontSelect label round)).length ∧
      (∃ added, after.scope.collected = state.scope.collected ++ added ∧
        added.map CollectedAnswer.value = (replies atoms (frontierPayloads codec label round rows)).map Effects.boolean ∧
        ∀ packet ∈ added, packet.associated = []) ∧
      (∀ other, other ≠ handle → after.world.state.read other = state.world.state.read other) ∧
      after.world.state.cells = state.world.state.cells ∧ after.allocator = state.allocator ∧
      after.scope.caller = state.scope.caller ∧ after.parents = state.parents ∧
      (state.scope.caller.isSome = true → (worker caller state context origins pending).events = []) := by
  dsimp only
  let pattern := CTLUntilScopedCapture.frontierCode formulaName roundName nodeName
  let body := ScopedRemovalSource.source handle pattern
  let ready := ScopedMatchPreparation.ready caller (.var result) handle pattern body
  let leaf := ScopedRemovalExecution.leaf program result handle pattern Context
  obtain ⟨_, selected, captured, choices⟩ := CTLUntilScopedCapture.frontier_capture codec program handle label round
    formulaName roundName nodeName body (.var result) caller state context origins pending principal atoms rows
    resolved formulaRead roundRead nodeFresh rfl snapshot decoded
  let payloads := frontierPayloads codec label round rows
  have words : payloads = (located (frontSelect label round) 0 rows).map
      (fun entry => render codec (.frontier label round entry.2)) :=
    (CTLUntilSourceRows.located_map (frontSelect label round) 0 rows
      (fun node => render codec (.frontier label round node))).symm
  have frames : List.Forall₂ (fun entry payload => Frame result pattern {entry.2 with goals := caller.goals} payload)
      selected.choices payloads := by
    rw [choices, words]
    induction located (frontSelect label round) 0 rows with
    | nil => exact .nil
    | cons entry rest ih =>
        exact .cons (frontier_frame codec label round entry.2 result formulaName roundName nodeName handle caller principal resolved
          formulaRead roundRead nodeFresh resultFresh apart finished output) ih
  obtain ⟨rendered, admitted⟩ := CTLUntilMixedStore.decode_rows_sound codec atoms rows decoded
  have allReady : ∀ payload ∈ payloads, ClosedQueryAdmission.rowsReady payload atoms = true := by
    intro payload member
    obtain ⟨node, _, rfl⟩ := List.mem_map.mp member
    rw [← rendered]
    exact CTLUntilMixedStore.rows_ready codec "fr" _ (by simp) rows admitted
  obtain ⟨after, completed, erased, allocator, collected, saved, parents, emitted⟩ :=
    visit_complete program result handle pattern caller.goals context origins selected.choices payloads frames state pending atoms snapshot allReady
  have actual : (run program leaf [(handle, pattern)] caller state context origins pending).stop = .complete after := by
    simp only [run, leaf, ScopedRemovalExecution.leaf, ScopedNestedQueryExecution.source] at captured ⊢
    rw [captured]
    exact completed
  obtain ⟨reading, others, cells⟩ := QueryBagErasure.eraseRows_receipt handle payloads state.world.state after.world.state atoms snapshot erased
  have length := List.Forall₂.length_eq frames
  obtain ⟨values, flat⟩ := packets_values result handle pattern caller.goals origins selected.choices payloads atoms length
  refine ⟨after, actual, ?_, CTLUntilMixedStore.decode_rows_complete codec _
    (CTLUntilCleanup.remaining_admitted label round rows admitted), ?_,
    ⟨_, collected, values, fun packet member => (flat packet member).choose_spec.2⟩,
    others, cells, allocator, saved, parents, ?_⟩
  · rw [reading, ← rendered]
    exact congrArg some (CTLUntilCleanup.retained_exact codec label round rows admitted)
  · rw [collected, List.length_append, packets_length _ _ _ _ _ _ _ _ length]
    simpa only [payloads, frontierPayloads, List.length_map] using congrArg (state.scope.collected.length + ·) length
  · intro nested
    simp only [run, ScopedRemovalExecution.leaf, ScopedNestedQueryExecution.source] at captured ⊢
    rw [captured]
    dsimp only
    change (visit (ScopedRemovalExecution.leaf program result handle pattern Context).execute
      caller.goals context origins selected.choices state pending).events = []
    rw [emitted]
    cases parent : state.scope.caller <;> simp_all

namespace Controls

open ScopedRemovalSource.Controls (fact)

private theorem fact_matches : Effects.removalMatches fact fact = true := Effects.removalMatches_self _ _

/-- Positive: removing a present payload replies true, however many copies it removes. -/
theorem present_payload_replies_true : replies [fact, fact] [fact] = [true] := by
  simp [replies, fact_matches]

/-- Negative: the second removal of a repeated payload finds nothing and replies false. -/
theorem repeated_payload_replies_false : replies [fact] [fact, fact] = [true, false] := by
  simp [replies, fact_matches]

/-- The live packets carry these replies in capture order. -/
theorem repeated_payload_packets (result : String) (handle : NamedSpaces.Handle) (payloadCode : Atom)
    (older : List Goal) (origins : List Nat) (first second : Nat × Control) :
    (packets result handle payloadCode older origins [first, second] [fact, fact] [fact]).map CollectedAnswer.value =
      [Effects.boolean true, Effects.boolean false] := by
  rw [(packets_values result handle payloadCode older origins [first, second] [fact, fact] [fact] rfl).1,
    repeated_payload_replies_false]
  rfl

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedRemovalQuery
