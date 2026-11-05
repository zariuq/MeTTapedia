import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCountedCleanup
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedInsertionSequence

/-!
# Occurrence-preserving EU source seeding

The initial goal query is captured once. Every captured occurrence appends a
satisfaction row and then its round-zero frontier row, without a membership
guard. Collection and numeric return use the actual scoped source machine.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSeedSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open NamedGuardedCandidateBatch (State)
open FlatQueryRowCodec (Codec)
open ClosedOnceQueryFrame (FreshFor placed)
open CTLUntilMixedStore (Row render decodeRows satisfactionView satisfactionPattern)
open CTLUntilSourceRows (number located)
open CountedSourceEntry (Input)

variable {Context Label : Type} [DecidableEq Label]

def seedRows (label : Label) (node : Nat) : List (Row Label) :=
  [.satisfaction label node, .frontier label 0 node]

def firstCode (formula node : String) : Atom := NamedPresenceSource.patternCode formula node
def secondCode (formula node : String) : Atom :=
  .expression [.symbol "fr", .var formula, number 0, .var node]
def pairBody (handle : NamedSpaces.Handle) (formula node temporary : String) : Atom :=
  ScopedInsertionSequence.source temporary handle handle (firstCode formula node) (secondCode formula node)
def body (handle : NamedSpaces.Handle) (formula goal node temporary : String) : Atom :=
  ScopedMatchPreparation.source handle (NamedPresenceSource.patternCode goal node)
    (pairBody handle formula node temporary)

def select (label : Label) : Row Label → Option Nat
  | .satisfaction other node => if other = label then some node else none
  | _ => none

theorem select_values (label : Label) (rows : List (Row Label)) :
    rows.filterMap (select label) = satisfactionView label rows := rfl

theorem selected_match (codec : Codec Label) (label : Label) (slot : String)
    (row : Row Label) (admitted : row.admitted) :
    SpaceSemantics.matchValue [] (satisfactionPattern codec label slot) (render codec row) =
      (select label row).map (fun node => [(slot, number node)]) := by
  cases row with
  | frontier => exact CTLUntilMixedStore.different_head [] "sat" "fr" _ _ (by decide) (by decide)
  | edge => exact CTLUntilMixedStore.different_head [] "sat" "rt" _ _ (by decide) (by decide)
  | satisfaction other node =>
      unfold satisfactionPattern render
      rw [SpaceSemantics.matchValue_expression_of_not_cons _ _ _ (by simp)]
      by_cases same : other = label
      · subst other
        simp [SpaceSemantics.matchValue.matchValues, SpaceSemantics.matchValue_literal (codec.literal label),
          SpaceSemantics.matchValue, Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup,
          Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, number, select]
      · simp [SpaceSemantics.matchValue.matchValues, SpaceSemantics.matchValue_literal (codec.literal label),
          codec.injective.eq_iff, SpaceSemantics.matchValue,
          Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, select, same, Ne.symm same]
  | other head children => exact CTLUntilMixedStore.different_head [] "sat" head _ _ (by decide) (Ne.symm admitted.2.2)

theorem capture (codec : Codec Label) (goal : Label) (program : SpaceSemantics.Program)
    (handle : NamedSpaces.Handle) (goalName nodeName : String) (child destination : Atom)
    (caller : Control) (state : State Context) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context)) (principal : Environment) (atoms : List Atom) (rows : List (Row Label))
    (resolved : resolve caller.bindings = some principal)
    (goalRead : read principal (.var goalName) = codec.encode goal) (fresh : FreshFor nodeName caller.bindings)
    (nonscalar : ConstantQuerySource.isScalar child = false)
    (snapshot : state.world.state.read handle = some atoms) (decoded : decodeRows codec atoms = some rows) :
    let pattern := NamedPresenceSource.patternCode goalName nodeName
    let ready := ScopedMatchPreparation.ready caller destination handle pattern child
    (ScopedMatchEntry.execute program handle pattern child destination caller state context origins pending).budget = 4 ∧
      ∃ selected, (ScopedMatchEntry.execute program handle pattern child destination caller state context origins pending).result = .captured selected ∧
        selected.choices = (located (select goal) 0 rows).map
          (fun entry => (entry.1, ScopedQuerySource.bodyControl ready [(nodeName, number entry.2)] child destination caller.goals)) := by
  dsimp only
  let pattern := NamedPresenceSource.patternCode goalName nodeName
  let ready := ScopedMatchPreparation.ready caller destination handle pattern child
  obtain ⟨environment, prepared⟩ := resolve_complete
    (ScopedMatchPreparation.ready_consistent caller destination handle pattern child ⟨principal, resolve_sound resolved⟩)
  have inherited := ScopedMatchPreparation.closed_reading caller destination handle pattern child principal environment
    (.var goalName) (codec.encode goal) resolved prepared goalRead (LiteralQuerySource.read_literal _ (codec.literal goal))
  have retained := CTLUntilScopedCapture.pattern_name_retained caller destination handle pattern child nodeName (by
    dsimp only [pattern]
    rw [NamedPresenceSource.patternCode, CapturedPatternSupport.mem_expression_names]
    exact ⟨.var nodeName, by simp, by simp [encode, Mettapedia.Logic.LP.Term.freeVars]⟩)
  have nodeRead := ClosedOnceQueryFrame.fresh_read ready.bindings nodeName environment
    (ScopedMatchPreparation.retained_fresh caller destination handle pattern child nodeName fresh retained) prepared
  have patternRead : read environment pattern = satisfactionPattern codec goal nodeName := by
    simp only [read_eq_applyTypeValuation, HE.Spec.Type.RuntimeRefinement.applyTypeValuation] at inherited nodeRead
    simp only [pattern, NamedPresenceSource.patternCode, satisfactionPattern, read_eq_applyTypeValuation,
      HE.Spec.Type.RuntimeRefinement.applyTypeValuation, List.map_cons, List.map_nil, inherited, nodeRead]
  obtain ⟨rendered, admitted⟩ := CTLUntilMixedStore.decode_rows_sound codec atoms rows decoded
  have actual := CTLUntilMixedCapture.single_capture codec (select goal) _ nodeName
    (selected_match codec goal nodeName) ready environment nodeName child destination caller.goals 0 rows admitted prepared nodeRead
  apply ScopedMatchEntry.captured_of_checks program handle pattern child destination caller state context origins pending
    principal environment atoms _ resolved prepared snapshot
  · rw [patternRead, ← rendered]
    exact CTLUntilMixedStore.rows_ready codec "sat" _ (by simp) rows admitted
  · simp [ScopedQuerySource.fused, nonscalar]
  · rw [patternRead, ← rendered]
    exact actual

structure Frame (codec : Codec Label) (label : Label) (handle : NamedSpaces.Handle)
    (result formula node temporary : String) (caller : Control) (value : Nat) : Prop where
  finished : caller.goals = []
  output : caller.destination = .var result
  resultFresh : FreshFor result caller.bindings
  temporaryFresh : FreshFor temporary caller.bindings
  distinct : temporary ≠ result
  resolved : ∃ principal, resolve caller.bindings = some principal ∧
    read principal (firstCode formula node) = render codec (.satisfaction label value) ∧
    read principal (secondCode formula node) = render codec (.frontier label 0 value)

def packet (result formula node temporary : String) (handle : NamedSpaces.Handle)
    (caller : Control) (origins : List Nat) : CollectedAnswer :=
  ⟨Effects.boolean true, (ScopedInsertionSequence.returned caller result temporary handle handle
    (firstCode formula node) (secondCode formula node)).bindings, origins ++ [0, 0], []⟩

def advanced (result formula node temporary : String) (handle : NamedSpaces.Handle)
    (caller : Control) (origins : List Nat) (state : State Context) (after : Effects.State) : State Context :=
  {state with
    world := {state.world with state := after}
    scope := {state.scope with collected := state.scope.collected ++ [packet result formula node temporary handle caller origins]}}

omit [DecidableEq Label] in
theorem row_prefix (codec : Codec Label) (label : Label) (program : SpaceSemantics.Program)
    (handle : NamedSpaces.Handle) (result formula node temporary : String)
    (caller : Control) (state : State Context) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context)) (value : Nat)
    (framed : Frame codec label handle result formula node temporary caller value)
    (middle after : Effects.State)
    (first : Effects.insert state.world.state handle (render codec (.satisfaction label value)) = some middle)
    (second : Effects.insert middle handle (render codec (.frontier label 0 value)) = some after) :
    (ScopedQuerySource.machine .relational program).run 14
      (ScopedMatchEntry.entrance (pairBody handle formula node temporary) (.var result) caller state context origins pending) =
      ((if state.scope.caller.isNone then [packet result formula node temporary handle caller origins] else []),
        .exhausted ((advanced result formula node temporary handle caller origins state after).cursor pending)) := by
  obtain ⟨principal, resolved, firstRead, secondRead⟩ := framed.resolved
  let returned := ScopedInsertionSequence.returned caller result temporary handle handle (firstCode formula node) (secondCode formula node)
  let answer := packet result formula node temporary handle caller origins
  let finalCursor := (advanced result formula node temporary handle caller origins state after).cursor pending
  obtain ⟨environment, found⟩ := resolve_complete
    (ScopedInsertionSequence.returned_consistent caller result temporary handle handle _ _ principal resolved
      framed.temporaryFresh framed.resultFresh framed.distinct)
  have valueRead := ScopedInsertionSequence.returned_value caller result temporary handle handle _ _ environment (resolve_sound found)
  have terminal : returned.goals = [] := framed.finished
  have outputRead : read environment returned.destination = Effects.boolean true := by
    change read environment caller.destination = Effects.boolean true
    rw [framed.output]
    exact valueRead
  have last : (ScopedQuerySource.machine .relational program).step
      (placed state.allocator {state.world with state := after} state.scope state.parents returned context (origins ++ [0, 0]) pending) =
      some (if state.scope.caller.isNone then .publish [answer] finalCursor else .silent finalCursor) := by
    simp only [placed]
    rw [ScopedQuerySource.Guards.empty_goals_step .relational program state.allocator {state.world with state := after}
      {state.scope with frontier := (returned, context, origins ++ [0, 0]) :: pending}
      state.parents returned context (origins ++ [0, 0]) pending rfl terminal]
    have delivered := scope_terminal_value .relational program state.allocator {state.world with state := after}
      {state.scope with frontier := (returned, context, origins ++ [0, 0]) :: pending}
      state.parents returned context (origins ++ [0, 0]) pending environment rfl terminal found
    simp only [outputRead] at delivered
    simpa [answer, packet, returned, finalCursor, advanced, State.cursor, EagerDFS.Scope.record] using congrArg some delivered
  have finalStep : (ScopedQuerySource.machine .relational program).run 1
      (placed state.allocator {state.world with state := after} state.scope state.parents returned context (origins ++ [0, 0]) pending) =
      ((if state.scope.caller.isNone then [answer] else []), .exhausted finalCursor) := by
    cases parent : state.scope.caller <;> simp [Machine.run, last, parent]
  have started := ScopedInsertionSequence.source_prefix program state.allocator state.world state.scope state.parents caller context
    origins pending result temporary handle handle (firstCode formula node) (secondCode formula node)
    (render codec (.satisfaction label value)) (render codec (.frontier label 0 value)) principal middle after resolved
    framed.temporaryFresh framed.resultFresh framed.distinct firstRead secondRead
    (LiteralQuerySource.read_literal _ (CTLUntilPublicationSource.satisfaction_literal codec label value))
    (LiteralQuerySource.read_literal _ (CTLUntilPublicationSource.frontier_literal codec label 0 value))
    (CTLUntilPublicationSource.satisfaction_ordinary codec label value)
    (CTLUntilPublicationSource.frontier_ordinary codec label 0 value) first second
  have combined := (ScopedQuerySource.machine .relational program).established_and_pending 13 1 _ _ [] started
  rw [finalStep] at combined
  simpa only [List.nil_append, ScopedMatchEntry.entrance, ScopedInsertionSequence.entry, pairBody] using combined

def packets (result formula node temporary : String) (handle : NamedSpaces.Handle)
    (origins : List Nat) (selected : List (Nat × Control)) : List CollectedAnswer :=
  selected.map fun entry => packet result formula node temporary handle {entry.2 with goals := []} (origins ++ [entry.1])

omit [DecidableEq Label] in
/-- This induction follows the already captured source work list. It is not
a replacement evaluator, and both insertion receipts are constructed from
the current readable target on each branch. -/
theorem captured_prefix (codec : Codec Label) (label : Label) (program : SpaceSemantics.Program)
    (handle : NamedSpaces.Handle) (result formula node temporary : String) (context : Context) (origins : List Nat)
    (selected : List (Nat × Control)) (values : List Nat)
    (frames : List.Forall₂ (fun entry value => Frame codec label handle result formula node temporary
      {entry.2 with goals := []} value) selected values)
    (shapes : ∀ entry ∈ selected, entry.2.goals = [.evaluate (pairBody handle formula node temporary) (.var result)])
    (state : State Context) (pending : List (CollectionWork Context)) (rows : List Atom)
    (snapshot : state.world.state.read handle = some rows) (localScope : state.scope.caller.isSome = true) :
    ∃ after : State Context,
      (ScopedQuerySource.machine .relational program).run (14 * selected.length)
        (state.cursor (ScopedQuerySource.work context origins selected ++ pending)) = ([], .exhausted (after.cursor pending)) ∧
      after.world.state.read handle = some (rows ++ (values.flatMap (seedRows label)).map (render codec)) ∧
      (∀ other, other ≠ handle → after.world.state.read other = state.world.state.read other) ∧
      after.world.state.cells = state.world.state.cells ∧ after.allocator = state.allocator ∧
      after.scope.collected = state.scope.collected ++ packets result formula node temporary handle origins selected ∧
      after.scope.caller = state.scope.caller ∧ after.parents = state.parents := by
  induction frames generalizing state pending rows with
  | nil => exact ⟨state, rfl, by simpa using snapshot, fun _ _ => rfl, rfl, rfl, by simp [packets], rfl, rfl⟩
  | @cons entry value entries values framed frames ih =>
      let caller := {entry.2 with goals := []}
      let tail := ScopedQuerySource.work context origins entries ++ pending
      obtain ⟨middleWorld, finalWorld, first, second⟩ := ScopedInsertionSequence.pair_exists state.world.state handle handle
        (render codec (.satisfaction label value)) (render codec (.frontier label 0 value)) rows rows snapshot snapshot
      let middle := advanced result formula node temporary handle caller (origins ++ [entry.1]) state finalWorld
      have firstRun := row_prefix codec label program handle result formula node temporary caller state context
        (origins ++ [entry.1]) tail value framed middleWorld finalWorld first second
      have shaped : ({caller with goals := [.evaluate (pairBody handle formula node temporary) (.var result)]} : Control) = entry.2 := by
        dsimp only [caller]
        rw [← shapes entry List.mem_cons_self]
      have silent : state.scope.caller.isNone = false := by cases found : state.scope.caller <;> simp_all
      have actual : (ScopedQuerySource.machine .relational program).run 14
          (state.cursor (ScopedQuerySource.work context origins (entry :: entries) ++ pending)) =
          ([], .exhausted (middle.cursor tail)) := by
        simpa only [ScopedMatchEntry.entrance, silent, Bool.false_eq_true, ↓reduceIte, shaped,
          ScopedQuerySource.work, List.map_cons, List.cons_append, caller, middle, tail, State.cursor, placed] using firstRun
      have readAfter := ScopedInsertionSequence.pair_store_receipt state.world.state middleWorld finalWorld handle handle _ _ first second handle
      have nextRead : middle.world.state.read handle =
          some (rows ++ [render codec (.satisfaction label value), render codec (.frontier label 0 value)]) := by
        simpa [middle, advanced, snapshot, List.append_assoc] using readAfter
      obtain ⟨after, continued, reading, others, cells, allocator, collected, saved, parents⟩ :=
        ih (fun entry member => shapes entry (List.mem_cons_of_mem _ member)) middle pending _ nextRead localScope
      have joined := (ScopedQuerySource.machine .relational program).established_and_pending 14 (14 * entries.length) _ _ [] actual
      rw [continued] at joined
      refine ⟨after, ?_, ?_, ?_, ?_, allocator, ?_, saved, parents⟩
      · simpa [List.length_cons, Nat.mul_add, Nat.add_comm, List.nil_append, tail] using joined
      · simpa [List.flatMap_cons, seedRows, List.map_append, List.append_assoc] using reading
      · intro other apart
        exact (others other apart).trans
          ((Effects.insert_read_other second apart).trans (Effects.insert_read_other first apart))
      · exact cells.trans ((Effects.insert_preserves_cells second).trans (Effects.insert_preserves_cells first))
      · simpa [middle, advanced, packets, List.map_cons, List.append_assoc] using collected

omit [DecidableEq Label] in
theorem temporary_in_pair (handle : NamedSpaces.Handle) (formula node temporary : String) :
    temporary ∈ (encode (pairBody handle formula node temporary)).freeVars := by
  rw [pairBody, ScopedInsertionSequence.source, CapturedPatternSupport.mem_expression_names]
  exact ⟨.var temporary, by simp, by simp [encode, Mettapedia.Logic.LP.Term.freeVars]⟩

omit [DecidableEq Label] in
theorem node_in_pattern (goal node : String) :
    node ∈ (encode (NamedPresenceSource.patternCode goal node)).freeVars := by
  rw [NamedPresenceSource.patternCode, CapturedPatternSupport.mem_expression_names]
  exact ⟨.var node, by simp, by simp [encode, Mettapedia.Logic.LP.Term.freeVars]⟩

omit [DecidableEq Label] in
theorem captured_frame (codec : Codec Label) (label : Label) (handle : NamedSpaces.Handle)
    (result formula goal node temporary : String) (caller : Control) (principal : Environment) (value : Nat)
    (resolved : resolve caller.bindings = some principal)
    (formulaRead : read principal (.var formula) = codec.encode label)
    (nodeFresh : FreshFor node caller.bindings) (temporaryFresh : FreshFor temporary caller.bindings)
    (resultFresh : FreshFor result caller.bindings) (temporaryResult : temporary ≠ result)
    (resultNode : result ≠ node) (temporaryNode : temporary ≠ node)
    (output : caller.destination = .var result) :
    let pattern := NamedPresenceSource.patternCode goal node
    let child := pairBody handle formula node temporary
    let ready := ScopedMatchPreparation.ready caller (.var result) handle pattern child
    Frame codec label handle result formula node temporary
      {ScopedQuerySource.bodyControl ready [(node, number value)] child (.var result) [] with goals := []} value := by
  dsimp only
  let pattern := NamedPresenceSource.patternCode goal node
  let child := pairBody handle formula node temporary
  let ready := ScopedMatchPreparation.ready caller (.var result) handle pattern child
  have nodeRetained := CTLUntilScopedCapture.pattern_name_retained caller (.var result) handle pattern child node (node_in_pattern goal node)
  obtain ⟨environment, found⟩ := CTLUntilScopedFrame.number_capture_resolves caller (.var result) handle pattern child node value
    principal resolved nodeFresh nodeRetained
  have formulaAfter := CTLUntilScopedFrame.capture_closed_reading caller (.var result) handle pattern child [(node, number value)]
    principal environment (.var formula) (codec.encode label) resolved found formulaRead
    (LiteralQuerySource.read_literal _ (codec.literal label))
  have nodeAfter := CTLUntilScopedFrame.number_capture_read caller (.var result) handle pattern child node value environment found
  have resultRetained : result ∈ (ScopedMatchPreparation.entry caller (.var result) handle pattern child).support := by
    apply GuardedInsertionPairSource.goal_atom_support _ (.var result) result
    · simp [ScopedMatchPreparation.entry, Goal.atoms]
    · simp [encode, Mettapedia.Logic.LP.Term.freeVars]
  have temporaryRetained := CTLUntilScopedCapture.body_name_retained caller (.var result) handle pattern child temporary
    (temporary_in_pair handle formula node temporary)
  refine ⟨rfl, output, ?_, ?_, temporaryResult, environment, found, ?_, ?_⟩
  · exact CTLUntilScopedFrame.number_capture_fresh caller (.var result) handle pattern child node result value resultFresh resultRetained resultNode
  · exact CTLUntilScopedFrame.number_capture_fresh caller (.var result) handle pattern child node temporary value
      temporaryFresh temporaryRetained temporaryNode
  · simp only [read_eq_applyTypeValuation, HE.Spec.Type.RuntimeRefinement.applyTypeValuation] at formulaAfter nodeAfter
    simp only [firstCode, NamedPresenceSource.patternCode, render, read_eq_applyTypeValuation,
      HE.Spec.Type.RuntimeRefinement.applyTypeValuation, List.map_cons, List.map_nil, formulaAfter, nodeAfter]
  · simp only [read_eq_applyTypeValuation, HE.Spec.Type.RuntimeRefinement.applyTypeValuation] at formulaAfter nodeAfter
    simp only [secondCode, render, read_eq_applyTypeValuation,
      HE.Spec.Type.RuntimeRefinement.applyTypeValuation, List.map_cons, List.map_nil, formulaAfter, nodeAfter, number]

structure Entry (codec : Codec Label) (label goal : Label) (input : Input Context)
    (handle : NamedSpaces.Handle) (formulaName goalName nodeName temporary : String) where
  written : input.body = body handle formulaName goalName nodeName temporary
  principal : Environment
  resolved : resolve input.caller.bindings = some principal
  formula : read principal (.var formulaName) = codec.encode label
  goal : read principal (.var goalName) = codec.encode goal
  nodeFresh : FreshFor nodeName input.caller.bindings
  temporaryFresh : FreshFor temporary input.caller.bindings
  temporaryNode : temporary ≠ nodeName
  atoms : List Atom
  rows : List (Row Label)
  snapshot : input.state.world.state.read handle = some atoms
  decoded : decodeRows codec atoms = some rows

omit [DecidableEq Label] in
theorem child_apart (input : Input Context) (handle : NamedSpaces.Handle) (formula goal node temporary : String)
    (written : input.body = body handle formula goal node temporary) :
    input.childName ≠ node ∧ input.childName ≠ temporary := by
  have retained (name : String) (member : name ∈ (encode input.body).freeVars) : input.childName ≠ name := by
    intro same
    apply childName_fresh input.preparing input.boundary
    apply Finset.mem_union_left
    change input.childName ∈ input.preparing.support
    rw [same]
    apply GuardedInsertionPairSource.goal_atom_support input.preparing input.collection name
    · simp [Input.preparing, Goal.atoms]
    · rw [Input.collection, CapturedPatternSupport.mem_expression_names]
      exact ⟨input.body, by simp, member⟩
  constructor
  · apply retained
    rw [written, body, ScopedMatchPreparation.source, CapturedPatternSupport.mem_expression_names]
    exact ⟨NamedPresenceSource.patternCode goal node, by simp, node_in_pattern goal node⟩
  · apply retained
    rw [written, body, ScopedMatchPreparation.source, CapturedPatternSupport.mem_expression_names]
    exact ⟨pairBody handle formula node temporary, by simp, temporary_in_pair handle formula node temporary⟩

/-- The actual query and its captured branches complete without spending
identities. Its collector receives one ready true packet per goal occurrence. -/
theorem child_completed {codec : Codec Label} {label goal : Label} {input : Input Context}
    {handle : NamedSpaces.Handle} {formulaName goalName nodeName temporary : String}
    (entry : Entry codec label goal input handle formulaName goalName nodeName temporary) :
    ∃ after : State Context,
      (ScopedQuerySource.machine .relational input.program).run
        (4 + 14 * (satisfactionView goal entry.rows).length) input.childBefore =
          ([], .exhausted (after.cursor [])) ∧
      after.world.state.read handle = some (entry.atoms ++
        ((satisfactionView goal entry.rows).flatMap (seedRows label)).map (render codec)) ∧
      (∀ other, other ≠ handle → after.world.state.read other = input.state.world.state.read other) ∧
      after.world.state.cells = input.state.world.state.cells ∧ after.allocator = input.state.allocator ∧
      after.scope.collected.length = (satisfactionView goal entry.rows).length ∧
      GuardedQueryPackets.CollectedReady after ∧ after.scope.caller = some input.savedCaller ∧
      after.parents = {input.state.scope with frontier := input.pending} :: input.state.parents := by
  let pattern := NamedPresenceSource.patternCode goalName nodeName
  let child := pairBody handle formulaName nodeName temporary
  let ready := ScopedMatchPreparation.ready input.childCaller (.var input.childName) handle pattern child
  let positions := located (select goal) 0 entry.rows
  have apart := child_apart input handle formulaName goalName nodeName temporary entry.written
  obtain ⟨budget, selected, captured, choices⟩ := capture codec goal input.program handle goalName nodeName child
    (.var input.childName) input.childCaller input.childState input.context input.origins [] entry.principal entry.atoms entry.rows
    entry.resolved entry.goal entry.nodeFresh rfl entry.snapshot entry.decoded
  have values : (satisfactionView goal entry.rows) = positions.map Prod.snd := by
    change entry.rows.filterMap (select goal) = (located (select goal) 0 entry.rows).map Prod.snd
    symm
    simpa using CTLUntilSourceRows.located_map (select goal) 0 entry.rows id
  have frames : List.Forall₂ (fun selected value => Frame codec label handle input.childName formulaName nodeName temporary
      {selected.2 with goals := []} value) selected.choices (satisfactionView goal entry.rows) := by
    rw [choices, values]
    change List.Forall₂ _ (positions.map (fun position =>
      (position.1, ScopedQuerySource.bodyControl ready [(nodeName, number position.2)] child (.var input.childName) [])))
      (positions.map Prod.snd)
    induction positions with
    | nil => exact .nil
    | cons position positions ih =>
      exact .cons (captured_frame codec label handle input.childName formulaName goalName nodeName temporary
        input.childCaller entry.principal position.2 entry.resolved entry.formula entry.nodeFresh entry.temporaryFresh
        (CountedSourceEntry.child_result_fresh input) apart.2.symm apart.1 entry.temporaryNode rfl) ih
  have shapes : ∀ chosen ∈ selected.choices, chosen.2.goals = [.evaluate child (.var input.childName)] := by
    intro chosen member
    simpa only [Input.childCaller] using selected.shape chosen member
  obtain ⟨after, visited, reading, others, cells, allocator, collected, saved, parents⟩ := captured_prefix codec label input.program
    handle input.childName formulaName nodeName temporary input.context input.origins selected.choices (satisfactionView goal entry.rows)
    frames shapes input.childState [] entry.atoms entry.snapshot rfl
  have entered := (ScopedMatchEntry.execute input.program handle pattern child (.var input.childName)
    input.childCaller input.childState input.context input.origins []).exact
  rw [budget, captured] at entered
  change (ScopedQuerySource.machine .relational input.program).run 4
    (ScopedMatchEntry.entrance (body handle formulaName goalName nodeName temporary) (.var input.childName)
      input.childCaller input.childState input.context input.origins []) =
    ([], .exhausted (input.childState.cursor (ScopedQuerySource.work input.context input.origins selected.choices ++ []))) at entered
  rw [← entry.written] at entered
  have joined := (ScopedQuerySource.machine .relational input.program).established_and_pending 4 (14 * selected.choices.length) _ _ [] entered
  rw [visited] at joined
  have size := frames.length_eq
  refine ⟨after, ?_, reading, others, cells, allocator, ?_, ?_, saved, parents⟩
  · simpa only [size, List.nil_append, Input.childBefore] using joined
  · rw [collected]
    simp only [Input.childState, List.nil_append, packets, List.length_map, size]
  · intro value member
    rw [collected] at member
    simp only [Input.childState, List.nil_append, packets, List.mem_map] at member
    obtain ⟨chosen, _, rfl⟩ := member
    exact ⟨rfl, rfl⟩

/-- Seeding returns its original occurrence count and preserves the caller.
Capacity is checked before the proof constructs the actual collector copy. -/
theorem counted_prefix {codec : Codec Label} {label goal : Label} {input : Input Context}
    {handle : NamedSpaces.Handle} {formulaName goalName nodeName temporary : String}
    (entry : Entry codec label goal input handle formulaName goalName nodeName temporary)
    (reserve : (satisfactionView goal entry.rows).length ≤ input.state.allocator.usableCount)
    (representative : String) (unbound : read entry.principal input.destination = .var representative) :
    ∃ (after : State Context) (next : Allocator),
      after.world.state.read handle = some ((entry.rows ++ (satisfactionView goal entry.rows).flatMap (seedRows label)).map (render codec)) ∧
      decodeRows codec ((entry.rows ++ (satisfactionView goal entry.rows).flatMap (seedRows label)).map (render codec)) =
        some (entry.rows ++ (satisfactionView goal entry.rows).flatMap (seedRows label)) ∧
      (∀ other, other ≠ handle → after.world.state.read other = input.state.world.state.read other) ∧
      after.world.state.cells = input.state.world.state.cells ∧
      next.usableCount + (satisfactionView goal entry.rows).length = input.state.allocator.usableCount ∧
      (ScopedQuerySource.machine .relational input.program).run
        (2 + (4 + 14 * (satisfactionView goal entry.rows).length) + 1 + 3) input.before =
        ([], .exhausted (placed next after.world input.state.scope input.state.parents
          (GuardedCountReturn.counted input.caller input.slot input.destination (satisfactionView goal entry.rows).length)
          input.context (input.origins ++ [0]) input.pending)) := by
  obtain ⟨after, completed, reading, others, cells, allocator, count, ready, saved, parents⟩ := child_completed entry
  have boundary : after.cursor [] = GuardedQueryCollection.boundary after.allocator after.world after.scope.collected
      input.savedCaller {input.state.scope with frontier := input.pending} input.state.parents := by
    simp only [State.cursor, GuardedQueryCollection.boundary, parents]
    congr 2
    cases scope : after.scope
    simp_all
  have capacity : after.scope.collected.length ≤ after.allocator.usableCount := by rw [count, allocator]; exact reserve
  obtain ⟨next, returned, balance⟩ := GuardedQueryCopyCapacity.return_with_capacity input.program after.allocator
    after.world after.scope.collected input.savedCaller {input.state.scope with frontier := input.pending} input.state.parents ready capacity
  rw [← boundary] at returned
  change (ScopedQuerySource.machine .relational input.program).run 1 (after.cursor []) =
    ([], .exhausted (placed next after.world input.state.scope input.state.parents
      (GuardedCountReturn.tupleReturned input.caller input.slot input.destination after.scope.collected.length)
      input.context input.origins input.pending)) at returned
  have entered := (ScopedQuerySource.machine .relational input.program).established_and_pending
    2 (4 + 14 * (satisfactionView goal entry.rows).length) _ _ [] (CountedSourceEntry.entry_prefix input)
  rw [completed] at entered
  simp only [List.nil_append] at entered
  have collected := (ScopedQuerySource.machine .relational input.program).established_and_pending
    (2 + (4 + 14 * (satisfactionView goal entry.rows).length)) 1 _ _ [] entered
  rw [returned] at collected
  simp only [List.nil_append] at collected
  have numeric := GuardedCountReturn.count_prefix input.program next after.world input.state.scope input.state.parents
    input.caller input.context input.origins input.pending input.slot input.destination after.scope.collected.length
    entry.principal representative entry.resolved unbound (CountedSourceEntry.slot_fresh input) (CountedSourceEntry.slot_apart input)
  have joined := (ScopedQuerySource.machine .relational input.program).established_and_pending
    (2 + (4 + 14 * (satisfactionView goal entry.rows).length) + 1) 3 _ _ [] collected
  rw [numeric, count] at joined
  rw [count, allocator] at balance
  obtain ⟨rendered, admitted⟩ := CTLUntilMixedStore.decode_rows_sound codec entry.atoms entry.rows entry.decoded
  refine ⟨after, next, ?_, ?_, others, cells, balance, by simpa only [List.nil_append] using joined⟩
  · simpa only [List.map_append, rendered] using reading
  · apply CTLUntilMixedStore.decode_rows_complete
    intro row member
    rcases List.mem_append.mp member with old | seeded
    · exact admitted row old
    · obtain ⟨value, _, selected⟩ := List.mem_flatMap.mp seeded
      simp only [seedRows, List.mem_cons, List.not_mem_nil, or_false] at selected
      rcases selected with rfl | rfl <;> trivial

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSeedSource
