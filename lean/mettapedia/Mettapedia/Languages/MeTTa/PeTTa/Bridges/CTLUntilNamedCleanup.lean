import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilCountedCleanup
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedClosedEquationSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedEquationReturn

/-!
# The named frontier cleanup reaches its counted source body

The actual two-operand clause scan retains the caller equations and freshens
the local frontier variable. Counted cleanup then runs at that reached frame,
returns its captured occurrence count and restores the predicate delimiter.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilNamedCleanup

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open HE.Spec.Type.RuntimeRefinement (renameTypeVars)
open HE.Spec.Type.Presentation (TypeSubst)
open ClosedOnceQueryFrame (FreshFor placed)
open FlatQueryRowCodec (Codec)
open CTLUntilMixedStore (Row render decodeRows frontSelect)
open CTLUntilSourceRows (number)

def source (handle : NamedSpaces.Handle) (formulaName roundName nodeName : String) : Atom :=
  .expression [.symbol "size-atom", .expression [.symbol "collapse",
    CTLUntilCountedCleanup.body handle formulaName roundName nodeName]]

private theorem handle_renamed (handle : NamedSpaces.Handle) (rename : String → String) :
    renameTypeVars rename (Effects.handleValue handle) = Effects.handleValue handle := by
  cases handle <;> simp [Effects.handleValue, renameTypeVars]

private theorem handle_names (handle : NamedSpaces.Handle) : TypeSubst.typeVars (Effects.handleValue handle) = [] := by
  cases handle <;> simp [Effects.handleValue, TypeSubst.typeVars]

theorem source_renamed (handle : NamedSpaces.Handle) (formulaName roundName nodeName : String) (rename : String → String) :
    renameTypeVars rename (source handle formulaName roundName nodeName) =
      source handle (rename formulaName) (rename roundName) (rename nodeName) := by
  simp [source, CTLUntilCountedCleanup.body, ScopedMatchPreparation.source, ScopedRemovalSource.source,
    CTLUntilScopedCapture.frontierCode, renameTypeVars, handle_renamed]

theorem source_names (handle : NamedSpaces.Handle) (formulaName roundName nodeName name : String) :
    name ∈ TypeSubst.typeVars (source handle formulaName roundName nodeName) ↔
      name ∈ [formulaName, roundName, nodeName] := by
  simp only [source, CTLUntilCountedCleanup.body, ScopedMatchPreparation.source, ScopedRemovalSource.source,
    CTLUntilScopedCapture.frontierCode, TypeSubst.typeVars, TypeSubst.typeVarsList, handle_names,
    List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false]
  tauto

structure Call (Context : Type) where
  program : SpaceSemantics.Program
  state : NamedGuardedCandidateBatch.State Context
  control : Control
  context : Context
  origins : List Nat
  pending : List (CollectionWork Context)
  arguments : List Atom
  destination : Atom
  older : List Goal
  handle : NamedSpaces.Handle
  formulaName : String
  roundName : String
  nodeName : String
  distinct : [formulaName, roundName, nodeName].Nodup
  occurrence : Nat

variable {Context Label : Type} [DecidableEq Label]

def Call.definition (call : Call Context) : ScopedClosedEquationSource.Definition := {
  head := "drop", formals := [call.formulaName, call.roundName]
  body := source call.handle call.formulaName call.roundName call.nodeName
  distinct := by
    have names := call.distinct
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at names ⊢
    tauto }

def Call.activeScope (call : Call Context) : CollectionScope Context :=
  {call.state.scope with frontier := (call.control, call.context, call.origins) :: call.pending}
def Call.protectedControl (call : Call Context) : Control :=
  protectControl call.control (collectionSupport ⟨call.state.world, call.activeScope :: call.state.parents⟩)
def Call.name (call : Call Context) (name : String) : String :=
  ScopedClosedEquationSource.formal call.protectedControl call.occurrence call.definition name
def Call.selected (call : Call Context) (arguments : List Atom) : Control :=
  ScopedClosedEquationSource.selected call.protectedControl call.occurrence call.definition arguments call.destination call.older
def Call.bodyCaller (call : Call Context) (arguments : List Atom) : Control :=
  {call.selected arguments with
    goals := .restoreCommit call.control.cutBoundary :: call.older
    cutBoundary := call.pending.length}
def Call.countInput (call : Call Context) (arguments : List Atom) : CountedSourceEntry.Input Context := {
  program := call.program, state := call.state, caller := call.bodyCaller arguments
  context := call.context, origins := call.origins ++ [call.occurrence], pending := call.pending
  destination := call.destination
  body := CTLUntilCountedCleanup.body call.handle (call.name call.formulaName) (call.name call.roundName) (call.name call.nodeName) }
def Call.before (call : Call Context) : ScopedCursor Context :=
  placed call.state.allocator call.state.world call.state.scope call.state.parents call.control call.context call.origins call.pending
def Call.returned (call : Call Context) (arguments : List Atom) (count : Nat) : Control :=
  {GuardedCountReturn.counted (call.bodyCaller arguments) (call.countInput arguments).slot call.destination count with
    goals := call.older, cutBoundary := call.control.cutBoundary}

def values (codec : Codec Label) (label : Label) (round : Nat) : List Atom := [codec.encode label, number round]

structure Evidence (codec : Codec Label) (label : Label) (round : Nat) (call : Call Context) where
  atCall : call.control.goals = .invoke "drop" call.arguments call.destination :: call.older
  principal : Environment
  resolved : resolve call.control.bindings = some principal
  readings : call.arguments.map (read principal) = values codec label round
  representative : String
  unbound : read principal call.destination = .var representative
  row : call.program.equations[call.occurrence]? = some call.definition.declaration
  otherHeads : ∀ index equation, call.program.equations[index]? = some equation →
    index ≠ call.occurrence → equation.head ≠ "drop"
  atoms : List Atom
  rows : List (Row Label)
  snapshot : call.state.world.state.read call.handle = some atoms
  decoded : decodeRows codec atoms = some rows

def Evidence.count {codec : Codec Label} {label : Label} {round : Nat} {call : Call Context}
    (evidence : Evidence codec label round call) : Nat := (evidence.rows.filterMap (frontSelect label round)).length

omit [DecidableEq Label] in
theorem values_closed (codec : Codec Label) (label : Label) (round : Nat)
    (value : Atom) (member : value ∈ values codec label round) (environment : Environment) : read environment value = value := by
  simp only [values, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact LiteralQuerySource.read_literal _ (codec.literal label) environment
  · exact CTLUntilSourceCapture.number_closed round environment

theorem entered_body (call : Call Context) (arguments : List Atom) :
    predicateEntry call.pending.length (call.selected arguments) = (call.countInput arguments).entry := by
  have renamed := source_renamed call.handle call.formulaName call.roundName call.nodeName
    (ScopedClosedEquationSource.formal call.protectedControl call.occurrence call.definition)
  change ClauseChoice.freshBody call.protectedControl call.occurrence call.definition.declaration =
    source call.handle (call.name call.formulaName) (call.name call.roundName) (call.name call.nodeName) at renamed
  simp only [Call.selected, ScopedClosedEquationSource.selected, predicateEntry]
  rw [renamed]
  rfl

omit [DecidableEq Label] in
theorem enter_prefix {codec : Codec Label} {label : Label} {round : Nat} {call : Call Context}
    (evidence : Evidence codec label round call) :
    (ScopedQuerySource.machine .relational call.program).run 1 call.before =
      ([], .exhausted (call.countInput (values codec label round)).before) := by
  have length : call.arguments.length = call.definition.formals.length := by
    have measured := congrArg List.length evidence.readings
    simpa [values, Call.definition] using measured
  have closed : ∀ argument ∈ call.arguments, ∀ environment,
      read environment (read evidence.principal argument) = read evidence.principal argument := by
    intro argument member environment
    apply values_closed codec label round _ ?_ environment
    rw [← evidence.readings]
    exact List.mem_map.mpr ⟨argument, member, rfl⟩
  have entry := ScopedClosedEquationSource.enter .relational call.program call.state.allocator call.state.world
    call.activeScope call.state.parents call.control call.context call.origins call.pending call.definition
    call.occurrence call.arguments call.destination call.older evidence.principal evidence.representative
    rfl evidence.atCall evidence.resolved evidence.unbound length closed
    (by change ("drop" : String) ≠ "parse"; decide) (by change StdLib.known "drop" = false; decide)
    (by change Eval.ioHead "drop" = false; decide) evidence.row evidence.otherHeads
  dsimp only at entry
  rw [evidence.readings] at entry
  change (ScopedQuerySource.machine .relational call.program).run 1 call.before =
    ([], .exhausted (placed call.state.allocator call.state.world call.activeScope call.state.parents
      (predicateEntry call.pending.length (call.selected (values codec label round)))
      call.context (call.origins ++ [call.occurrence]) call.pending)) at entry
  rw [entered_body] at entry
  simpa only [CountedSourceEntry.Input.before, Call.countInput, Call.activeScope, placed] using entry

omit [DecidableEq Label] in
theorem body_frame {codec : Codec Label} {label : Label} {round : Nat} {call : Call Context}
    (evidence : Evidence codec label round call) :
    ∃ principal representative,
      resolve (call.bodyCaller (values codec label round)).bindings = some principal ∧
      read principal call.destination = .var representative ∧
      read principal (.var (call.name call.formulaName)) = codec.encode label ∧
      read principal (.var (call.name call.roundName)) = number round ∧
      FreshFor (call.name call.nodeName) (call.bodyCaller (values codec label round)).bindings := by
  have retained : (encode call.destination).freeVars ⊆ call.protectedControl.support := by
    rw [Call.protectedControl, protectControl_support]
    exact Finset.Subset.trans
      (ScopedClosedEquationSource.call_destination_retained call.control "drop" call.arguments
        call.destination call.older evidence.atCall) Finset.subset_union_left
  obtain ⟨principal, representative, resolved, unbound⟩ := ScopedClosedEquationSource.selected_unbound
    call.protectedControl call.occurrence call.definition (values codec label round) call.destination call.older
    evidence.principal evidence.representative rfl (values_closed codec label round) evidence.resolved evidence.unbound retained
  have readings := ScopedClosedEquationSource.selected_readings call.protectedControl call.occurrence call.definition
    (values codec label round) call.destination call.older principal (values_closed codec label round) (resolve_sound resolved)
  change [read principal (.var (call.name call.formulaName)), read principal (.var (call.name call.roundName))] =
    [codec.encode label, number round] at readings
  simp only [List.cons.injEq, and_true] at readings
  refine ⟨principal, representative, resolved, unbound, readings.1, readings.2, ?_⟩
  apply ScopedClosedEquationSource.local_fresh call.protectedControl call.occurrence call.definition
    (values codec label round) call.destination call.older call.nodeName
  · exact (source_names call.handle call.formulaName call.roundName call.nodeName call.nodeName).mpr (by simp)
  · have names := call.distinct
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at names
    change call.nodeName ∉ [call.formulaName, call.roundName]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨Ne.symm names.1.2, Ne.symm names.2.1⟩
  · exact values_closed codec label round

theorem returned_inherits (call : Call Context) (arguments : List Atom) (count : Nat)
    (environment : Environment) (solved : Solves environment (call.returned arguments count).bindings) :
    Solves environment call.control.bindings := by
  intro pair member
  exact solved pair (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ member)))

theorem returned_value (call : Call Context) (arguments : List Atom) (count : Nat)
    (environment : Environment) (solved : Solves environment (call.returned arguments count).bindings) :
    read environment call.destination = number count := GuardedCountReturn.counted_value _ _ _ _ environment solved

theorem returned_continuation (call : Call Context) (arguments : List Atom) (count : Nat) :
    (call.returned arguments count).goals = call.older ∧
      (call.returned arguments count).cutBoundary = call.control.cutBoundary ∧
      (call.returned arguments count).destination = call.control.destination := ⟨rfl, rfl, rfl⟩

private theorem caller_support_reserved (call : Call Context) (name : String)
    (retained : name ∈ call.control.support) : name ∈ call.protectedControl.reserved := by
  apply Finset.mem_union_right
  apply scope_support ⟨call.state.world, call.activeScope :: call.state.parents⟩ call.activeScope (by simp)
  exact scope_work_support call.activeScope (call.control, call.context, call.origins)
    (by simp [Call.activeScope]) retained

omit [DecidableEq Label] in
/-- A retained caller-local name survives cleanup when it is not part of the
count destination. The destination may itself be an unbound alias. -/
theorem returned_fresh (codec : Codec Label) (label : Label) (round : Nat)
    (call : Call Context) (count : Nat) (name : String)
    (fresh : FreshFor name call.control.bindings) (retained : name ∈ call.control.support)
    (notOutput : name ∉ (encode call.destination).freeVars) :
    FreshFor name (call.returned (values codec label round) count).bindings := by
  let arguments := values codec label round
  let input := call.countInput arguments
  have protectedRetained : name ∈ call.protectedControl.support := by
    rw [Call.protectedControl, protectControl_support]
    exact Finset.mem_union_left _ retained
  have headFresh : FreshFor name (call.selected arguments).bindings := by
    intro equation member
    rcases List.mem_append.mp member with old | added
    · exact fresh equation old
    · cases List.mem_singleton.mp added
      constructor
      · rw [CapturedPatternSupport.mem_expression_names]
        rintro ⟨atom, present, occurs⟩
        rcases List.mem_cons.mp present with same | member
        · subst atom
          simp [encode, Mettapedia.Logic.LP.Term.freeVars] at occurs
        · rw [ScopedClosedEquationSource.closed_names atom (values_closed codec label round atom member)] at occurs
          exact Finset.notMem_empty _ occurs
      · rw [ScopedClosedEquationSource.fresh_pattern, CapturedPatternSupport.mem_expression_names]
        rintro ⟨atom, present, occurs⟩
        rcases List.mem_cons.mp present with same | member
        · subst atom
          simp [encode, Mettapedia.Logic.LP.Term.freeVars] at occurs
        · obtain ⟨renamed, renamedMember, rfl⟩ := List.mem_map.mp member
          obtain ⟨original, _, rfl⟩ := List.mem_map.mp renamedMember
          have same : name = ScopedClosedEquationSource.formal call.protectedControl call.occurrence call.definition original := by
            simpa [encode, Mettapedia.Logic.LP.Term.freeVars] using occurs
          have renamedPresent : ScopedClosedEquationSource.formal call.protectedControl call.occurrence call.definition original ∈
              call.protectedControl.support := same ▸ protectedRetained
          exact ClauseChoice.rename_fresh call.protectedControl call.occurrence
            (ClauseChoice.clauseAtoms call.definition.declaration) original renamedPresent
  have slotApart : name ≠ input.slot := by
    intro same
    have present : name ∈ input.entry.support :=
      Finset.mem_union_left _ (caller_support_reserved call name retained)
    have slotPresent : input.slot ∈ input.entry.support := same ▸ present
    exact freshName_not_mem input.entry 0 slotPresent
  intro equation member
  rcases List.mem_append.mp member with beforeNumber | numeric
  · rcases List.mem_append.mp beforeNumber with beforeTuple | tuple
    · exact headFresh equation beforeTuple
    · cases List.mem_singleton.mp tuple
      constructor
      · rw [CapturedPatternSupport.literal_names_empty _ (GuardedCountReturn.tuple_literal count)]
        exact Finset.notMem_empty name
      · simpa [encode, Mettapedia.Logic.LP.Term.freeVars] using slotApart
  · cases List.mem_singleton.mp numeric
    exact ⟨by simp [GuardedCountReturn.value, encode, Mettapedia.Logic.LP.Term.freeVars], notOutput⟩

theorem returned_closed_reading (call : Call Context) (arguments : List Atom) (count : Nat)
    (before after : Environment) (atom value : Atom)
    (resolved : resolve call.control.bindings = some before) (reading : read before atom = value)
    (closed : ∀ environment, read environment value = value)
    (solved : Solves after (call.returned arguments count).bindings) :
    read after atom = value :=
  CapturedQueryOperands.resolved_forces resolved atom value reading closed after
    (returned_inherits call arguments count after solved)

theorem returns {codec : Codec Label} {label : Label} {round : Nat} {call : Call Context}
    (evidence : Evidence codec label round call) (reserve : evidence.count ≤ call.state.allocator.usableCount) :
    ∃ (after : NamedGuardedCandidateBatch.State Context) (next : Allocator),
      after.world.state.read call.handle = some ((CTLUntilCleanup.remaining label round evidence.rows).map (render codec)) ∧
      decodeRows codec ((CTLUntilCleanup.remaining label round evidence.rows).map (render codec)) =
        some (CTLUntilCleanup.remaining label round evidence.rows) ∧
      (∀ other, other ≠ call.handle → after.world.state.read other = call.state.world.state.read other) ∧
      after.world.state.cells = call.state.world.state.cells ∧
      next.usableCount + evidence.count = call.state.allocator.usableCount ∧
      (∃ principal, resolve (call.returned (values codec label round) evidence.count).bindings = some principal ∧
        read principal call.destination = number evidence.count) ∧
      (ScopedQuerySource.machine .relational call.program).run
        (1 + (2 + (CTLUntilCountedCleanup.childExecution (call.countInput (values codec label round)) call.handle
          (call.name call.formulaName) (call.name call.roundName) (call.name call.nodeName)).budget + 1 + 3) + 1) call.before =
        ([], .exhausted (placed next after.world call.state.scope call.state.parents
          (call.returned (values codec label round) evidence.count) call.context
          ((call.origins ++ [call.occurrence]) ++ [0]) call.pending)) := by
  obtain ⟨principal, representative, resolved, unbound, formula, current, nodeFresh⟩ := body_frame evidence
  let input := call.countInput (values codec label round)
  let admission : CTLUntilCountedCleanup.Entry codec label round input call.handle
      (call.name call.formulaName) (call.name call.roundName) (call.name call.nodeName) := {
    written := rfl, principal, resolved, formula, current, nodeFresh
    atoms := evidence.atoms, rows := evidence.rows, snapshot := evidence.snapshot, decoded := evidence.decoded }
  obtain ⟨after, next, reading, decoded, others, cells, capacity, counted⟩ :=
    CTLUntilCountedCleanup.counted_prefix admission reserve representative unbound
  let child := CTLUntilCountedCleanup.childExecution input call.handle
    (call.name call.formulaName) (call.name call.roundName) (call.name call.nodeName)
  change (ScopedQuerySource.machine .relational call.program).run (2 + child.budget + 1 + 3) input.before =
    ([], .exhausted (placed next after.world call.state.scope call.state.parents
      (GuardedCountReturn.counted input.caller input.slot call.destination evidence.count)
      call.context ((call.origins ++ [call.occurrence]) ++ [0]) call.pending)) at counted
  have restored := ScopedEquationReturn.restore_prefix .relational call.program next after.world call.state.scope
    call.state.parents (GuardedCountReturn.counted input.caller input.slot call.destination evidence.count)
    call.context ((call.origins ++ [call.occurrence]) ++ [0]) call.pending call.control.cutBoundary call.older rfl
  have entered := enter_prefix evidence
  change (ScopedQuerySource.machine .relational call.program).run 1 call.before = ([], .exhausted input.before) at entered
  have first := (ScopedQuerySource.machine .relational call.program).established_and_pending
    1 (2 + child.budget + 1 + 3) _ _ [] entered
  rw [counted] at first
  simp only [List.nil_append] at first
  have joined := (ScopedQuerySource.machine .relational call.program).established_and_pending
    (1 + (2 + child.budget + 1 + 3)) 1 _ _ [] first
  rw [restored] at joined
  have tupleApart : input.slot ∉ (encode (GuardedQueryCollection.tuple evidence.count)).freeVars := by
    rw [CapturedPatternSupport.literal_names_empty _ (GuardedCountReturn.tuple_literal _)]
    simp
  obtain ⟨tuplePrincipal, tupleName, tupleResolved, tupleUnbound⟩ := ScopedMutationSource.unbound_after_fresh_operand
    input.caller.bindings principal call.destination (GuardedQueryCollection.tuple evidence.count)
    representative input.slot resolved unbound (CountedSourceEntry.slot_fresh input) (CountedSourceEntry.slot_apart input) tupleApart
  have numeric := ScopedMutationSource.refine_unbound _ tuplePrincipal call.destination (number evidence.count)
    tupleName tupleResolved tupleUnbound (CTLUntilSourceCapture.number_closed evidence.count)
  obtain ⟨finalPrincipal, finalResolved⟩ := resolve_complete (ClosedOnceQueryFrame.refined_consistent _ _ _ numeric)
  refine ⟨after, next, reading, decoded, others, cells, capacity, ⟨finalPrincipal, finalResolved, ?_⟩, ?_⟩
  · exact returned_value call _ _ finalPrincipal (resolve_sound finalResolved)
  · simpa only [List.nil_append, child, input, Call.returned, Call.countInput] using joined

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilNamedCleanup

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilNamedCleanup.returns
