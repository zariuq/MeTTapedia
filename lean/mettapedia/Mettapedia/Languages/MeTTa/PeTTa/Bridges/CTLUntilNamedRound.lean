import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundSyntax
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundData
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedEquationReturn

/-!
# The named EU round reaches and returns its actual counted body

The source invocation retains its operand slots and caller equations. Its
closed readings determine the actual freshened equation selection. Local
query admission, collection completion, copying and numeric return are
derived, followed by the real predicate-delimiter restoration step.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilNamedRound

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open ClosedOnceQueryFrame (FreshFor placed)
open CTLUntilScopedRound (Query Decoded)
open CTLUntilLeafAdmission (GuardProfile)
open FlatQueryRowCodec (Codec)
open CTLUntilMixedStore (Row decodeRows graphView satisfactionView frontSelect)
open CTLUntilSourceRows (number)

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
  query : Query
  distinct : (CTLUntilRoundSyntax.sourceNames query).Nodup
  occurrence : Nat

variable {Context Label : Type} [DecidableEq Label]

def values (codec : Codec Label) (label operand : Label) (round : Nat) : List Atom :=
  [codec.encode label, codec.encode operand, number round, number (round + 1)]

def Call.definition (call : Call Context) : ScopedClosedEquationSource.Definition :=
  CTLUntilRoundSyntax.definition call.query (CTLUntilRoundSyntax.formals_distinct call.query call.distinct)

def Call.activeScope (call : Call Context) : CollectionScope Context :=
  {call.state.scope with frontier := (call.control, call.context, call.origins) :: call.pending}

def Call.protectedControl (call : Call Context) : Control :=
  protectControl call.control (collectionSupport ⟨call.state.world, call.activeScope :: call.state.parents⟩)

def Call.freshQuery (call : Call Context) : Query :=
  CTLUntilRoundSyntax.freshQuery call.protectedControl call.occurrence call.query
    (CTLUntilRoundSyntax.formals_distinct call.query call.distinct)

def Call.selected (call : Call Context) (arguments : List Atom) : Control :=
  ScopedClosedEquationSource.selected call.protectedControl call.occurrence call.definition arguments call.destination call.older

def Call.bodyCaller (call : Call Context) (arguments : List Atom) : Control :=
  {call.selected arguments with
    goals := .restoreCommit call.control.cutBoundary :: call.older
    cutBoundary := call.pending.length}

def Call.countInput (call : Call Context) (arguments : List Atom) : GuardedCountSource.Input Context := {
  program := call.program, state := call.state, caller := call.bodyCaller arguments
  context := call.context, origins := call.origins ++ [call.occurrence], pending := call.pending
  destination := call.destination, legs := call.freshQuery.legs, template := call.freshQuery.template }

def Call.before (call : Call Context) : ScopedCursor Context :=
  placed call.state.allocator call.state.world call.state.scope call.state.parents
    call.control call.context call.origins call.pending

def Call.returned (call : Call Context) (arguments : List Atom) (count : Nat) : Control :=
  {GuardedCountReturn.counted (call.bodyCaller arguments) (call.countInput arguments).slot call.destination count with
    goals := call.older, cutBoundary := call.control.cutBoundary}

structure Evidence (codec : Codec Label) (label operand : Label) (round : Nat) (call : Call Context) where
  atCall : call.control.goals = .invoke "eu-round" call.arguments call.destination :: call.older
  principal : Environment
  resolved : resolve call.control.bindings = some principal
  readings : call.arguments.map (read principal) = values codec label operand round
  representative : String
  unbound : read principal call.destination = .var representative
  row : call.program.equations[call.occurrence]? = some call.definition.declaration
  otherHeads : ∀ index equation, call.program.equations[index]? = some equation →
    index ≠ call.occurrence → equation.head ≠ "eu-round"
  profile : GuardProfile codec label call.query call.program
  decoded : Decoded codec call.query.handles call.state
  frontAtoms : List Atom
  graphAtoms : List Atom
  factAtoms : List Atom
  fronts : List (Row Label)
  graph : List (Row Label)
  facts : List (Row Label)
  frontRead : call.state.world.state.read call.query.frontierHandle = some frontAtoms
  frontDecode : decodeRows codec frontAtoms = some fronts
  graphRead : call.state.world.state.read call.query.edgeHandle = some graphAtoms
  graphDecode : decodeRows codec graphAtoms = some graph
  factRead : call.state.world.state.read call.query.operandHandle = some factAtoms
  factDecode : decodeRows codec factAtoms = some facts
  initialKnown : List Nat
  initialFrontier : List Nat
  knownRead : CTLUntilRoundPublication.known codec label call.query call.state.world.state = some initialKnown
  frontierRead : CTLUntilRoundPublication.frontier codec label round call.query call.state.world.state = some initialFrontier

def Evidence.word {codec : Codec Label} {label operand : Label} {round : Nat} {call : Call Context}
    (evidence : Evidence codec label operand round call) : List Nat :=
  Mettapedia.Machines.CTLUntilCandidateBag.candidates (graphView evidence.graph) (satisfactionView operand evidence.facts)
    (evidence.fronts.filterMap (frontSelect label round))

def Evidence.added {codec : Codec Label} {label operand : Label} {round : Nat} {call : Call Context}
    (evidence : Evidence codec label operand round call) : List Nat :=
  Mettapedia.Machines.CTLUntilCandidateBag.fresh evidence.word evidence.initialKnown.toFinset

omit [DecidableEq Label] in
theorem values_closed (codec : Codec Label) (label operand : Label) (round : Nat)
    (value : Atom) (member : value ∈ values codec label operand round) (environment : Environment) :
    read environment value = value := by
  simp only [values, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact LiteralQuerySource.read_literal _ (codec.literal label) environment
  · exact LiteralQuerySource.read_literal _ (codec.literal operand) environment
  · exact CTLUntilSourceCapture.number_closed round environment
  · exact CTLUntilSourceCapture.number_closed (round + 1) environment

theorem entered_body (call : Call Context) (arguments : List Atom) :
    predicateEntry call.pending.length (call.selected arguments) = (call.countInput arguments).entry := by
  have body := CTLUntilRoundSyntax.fresh_body call.protectedControl call.occurrence call.query
    (CTLUntilRoundSyntax.formals_distinct call.query call.distinct)
  simp only [Call.selected, ScopedClosedEquationSource.selected, predicateEntry, Call.definition] at ⊢ body
  rw [body]
  rfl

theorem enter_prefix {codec : Codec Label} {label operand : Label} {round : Nat} {call : Call Context}
    (evidence : Evidence codec label operand round call) :
    (ScopedQuerySource.machine .relational call.program).run 1 call.before =
      ([], .exhausted (call.countInput (values codec label operand round)).before) := by
  have length : call.arguments.length = call.definition.formals.length := by
    have measured := congrArg List.length evidence.readings
    simpa [values, Call.definition, CTLUntilRoundSyntax.definition, CTLUntilRoundSyntax.formals] using measured
  have closed : ∀ argument ∈ call.arguments, ∀ environment,
      read environment (read evidence.principal argument) = read evidence.principal argument := by
    intro argument member environment
    apply values_closed codec label operand round _ ?_ environment
    rw [← evidence.readings]
    exact List.mem_map.mpr ⟨argument, member, rfl⟩
  have entry := ScopedClosedEquationSource.enter .relational call.program call.state.allocator call.state.world
    call.activeScope call.state.parents call.control call.context call.origins call.pending call.definition
    call.occurrence call.arguments call.destination call.older evidence.principal evidence.representative
    rfl evidence.atCall evidence.resolved evidence.unbound length closed
    (by change ("eu-round" : String) ≠ "parse"; decide)
    (by change StdLib.known "eu-round" = false; decide)
    (by change Eval.ioHead "eu-round" = false; decide)
    evidence.row evidence.otherHeads
  dsimp only at entry
  rw [evidence.readings] at entry
  change (ScopedQuerySource.machine .relational call.program).run 1 call.before =
    ([], .exhausted (placed call.state.allocator call.state.world call.activeScope call.state.parents
      (predicateEntry call.pending.length (call.selected (values codec label operand round)))
      call.context (call.origins ++ [call.occurrence]) call.pending)) at entry
  rw [entered_body] at entry
  simpa only [GuardedCountSource.Input.before, Call.countInput, Call.activeScope, placed] using entry

/-- Head refinement supplies both the actual principal readings and the
fresh local variables needed by the counted worker. -/
theorem body_frame {codec : Codec Label} {label operand : Label} {round : Nat} {call : Call Context}
    (evidence : Evidence codec label operand round call) :
    ∃ principal representative,
      resolve (call.bodyCaller (values codec label operand round)).bindings = some principal ∧
      read principal call.destination = .var representative ∧
      read principal (.var call.freshQuery.names.formula) = codec.encode label ∧
      read principal (.var call.freshQuery.operand) = codec.encode operand ∧
      read principal (.var call.freshQuery.currentRound) = number round ∧
      read principal (.var call.freshQuery.names.nextRound) = number (round + 1) ∧
      FreshFor call.freshQuery.names.next (call.bodyCaller (values codec label operand round)).bindings ∧
      FreshFor call.freshQuery.names.prior (call.bodyCaller (values codec label operand round)).bindings ∧
      FreshFor call.freshQuery.names.temporary (call.bodyCaller (values codec label operand round)).bindings := by
  have retained : (encode call.destination).freeVars ⊆ call.protectedControl.support := by
    rw [Call.protectedControl, protectControl_support]
    exact Finset.Subset.trans
      (ScopedClosedEquationSource.call_destination_retained call.control "eu-round" call.arguments
        call.destination call.older evidence.atCall) Finset.subset_union_left
  obtain ⟨principal, representative, resolved, unbound⟩ := ScopedClosedEquationSource.selected_unbound
    call.protectedControl call.occurrence call.definition (values codec label operand round) call.destination call.older
    evidence.principal evidence.representative rfl (values_closed codec label operand round)
    evidence.resolved evidence.unbound retained
  have readings := ScopedClosedEquationSource.selected_readings call.protectedControl call.occurrence call.definition
    (values codec label operand round) call.destination call.older principal (values_closed codec label operand round)
    (resolve_sound resolved)
  change [read principal (.var call.freshQuery.names.formula), read principal (.var call.freshQuery.operand),
    read principal (.var call.freshQuery.currentRound), read principal (.var call.freshQuery.names.nextRound)] =
    [codec.encode label, codec.encode operand, number round, number (round + 1)] at readings
  simp only [List.cons.injEq, and_true] at readings
  refine ⟨principal, representative, resolved, unbound, readings.1, readings.2.1, readings.2.2.1,
    readings.2.2.2, ?_, ?_, ?_⟩
  · exact CTLUntilRoundSyntax.selected_local_fresh call.protectedControl call.occurrence call.query call.distinct
      (values codec label operand round) call.destination call.older call.query.names.next
      (by simp [CTLUntilRoundSyntax.locals]) (values_closed codec label operand round)
  · exact CTLUntilRoundSyntax.selected_local_fresh call.protectedControl call.occurrence call.query call.distinct
      (values codec label operand round) call.destination call.older call.query.names.prior
      (by simp [CTLUntilRoundSyntax.locals]) (values_closed codec label operand round)
  · exact CTLUntilRoundSyntax.selected_local_fresh call.protectedControl call.occurrence call.query call.distinct
      (values codec label operand round) call.destination call.older call.query.names.temporary
      (by simp [CTLUntilRoundSyntax.locals]) (values_closed codec label operand round)

theorem returned_inherits (call : Call Context) (arguments : List Atom) (count : Nat)
    (environment : Environment) (solved : Solves environment (call.returned arguments count).bindings) :
    Solves environment call.control.bindings := by
  intro pair member
  exact solved pair (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ member)))

theorem returned_value (call : Call Context) (arguments : List Atom) (count : Nat)
    (environment : Environment) (solved : Solves environment (call.returned arguments count).bindings) :
    read environment call.destination = number count :=
  GuardedCountReturn.counted_value _ _ _ _ environment solved

theorem returned_continuation (call : Call Context) (arguments : List Atom) (count : Nat) :
    (call.returned arguments count).goals = call.older ∧
      (call.returned arguments count).cutBoundary = call.control.cutBoundary ∧
      (call.returned arguments count).destination = call.control.destination := ⟨rfl, rfl, rfl⟩

theorem caller_support_reserved (call : Call Context) (name : String) (retained : name ∈ call.control.support) :
    name ∈ call.protectedControl.reserved := by
  apply Finset.mem_union_right
  apply scope_support ⟨call.state.world, call.activeScope :: call.state.parents⟩ call.activeScope (by simp)
  exact scope_work_support call.activeScope (call.control, call.context, call.origins)
    (by simp [Call.activeScope]) retained

omit [DecidableEq Label] in
/-- Caller-local names protected by the real collection boundary survive
head refinement, the generated tuple slot and the numeric result equation.
The output may be aliased; only the named local's absence from it matters. -/
theorem returned_fresh (codec : Codec Label) (label operand : Label) (round : Nat)
    (call : Call Context) (count : Nat) (name : String)
    (fresh : FreshFor name call.control.bindings) (retained : name ∈ call.control.support)
    (notOutput : name ∉ (encode call.destination).freeVars) :
    FreshFor name (call.returned (values codec label operand round) count).bindings := by
  let arguments := values codec label operand round
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
        · rw [ScopedClosedEquationSource.closed_names atom (values_closed codec label operand round atom member)] at occurs
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

set_option maxHeartbeats 1000000 in
/-- One prepared invocation, its source-created counted child, and the saved
predicate return. The reserve counts candidate occurrences, not unique rows. -/
theorem returns_data_frontier {codec : Codec Label} {label operand : Label} {round : Nat} {call : Call Context}
    (evidence : Evidence codec label operand round call) (separate : label ≠ operand)
    (reserve : evidence.word.length ≤ call.state.allocator.usableCount) :
    ∃ (after : NamedGuardedCandidateBatch.State Context) (next : Allocator),
      Decoded codec call.query.handles after ∧
      CTLUntilRoundData.Preserved codec operand call.query call.state.world.state after.world.state ∧
      CTLUntilRoundData.OtherFrontiers codec label round call.state.world.state after.world.state ∧
      CTLUntilRoundPublication.known codec label call.query after.world.state = some (evidence.initialKnown ++ evidence.added) ∧
      CTLUntilRoundPublication.frontier codec label round call.query after.world.state = some (evidence.initialFrontier ++ evidence.added) ∧
      next.usableCount + evidence.word.length = call.state.allocator.usableCount ∧
      (∃ principal, resolve (call.returned (values codec label operand round) evidence.added.length).bindings = some principal ∧
        read principal call.destination = number evidence.added.length) ∧
      (ScopedQuerySource.machine .relational call.program).run
        (1 + (2 + (call.countInput (values codec label operand round)).childExecution.budget + 1 + 3) + 1) call.before =
        ([], .exhausted (placed next after.world call.state.scope call.state.parents
          (call.returned (values codec label operand round) evidence.added.length)
          call.context ((call.origins ++ [call.occurrence]) ++ [0]) call.pending)) := by
  obtain ⟨principal, representative, resolved, unbound, formula, holds, current, nextRound,
    nextFresh, priorFresh, temporaryFresh⟩ := body_frame evidence
  let input := call.countInput (values codec label operand round)
  let admission : CTLUntilCountedSource.Entry codec label operand round call.freshQuery input := {
    template := rfl, legs := rfl, principal, resolved, formula, holds, current, nextRound
    nextFresh, priorFresh, temporaryFresh
    distinct := CTLUntilRoundSyntax.fresh_locals_distinct call.protectedControl call.occurrence call.query call.distinct
    profile := {
      occurrence := evidence.profile.occurrence, row := evidence.profile.row, otherHeads := evidence.profile.otherHeads
      leftEvaluated := evidence.profile.leftEvaluated, rightEvaluated := evidence.profile.rightEvaluated }
    decoded := evidence.decoded
    frontAtoms := evidence.frontAtoms, graphAtoms := evidence.graphAtoms, factAtoms := evidence.factAtoms
    fronts := evidence.fronts, graph := evidence.graph, facts := evidence.facts
    frontRead := evidence.frontRead, frontDecode := evidence.frontDecode
    graphRead := evidence.graphRead, graphDecode := evidence.graphDecode
    factRead := evidence.factRead, factDecode := evidence.factDecode
    initialKnown := evidence.initialKnown, initialFrontier := evidence.initialFrontier
    knownRead := evidence.knownRead, frontierRead := evidence.frontierRead }
  obtain ⟨after, next, decoded, preserved, otherFrontiers, known, frontier, capacity, counted⟩ :=
    CTLUntilRoundData.counted_prefix_data_frontier admission separate reserve
    representative unbound
  change (ScopedQuerySource.machine .relational call.program).run (2 + input.childExecution.budget + 1 + 3)
    (call.countInput (values codec label operand round)).before =
    ([], .exhausted (placed next after.world call.state.scope call.state.parents
      (GuardedCountReturn.counted input.caller input.slot call.destination evidence.added.length)
      call.context ((call.origins ++ [call.occurrence]) ++ [0]) call.pending)) at counted
  have restored := ScopedEquationReturn.restore_prefix .relational call.program next after.world call.state.scope
    call.state.parents (GuardedCountReturn.counted input.caller input.slot call.destination evidence.added.length)
    call.context ((call.origins ++ [call.occurrence]) ++ [0]) call.pending call.control.cutBoundary call.older rfl
  have entry := enter_prefix evidence
  have first := (ScopedQuerySource.machine .relational call.program).established_and_pending
    1 (2 + input.childExecution.budget + 1 + 3) _ _ [] entry
  rw [counted] at first
  simp only [List.nil_append] at first
  have joined := (ScopedQuerySource.machine .relational call.program).established_and_pending
    (1 + (2 + input.childExecution.budget + 1 + 3)) 1 _ _ [] first
  rw [restored] at joined
  have tupleApart : input.slot ∉ (encode (GuardedQueryCollection.tuple evidence.added.length)).freeVars := by
    rw [CapturedPatternSupport.literal_names_empty _ (GuardedCountReturn.tuple_literal _)]
    simp
  obtain ⟨tuplePrincipal, tupleName, tupleResolved, tupleUnbound⟩ := ScopedMutationSource.unbound_after_fresh_operand
    input.caller.bindings principal call.destination (GuardedQueryCollection.tuple evidence.added.length)
    representative input.slot resolved unbound (GuardedCountSource.slot_fresh input) (GuardedCountSource.slot_apart input) tupleApart
  have numeric := ScopedMutationSource.refine_unbound _ tuplePrincipal call.destination
    (number evidence.added.length) tupleName tupleResolved tupleUnbound
    (CTLUntilSourceCapture.number_closed evidence.added.length)
  obtain ⟨finalPrincipal, finalResolved⟩ := resolve_complete (ClosedOnceQueryFrame.refined_consistent _ _ _ numeric)
  refine ⟨after, next, decoded, ⟨preserved.graph, preserved.operand, preserved.cells, preserved.outside⟩,
    otherFrontiers, known, frontier, capacity, ⟨finalPrincipal, finalResolved, ?_⟩, ?_⟩
  · exact returned_value call _ _ finalPrincipal (resolve_sound finalResolved)
  · simpa only [List.nil_append, input, Call.returned, Call.countInput] using joined

theorem returns_data {codec : Codec Label} {label operand : Label} {round : Nat} {call : Call Context}
    (evidence : Evidence codec label operand round call) (separate : label ≠ operand)
    (reserve : evidence.word.length ≤ call.state.allocator.usableCount) :
    ∃ (after : NamedGuardedCandidateBatch.State Context) (next : Allocator),
      Decoded codec call.query.handles after ∧
      CTLUntilRoundData.Preserved codec operand call.query call.state.world.state after.world.state ∧
      CTLUntilRoundPublication.known codec label call.query after.world.state = some (evidence.initialKnown ++ evidence.added) ∧
      CTLUntilRoundPublication.frontier codec label round call.query after.world.state = some (evidence.initialFrontier ++ evidence.added) ∧
      next.usableCount + evidence.word.length = call.state.allocator.usableCount ∧
      (∃ principal, resolve (call.returned (values codec label operand round) evidence.added.length).bindings = some principal ∧
        read principal call.destination = number evidence.added.length) ∧
      (ScopedQuerySource.machine .relational call.program).run
        (1 + (2 + (call.countInput (values codec label operand round)).childExecution.budget + 1 + 3) + 1) call.before =
        ([], .exhausted (placed next after.world call.state.scope call.state.parents
          (call.returned (values codec label operand round) evidence.added.length)
          call.context ((call.origins ++ [call.occurrence]) ++ [0]) call.pending)) := by
  obtain ⟨after, next, decoded, preserved, _otherFrontiers, result⟩ := returns_data_frontier evidence separate reserve
  exact ⟨after, next, decoded, preserved, result⟩

theorem returns {codec : Codec Label} {label operand : Label} {round : Nat} {call : Call Context}
    (evidence : Evidence codec label operand round call) (separate : label ≠ operand)
    (reserve : evidence.word.length ≤ call.state.allocator.usableCount) :
    ∃ (after : NamedGuardedCandidateBatch.State Context) (next : Allocator),
      CTLUntilRoundPublication.known codec label call.query after.world.state = some (evidence.initialKnown ++ evidence.added) ∧
      CTLUntilRoundPublication.frontier codec label round call.query after.world.state = some (evidence.initialFrontier ++ evidence.added) ∧
      next.usableCount + evidence.word.length = call.state.allocator.usableCount ∧
      (∃ principal, resolve (call.returned (values codec label operand round) evidence.added.length).bindings = some principal ∧
        read principal call.destination = number evidence.added.length) ∧
      (ScopedQuerySource.machine .relational call.program).run
        (1 + (2 + (call.countInput (values codec label operand round)).childExecution.budget + 1 + 3) + 1) call.before =
        ([], .exhausted (placed next after.world call.state.scope call.state.parents
          (call.returned (values codec label operand round) evidence.added.length)
          call.context ((call.origins ++ [call.occurrence]) ++ [0]) call.pending)) := by
  obtain ⟨after, next, _decoded, _preserved, result⟩ := returns_data evidence separate reserve
  exact ⟨after, next, result⟩

namespace Controls

def query : Query := {
  names := ⟨"f", "k1", "y", "x", "ghost-result", "ignored"⟩
  operand := "a", currentRound := "k"
  frontierHandle := .self, edgeHandle := .self, operandHandle := .self
  satisfactionHandle := .self, nextFrontierHandle := .self }

def row (head : String) (fields : List Atom) : Atom := .expression (.symbol head :: fields)

def rows : List Atom := [row "fr" [number 10, number 0, number 2],
  row "rt" [number 2, number 1], row "sat" [number 20, number 1]]

def program : SpaceSemantics.Program := {
  equations := [NamedPresenceSource.declaration
    (CTLUntilPublicationSource.request FlatQueryRowCodec.integers .self (10 : Int) 0),
    (CTLUntilRoundSyntax.definition query (by decide)).declaration]
  declarations := [] }

def invocation : Call Unit := {
  program
  state := ⟨Allocator.empty 8 4, ⟨NamedSpaces.Store.new rows [], [], []⟩, ⟨[], [], none⟩, []⟩
  control := ⟨[(.var "result", .var "alias")],
    [.invoke "eu-round" (values FlatQueryRowCodec.integers 10 20 0) (.var "alias"),
      .equate (.symbol "retained") (.var "tail")], .var "result", {"outside"}, 0⟩
  context := (), origins := [9], pending := []
  arguments := values FlatQueryRowCodec.integers 10 20 0
  destination := .var "alias", older := [.equate (.symbol "retained") (.var "tail")]
  query, distinct := by decide, occurrence := 1 }

def executed := (ScopedQuerySource.machine .relational program).run 800 invocation.before

#guard executed.1.map CollectedAnswer.value == [number 1]
#guard executed.1.head?.map (fun answer => answer.bindings.contains (.symbol "retained", .var "tail")) == some true
#guard (EagerDFSStreaming.Scoped.readback executed.2).bind (fun cursor => cursor.2.world.state.read .self) ==
  some (rows ++ [row "sat" [number 10, number 1], row "fr" [number 10, number 1, number 1]])

def emptyInvocation : Call Unit := {invocation with state := {invocation.state with
  allocator := Allocator.empty 0 4, world := ⟨NamedSpaces.Store.new [] [], [], []⟩}}

#guard ((ScopedQuerySource.machine .relational program).run 800 emptyInvocation.before).1.map CollectedAnswer.value == [number 0]

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilNamedRound
