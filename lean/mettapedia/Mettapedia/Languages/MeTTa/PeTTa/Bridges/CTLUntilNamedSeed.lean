import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSeedSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilDriverControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedClosedEquationSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedLetSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedCountReturnFrame

/-! Named entry and occurrence-preserving seeding for the authored EU driver.
The source clause is selected and freshened by the ordinary clause scan;
the seed collector retains the actual caller and following loop call. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilNamedSeed

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open ClosedOnceQueryFrame (FreshFor placed)
open FlatQueryRowCodec (Codec)
open CTLUntilMixedStore (Row decodeRows satisfactionView render)
open CTLUntilSourceRows (number)
open HE.Spec.Type.RuntimeRefinement (renameTypeVars)
open ScopedQuerySource

def definition : ScopedClosedEquationSource.Definition :=
  ⟨"do-eu", ["f", "a", "b"], CTLUntilDriverControls.entryBody, by decide⟩

theorem authored : definition.declaration = CTLUntilDriverControls.entryEquation := rfl

def seed (rename : String → String) : Atom :=
  CTLUntilSeedSource.body .self (rename "f") (rename "b") (rename "x") (rename "ignored")

def counted (rename : String → String) : Atom :=
  .expression [.symbol "size-atom", .expression [.symbol "collapse", seed rename]]

def loop (rename : String → String) : Atom :=
  ScopedAtomicCallOperands.source "eu-loop" [.var (rename "f"), .var (rename "a"), number 0]

theorem renamed_body (rename : String → String) :
    renameTypeVars rename definition.body = ScopedLetSource.source (rename "n") (counted rename) (loop rename) := by
  simp [definition, CTLUntilDriverControls.entryBody, CTLUntilDriverControls.counted,
    ScopedQuerySource.Controls.call, ScopedQuerySource.Controls.self, ScopedQuerySource.Controls.number,
    ScopedQuerySource.CTLUntilControls.sat, ScopedQuerySource.CTLUntilControls.frontier,
    ScopedLetSource.source, counted, seed, loop, ScopedAtomicCallOperands.source,
    CTLUntilSeedSource.body, CTLUntilSeedSource.pairBody, CTLUntilSeedSource.firstCode,
    CTLUntilSeedSource.secondCode, ScopedMatchPreparation.source, ScopedInsertionSequence.source,
    NamedPresenceSource.patternCode, ScopedInsertionSource.source, Effects.handleValue, number, renameTypeVars]

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
  occurrence : Nat

variable {Context Label : Type} [DecidableEq Label]

def values (codec : Codec Label) (label operand goal : Label) : List Atom :=
  [codec.encode label, codec.encode operand, codec.encode goal]

def Call.activeScope (call : Call Context) : CollectionScope Context :=
  {call.state.scope with frontier := (call.control, call.context, call.origins) :: call.pending}

def Call.protectedControl (call : Call Context) : Control :=
  protectControl call.control (collectionSupport ⟨call.state.world, call.activeScope :: call.state.parents⟩)

def Call.rename (call : Call Context) : String → String :=
  ScopedClosedEquationSource.formal call.protectedControl call.occurrence definition

def Call.selected (call : Call Context) (arguments : List Atom) : Control :=
  ScopedClosedEquationSource.selected call.protectedControl call.occurrence definition arguments call.destination call.older

def Call.bodyCaller (call : Call Context) (arguments : List Atom) : Control :=
  {call.selected arguments with
    goals := .restoreCommit call.control.cutBoundary :: call.older
    cutBoundary := call.pending.length}

def Call.producerCaller (call : Call Context) (arguments : List Atom) : Control :=
  ScopedLetSource.producerCaller (call.bodyCaller arguments) (call.rename "n")
    (counted call.rename) (loop call.rename) call.destination

def Call.producerSlot (call : Call Context) (arguments : List Atom) : String :=
  ScopedLetSource.slot (call.bodyCaller arguments) (call.rename "n")
    (counted call.rename) (loop call.rename) call.destination

def Call.seedInput (call : Call Context) (arguments : List Atom) : CountedSourceEntry.Input Context := {
  program := call.program, state := call.state, caller := call.producerCaller arguments,
  context := call.context, origins := call.origins ++ [call.occurrence], pending := call.pending,
  destination := .var (call.producerSlot arguments), body := seed call.rename }

def Call.before (call : Call Context) : ScopedCursor Context :=
  placed call.state.allocator call.state.world call.state.scope call.state.parents
    call.control call.context call.origins call.pending

def Call.seedReturned (call : Call Context) (arguments : List Atom) (count : Nat) : Control :=
  GuardedCountReturn.counted (call.seedInput arguments).caller (call.seedInput arguments).slot
    (call.seedInput arguments).destination count

structure Evidence (codec : Codec Label) (label operand goal : Label) (call : Call Context) where
  atCall : call.control.goals = .invoke "do-eu" call.arguments call.destination :: call.older
  principal : Environment
  resolved : resolve call.control.bindings = some principal
  readings : call.arguments.map (read principal) = values codec label operand goal
  representative : String
  unbound : read principal call.destination = .var representative
  row : call.program.equations[call.occurrence]? = some definition.declaration
  otherHeads : ∀ index equation, call.program.equations[index]? = some equation →
    index ≠ call.occurrence → equation.head ≠ "do-eu"

omit [DecidableEq Label] in
theorem values_closed (codec : Codec Label) (label operand goal : Label)
    (value : Atom) (member : value ∈ values codec label operand goal) (environment : Environment) :
    read environment value = value := by
  simp only [values, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;>
    exact LiteralQuerySource.read_literal _ (codec.literal _) environment

theorem entered_body (call : Call Context) (arguments : List Atom) :
    predicateEntry call.pending.length (call.selected arguments) =
      ScopedLetSource.entry (call.bodyCaller arguments) (call.rename "n")
        (counted call.rename) (loop call.rename) call.destination := by
  have written := renamed_body call.rename
  change ClauseChoice.freshBody call.protectedControl call.occurrence definition.declaration = _ at written
  simp only [Call.selected, ScopedClosedEquationSource.selected, predicateEntry, written,
    ScopedLetSource.entry, Call.bodyCaller]
  rfl

omit [DecidableEq Label] in
theorem enter_prefix {codec : Codec Label} {label operand goal : Label} {call : Call Context}
    (evidence : Evidence codec label operand goal call) :
    (ScopedQuerySource.machine .relational call.program).run 1 call.before =
      ([], .exhausted (placed call.state.allocator call.state.world call.state.scope call.state.parents
        (ScopedLetSource.entry (call.bodyCaller (values codec label operand goal)) (call.rename "n")
          (counted call.rename) (loop call.rename) call.destination)
        call.context (call.origins ++ [call.occurrence]) call.pending)) := by
  have length : call.arguments.length = definition.formals.length := by
    have measured := congrArg List.length evidence.readings
    simpa [values, definition] using measured
  have closed : ∀ argument ∈ call.arguments, ∀ environment,
      read environment (read evidence.principal argument) = read evidence.principal argument := by
    intro argument member environment
    apply values_closed codec label operand goal _ ?_ environment
    rw [← evidence.readings]
    exact List.mem_map.mpr ⟨argument, member, rfl⟩
  have actual := ScopedClosedEquationSource.enter .relational call.program call.state.allocator call.state.world
    call.activeScope call.state.parents call.control call.context call.origins call.pending definition
    call.occurrence call.arguments call.destination call.older evidence.principal evidence.representative
    rfl evidence.atCall evidence.resolved evidence.unbound length closed
    (by decide) (by decide) (by decide) evidence.row evidence.otherHeads
  dsimp only at actual
  rw [evidence.readings] at actual
  change (ScopedQuerySource.machine .relational call.program).run 1 call.before =
    ([], .exhausted (placed call.state.allocator call.state.world call.activeScope call.state.parents
      (predicateEntry call.pending.length (call.selected (values codec label operand goal)))
      call.context (call.origins ++ [call.occurrence]) call.pending)) at actual
  rw [entered_body] at actual
  simpa only [Call.activeScope, placed] using actual

theorem clause_name (name : String) (member : name ∈ ["f", "a", "b", "n", "x", "ignored"]) :
    name ∈ ClauseChoice.names (ClauseChoice.clauseAtoms definition.declaration) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem rename_apart (call : Call Context) (first second : String)
    (left : first ∈ ["f", "a", "b", "n", "x", "ignored"])
    (right : second ∈ ["f", "a", "b", "n", "x", "ignored"]) (different : first ≠ second) :
    call.rename first ≠ call.rename second := by
  intro same
  exact different (ClauseChoice.rename_injective_on call.protectedControl call.occurrence _
    (clause_name first left) (clause_name second right) same)

omit [DecidableEq Label] in
theorem local_fresh (codec : Codec Label) (label operand goal : Label) (call : Call Context)
    (name : String) (member : name ∈ ["n", "x", "ignored"]) :
    FreshFor (call.rename name) (call.bodyCaller (values codec label operand goal)).bindings := by
  apply ScopedClosedEquationSource.local_fresh call.protectedControl call.occurrence definition
    (values codec label operand goal) call.destination call.older name
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  · exact values_closed codec label operand goal

omit [DecidableEq Label] in
theorem body_frame {codec : Codec Label} {label operand goal : Label} {call : Call Context}
    (evidence : Evidence codec label operand goal call) :
    ∃ principal,
      resolve (call.bodyCaller (values codec label operand goal)).bindings = some principal ∧
      read principal (.var (call.rename "f")) = codec.encode label ∧
      read principal (.var (call.rename "a")) = codec.encode operand ∧
      read principal (.var (call.rename "b")) = codec.encode goal := by
  obtain ⟨principal, resolved⟩ := resolve_complete (ScopedClosedEquationSource.selected_consistent
    call.protectedControl call.occurrence definition (values codec label operand goal) call.destination call.older
    rfl (values_closed codec label operand goal) ⟨evidence.principal, resolve_sound evidence.resolved⟩)
  have readings := ScopedClosedEquationSource.selected_readings call.protectedControl call.occurrence definition
    (values codec label operand goal) call.destination call.older principal (values_closed codec label operand goal)
    (resolve_sound resolved)
  change [read principal (.var (call.rename "f")), read principal (.var (call.rename "a")),
    read principal (.var (call.rename "b"))] = [codec.encode label, codec.encode operand, codec.encode goal] at readings
  simp only [List.cons.injEq, and_true] at readings
  exact ⟨principal, resolved, readings⟩

theorem seed_local_retained (call : Call Context) (arguments : List Atom) (name : String)
    (member : name ∈ ["x", "ignored"]) :
    call.rename name ∈ (ScopedLetSource.entry (call.bodyCaller arguments) (call.rename "n")
      (counted call.rename) (loop call.rename) call.destination).support := by
  apply GuardedInsertionPairSource.goal_atom_support _
    (ScopedLetSource.source (call.rename "n") (counted call.rename) (loop call.rename))
  · simp [ScopedLetSource.entry, Goal.atoms]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rw [ScopedLetSource.source, CapturedPatternSupport.mem_expression_names]
    refine ⟨counted call.rename, by simp, ?_⟩
    rw [counted, CapturedPatternSupport.mem_expression_names]
    refine ⟨.expression [.symbol "collapse", seed call.rename], by simp, ?_⟩
    rw [CapturedPatternSupport.mem_expression_names]
    refine ⟨seed call.rename, by simp, ?_⟩
    rw [seed, CTLUntilSeedSource.body, ScopedMatchPreparation.source, CapturedPatternSupport.mem_expression_names]
    rcases member with rfl | rfl
    · refine ⟨NamedPresenceSource.patternCode (call.rename "b") (call.rename "x"), by simp, ?_⟩
      exact CTLUntilSeedSource.node_in_pattern _ _
    · refine ⟨CTLUntilSeedSource.pairBody .self (call.rename "f") (call.rename "x") (call.rename "ignored"), by simp, ?_⟩
      exact CTLUntilSeedSource.temporary_in_pair _ _ _ _

omit [DecidableEq Label] in
theorem seed_frame {codec : Codec Label} {label operand goal : Label} {call : Call Context}
    (evidence : Evidence codec label operand goal call)
    (atoms : List Atom) (rows : List (Row Label))
    (snapshot : call.state.world.state.read .self = some atoms)
    (decoded : decodeRows codec atoms = some rows) :
    ∃ (frame : CTLUntilSeedSource.Entry codec label goal (call.seedInput (values codec label operand goal))
        .self (call.rename "f") (call.rename "b") (call.rename "x") (call.rename "ignored")), ∃ representative,
      frame.rows = rows ∧ read frame.principal (call.seedInput (values codec label operand goal)).destination = .var representative := by
  obtain ⟨before, resolved, formula, _operand, goalRead⟩ := body_frame evidence
  obtain ⟨principal, representative, prepared, unbound⟩ := ScopedLetSource.producer_unbound
    (call.bodyCaller (values codec label operand goal)) (call.rename "n") (counted call.rename)
    (loop call.rename) call.destination before resolved (local_fresh codec label operand goal call "n" (by simp))
  have inherited := ScopedLetSource.inherited (call.bodyCaller (values codec label operand goal)) (call.rename "n")
    (counted call.rename) (loop call.rename) call.destination principal (resolve_sound prepared)
  have formulaAfter := CapturedQueryOperands.resolved_forces resolved (.var (call.rename "f"))
    (codec.encode label) formula (LiteralQuerySource.read_literal _ (codec.literal label)) principal inherited
  have goalAfter := CapturedQueryOperands.resolved_forces resolved (.var (call.rename "b"))
    (codec.encode goal) goalRead (LiteralQuerySource.read_literal _ (codec.literal goal)) principal inherited
  have retainedFresh (name : String) (member : name ∈ ["x", "ignored"]) :
      FreshFor (call.rename name) (call.producerCaller (values codec label operand goal)).bindings := by
    apply ScopedLetSource.producer_fresh_of_entry_support
    · exact local_fresh codec label operand goal call name (by simp_all)
    · exact seed_local_retained call _ name member
    · apply rename_apart call name "n" (by simp_all) (by simp)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> decide
  refine ⟨{
    written := rfl
    principal := principal
    resolved := prepared
    formula := formulaAfter
    goal := goalAfter
    nodeFresh := retainedFresh "x" (by simp)
    temporaryFresh := retainedFresh "ignored" (by simp)
    temporaryNode := rename_apart call "ignored" "x" (by simp) (by simp) (by decide)
    atoms := atoms
    rows := rows
    snapshot := snapshot
    decoded := decoded
  }, representative, rfl, unbound⟩

omit [DecidableEq Label] in
theorem seed_entry_prefix {codec : Codec Label} {label operand goal : Label} {call : Call Context}
    (evidence : Evidence codec label operand goal call) :
    (ScopedQuerySource.machine .relational call.program).run 4 call.before =
      ([], .exhausted (call.seedInput (values codec label operand goal)).before) := by
  obtain ⟨principal, resolved, _⟩ := body_frame evidence
  have prepared := ScopedLetSource.preparation call.program call.state.allocator call.state.world
    call.state.scope call.state.parents (call.bodyCaller (values codec label operand goal)) call.context
    (call.origins ++ [call.occurrence]) call.pending (call.rename "n") (counted call.rename)
    (loop call.rename) call.destination ⟨principal, resolve_sound resolved⟩
  have joined := (ScopedQuerySource.machine .relational call.program).established_and_pending 1 3 _ _ [] (enter_prefix evidence)
  rw [prepared] at joined
  simpa only [List.nil_append, Call.seedInput, CountedSourceEntry.Input.before, CountedSourceEntry.Input.entry,
    CountedSourceEntry.Input.source, CountedSourceEntry.Input.collection, Call.producerCaller,
    Call.producerSlot, ScopedLetSource.producing, counted] using joined

/-- The named source call reaches its real following loop goal after the
seed count, with every goal occurrence retained and its exact copy debit. -/
theorem seeded {codec : Codec Label} {label operand goal : Label} {call : Call Context}
    (evidence : Evidence codec label operand goal call)
    (atoms : List Atom) (rows : List (Row Label))
    (snapshot : call.state.world.state.read .self = some atoms)
    (decoded : decodeRows codec atoms = some rows)
    (reserve : (satisfactionView goal rows).length ≤ call.state.allocator.usableCount) :
    ∃ (after : NamedGuardedCandidateBatch.State Context) (next : Allocator),
      after.world.state.read .self = some ((rows ++ (satisfactionView goal rows).flatMap
        (CTLUntilSeedSource.seedRows label)).map (render codec)) ∧
      decodeRows codec ((rows ++ (satisfactionView goal rows).flatMap (CTLUntilSeedSource.seedRows label)).map (render codec)) =
        some (rows ++ (satisfactionView goal rows).flatMap (CTLUntilSeedSource.seedRows label)) ∧
      (∀ other, other ≠ .self → after.world.state.read other = call.state.world.state.read other) ∧
      after.world.state.cells = call.state.world.state.cells ∧
      next.usableCount + (satisfactionView goal rows).length = call.state.allocator.usableCount ∧
      (ScopedQuerySource.machine .relational call.program).run (14 + 14 * (satisfactionView goal rows).length) call.before =
        ([], .exhausted (placed next after.world call.state.scope call.state.parents
          (GuardedCountReturn.counted (call.seedInput (values codec label operand goal)).caller
            (call.seedInput (values codec label operand goal)).slot
            (call.seedInput (values codec label operand goal)).destination (satisfactionView goal rows).length)
          call.context ((call.origins ++ [call.occurrence]) ++ [0]) call.pending)) := by
  obtain ⟨frame, representative, rowsEqual, unbound⟩ := seed_frame evidence atoms rows snapshot decoded
  obtain ⟨after, next, reading, afterDecode, other, cells, debit, execution⟩ := CTLUntilSeedSource.counted_prefix frame
    (by change (satisfactionView goal frame.rows).length ≤ call.state.allocator.usableCount; rw [rowsEqual]; exact reserve)
    representative unbound
  rw [rowsEqual] at reading afterDecode debit execution
  change (ScopedQuerySource.machine .relational call.program).run _ (call.seedInput _).before = _ at execution
  have joined := (ScopedQuerySource.machine .relational call.program).established_and_pending
    4 (2 + (4 + 14 * (satisfactionView goal rows).length) + 1 + 3) _ _ [] (seed_entry_prefix evidence)
  rw [execution] at joined
  refine ⟨after, next, reading, afterDecode, other, cells, debit, ?_⟩
  have budget : 4 + (2 + (4 + 14 * (satisfactionView goal rows).length) + 1 + 3) =
      14 + 14 * (satisfactionView goal rows).length := by omega
  rw [budget] at joined
  simpa only [List.nil_append, Call.seedInput] using joined

theorem returned_frame {codec : Codec Label} {label operand goal : Label} {call : Call Context}
    (evidence : Evidence codec label operand goal call)
    (atoms : List Atom) (rows : List (Row Label))
    (snapshot : call.state.world.state.read .self = some atoms)
    (decoded : decodeRows codec atoms = some rows) :
    ∃ principal, resolve (call.seedReturned (values codec label operand goal) (satisfactionView goal rows).length).bindings = some principal ∧
      read principal (.var (call.rename "f")) = codec.encode label ∧
      read principal (.var (call.rename "a")) = codec.encode operand ∧
      read principal (.var (call.rename "n")) = number (satisfactionView goal rows).length := by
  obtain ⟨frame, representative, rowsEqual, unbound⟩ := seed_frame evidence atoms rows snapshot decoded
  obtain ⟨principal, resolved, numeric⟩ := GuardedCountReturnFrame.counted_resolves
    (call.seedInput (values codec label operand goal)).caller (call.seedInput (values codec label operand goal)).slot
    (call.seedInput (values codec label operand goal)).destination (satisfactionView goal rows).length
    frame.principal representative frame.resolved unbound
    (CountedSourceEntry.slot_fresh _) (CountedSourceEntry.slot_apart _)
  have producerSolved := GuardedCountReturnFrame.counted_inherits _ _ _ _ principal (resolve_sound resolved)
  have bodySolved := ScopedLetSource.inherited (call.bodyCaller (values codec label operand goal)) (call.rename "n")
    (counted call.rename) (loop call.rename) call.destination principal producerSolved
  obtain ⟨before, beforeResolved, formula, operandRead, _goal⟩ := body_frame evidence
  refine ⟨principal, resolved, ?_, ?_, ?_⟩
  · exact CapturedQueryOperands.resolved_forces beforeResolved _ _ formula
      (LiteralQuerySource.read_literal _ (codec.literal label)) principal bodySolved
  · exact CapturedQueryOperands.resolved_forces beforeResolved _ _ operandRead
      (LiteralQuerySource.read_literal _ (codec.literal operand)) principal bodySolved
  · exact ScopedLetSource.aliased_value (call.bodyCaller (values codec label operand goal)) (call.rename "n")
      (counted call.rename) (loop call.rename) call.destination _ principal producerSolved numeric

omit [DecidableEq Label] in
theorem returned_root_fresh {codec : Codec Label} {label operand goal : Label} {call : Call Context}
    (evidence : Evidence codec label operand goal call) (root : String) (output : call.destination = .var root)
    (fresh : FreshFor root call.control.bindings) (count : Nat) :
    FreshFor root (call.seedReturned (values codec label operand goal) count).bindings := by
  have retained : root ∈ call.protectedControl.support := by
    rw [Call.protectedControl, protectControl_support]
    apply Finset.mem_union_left
    apply ScopedClosedEquationSource.call_destination_retained call.control "do-eu" call.arguments
      call.destination call.older evidence.atCall
    simp [output, encode, Mettapedia.Logic.LP.Term.freeVars]
  have apart (name : String) : root ≠ call.rename name := by
    intro same
    apply ClauseChoice.rename_fresh call.protectedControl call.occurrence (ClauseChoice.clauseAtoms definition.declaration) name
    change call.rename name ∈ call.protectedControl.support
    rw [← same]
    exact retained
  have bodyFresh : FreshFor root (call.bodyCaller (values codec label operand goal)).bindings :=
    ScopedClosedEquationSource.selected_retained_fresh call.protectedControl call.occurrence definition
      (values codec label operand goal) call.destination call.older root fresh retained (values_closed codec label operand goal)
  have letRetained : root ∈ (ScopedLetSource.entry (call.bodyCaller (values codec label operand goal)) (call.rename "n")
      (counted call.rename) (loop call.rename) call.destination).support := by
    apply GuardedInsertionPairSource.goal_atom_support _ (.var root) root
    · simp [ScopedLetSource.entry, output, Goal.atoms]
    · simp [encode, Mettapedia.Logic.LP.Term.freeVars]
  have producerFresh : FreshFor root (call.producerCaller (values codec label operand goal)).bindings :=
    ScopedLetSource.producer_fresh_of_entry_support _ _ _ _ _ root bodyFresh letRetained (apart "n")
  have slotApart : root ≠ call.producerSlot (values codec label operand goal) := by
    intro same
    apply freshName_not_mem (ScopedLetSource.entry (call.bodyCaller (values codec label operand goal)) (call.rename "n")
      (counted call.rename) (loop call.rename) call.destination) 0
    change call.producerSlot (values codec label operand goal) ∈ _
    rw [← same]
    exact letRetained
  apply GuardedCountReturnFrame.counted_fresh (call.seedInput (values codec label operand goal)) count root producerFresh
  · apply GuardedInsertionPairSource.goal_atom_support _ (.var root) root
    · simp [Call.seedInput, CountedSourceEntry.Input.entry, Call.producerCaller,
        ScopedLetSource.producerCaller, output, Goal.atoms]
    · simp [encode, Mettapedia.Logic.LP.Term.freeVars]
  · change root ∉ (encode (.var (call.producerSlot (values codec label operand goal)))).freeVars
    simpa [encode, Mettapedia.Logic.LP.Term.freeVars] using slotApart

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilNamedSeed
