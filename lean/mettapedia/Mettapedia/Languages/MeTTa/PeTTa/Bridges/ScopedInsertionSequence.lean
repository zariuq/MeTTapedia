import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedInsertionSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedPatternSupport

/-! The authored two-insertion body: its local let binder, captured payloads
and caller remain explicit. The targets may differ, and both store effects
occur in source order. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedInsertionSequence

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open ClosedOnceQueryFrame (FreshFor placed)

def source (temporary : String) (firstHandle secondHandle : NamedSpaces.Handle) (first second : Atom) : Atom :=
  .expression [.symbol "let", .var temporary, ScopedInsertionSource.source firstHandle first,
    ScopedInsertionSource.source secondHandle second]

def entry (caller : Control) (result temporary : String) (firstHandle secondHandle : NamedSpaces.Handle) (first second : Atom) : Control :=
  {caller with goals := .evaluate (source temporary firstHandle secondHandle first second) (.var result) :: caller.goals}

def joined (caller : Control) (result temporary : String) (firstHandle secondHandle : NamedSpaces.Handle) (first second : Atom) : String :=
  freshName (entry caller result temporary firstHandle secondHandle first second) 0

def firstCaller (caller : Control) (result temporary : String) (firstHandle secondHandle : NamedSpaces.Handle) (first second : Atom) : Control :=
  {caller with
    bindings := caller.bindings ++ [(.var temporary, .var (joined caller result temporary firstHandle secondHandle first second))]
    goals := .evaluate (ScopedInsertionSource.source secondHandle second) (.var result) :: caller.goals}

def afterFirst (caller : Control) (result temporary : String) (firstHandle secondHandle : NamedSpaces.Handle) (first second : Atom) : Control :=
  ScopedInsertionSource.returned (firstCaller caller result temporary firstHandle secondHandle first second)
    (.var (joined caller result temporary firstHandle secondHandle first second)) firstHandle first

def secondCaller (caller : Control) (result temporary : String) (firstHandle secondHandle : NamedSpaces.Handle) (first second : Atom) : Control :=
  {(afterFirst caller result temporary firstHandle secondHandle first second) with goals := caller.goals}

def returned (caller : Control) (result temporary : String) (firstHandle secondHandle : NamedSpaces.Handle) (first second : Atom) : Control :=
  ScopedInsertionSource.returned (secondCaller caller result temporary firstHandle secondHandle first second) (.var result) secondHandle second

theorem fresh_for_goal_atom (control : Control) (index : Nat) (atom : Atom)
    (member : atom ∈ control.goals.flatMap Goal.atoms) : freshName control index ∉ (encode atom).freeVars := by
  intro used
  apply freshName_not_mem control index
  apply Finset.mem_union_right
  apply (ClosedOnceQueryFrame.fold_support_iff _ _ _).mpr
  exact Or.inr ⟨atom, List.mem_cons_of_mem _ (List.mem_append_right _ member), used⟩

theorem joined_apart (caller : Control) (result temporary : String) (firstHandle secondHandle : NamedSpaces.Handle) (first second : Atom) :
    joined caller result temporary firstHandle secondHandle first second ≠ temporary ∧ joined caller result temporary firstHandle secondHandle first second ≠ result := by
  have sourceFresh := fresh_for_goal_atom (entry caller result temporary firstHandle secondHandle first second) 0
    (source temporary firstHandle secondHandle first second) (by simp [entry, Goal.atoms])
  have resultFresh := fresh_for_goal_atom (entry caller result temporary firstHandle secondHandle first second) 0 (.var result)
    (by simp [entry, Goal.atoms])
  constructor
  · intro same
    apply sourceFresh
    change joined caller result temporary firstHandle secondHandle first second ∈ _
    rw [same, source, CapturedPatternSupport.mem_expression_names]
    exact ⟨.var temporary, by simp, by simp [encode, Mettapedia.Logic.LP.Term.freeVars]⟩
  · simpa [joined, encode, Mettapedia.Logic.LP.Term.freeVars] using resultFresh

theorem joined_fresh (caller : Control) (result temporary : String) (firstHandle secondHandle : NamedSpaces.Handle) (first second : Atom) :
    FreshFor (joined caller result temporary firstHandle secondHandle first second) caller.bindings :=
  ClosedOnceQueryFrame.fresh_for_bindings (entry caller result temporary firstHandle secondHandle first second) _ (freshName_not_mem _ _)

theorem joined_refined (caller : Control) (result temporary : String) (firstHandle secondHandle : NamedSpaces.Handle) (first second : Atom)
    (consistent : ∃ environment, Solves environment caller.bindings) :
    refine caller.bindings (.var temporary) (.var (joined caller result temporary firstHandle secondHandle first second)) =
      some (firstCaller caller result temporary firstHandle secondHandle first second).bindings := by
  apply ScopedMutationSource.refine_fresh_operand _ _ _ (joined_fresh caller result temporary firstHandle secondHandle first second) _ consistent
  simpa [encode, Mettapedia.Logic.LP.Term.freeVars] using (joined_apart caller result temporary firstHandle secondHandle first second).1

set_option maxHeartbeats 1200000 in
theorem preparation {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (result temporary : String)
    (firstHandle secondHandle : NamedSpaces.Handle) (first second : Atom) (consistent : ∃ environment, Solves environment caller.bindings) :
    (ScopedQuerySource.machine .relational program).run 3
      (placed allocator world scope parents (entry caller result temporary firstHandle secondHandle first second) context origins pending) =
      ([], .exhausted (placed allocator world scope parents
        (ScopedInsertionSource.entry (firstCaller caller result temporary firstHandle secondHandle first second)
          (.var (joined caller result temporary firstHandle secondHandle first second)) firstHandle first) context origins pending)) := by
  have refined := joined_refined caller result temporary firstHandle secondHandle first second consistent
  have patternRigid : rigid program (.var temporary) = true := rfl
  simp only [firstCaller, joined, entry, source] at refined
  simp [Machine.run, ScopedQuerySource.machine, ScopedQuerySource.step, ScopedQuerySource.syntaxStep,
    ScopedQuerySource.constrainedCall, ScopedQuerySource.mutationCall, ScopedQuerySource.queryStep,
    placed, entry, source, scopeStep, enterCollapse?, enterSuperpose?, EagerDFS.Destination.machine,
    prepare, replace, installChild, retainChild, letGoals, patternRigid,
    ScopedInsertionSource.entry, firstCaller, joined, refined]

theorem result_fresh_after_first (caller : Control) (result temporary : String) (firstHandle secondHandle : NamedSpaces.Handle)
    (first second : Atom) (freshResult : FreshFor result caller.bindings) (distinct : temporary ≠ result) :
    FreshFor result (afterFirst caller result temporary firstHandle secondHandle first second).bindings := by
  have apart := joined_apart caller result temporary firstHandle secondHandle first second
  have afterAlias : FreshFor result (firstCaller caller result temporary firstHandle secondHandle first second).bindings := by
    intro pair member
    rcases List.mem_append.mp member with old | added
    · exact freshResult pair old
    · have same := List.mem_singleton.mp added
      subst pair
      simpa [encode, Mettapedia.Logic.LP.Term.freeVars] using And.intro distinct.symm apart.2.symm
  have locationFresh := fresh_for_goal_atom
    (ScopedInsertionSource.entry (firstCaller caller result temporary firstHandle secondHandle first second)
      (.var (joined caller result temporary firstHandle secondHandle first second)) firstHandle first) 0 (.var result)
    (by simp [ScopedInsertionSource.entry, firstCaller, Goal.atoms])
  have locationApart : result ≠ ScopedInsertionSource.location (firstCaller caller result temporary firstHandle secondHandle first second)
      (.var (joined caller result temporary firstHandle secondHandle first second)) firstHandle first := by
    exact Ne.symm (by simpa [ScopedInsertionSource.location, encode, Mettapedia.Logic.LP.Term.freeVars] using locationFresh)
  apply PresenceGuardSource.fresh_append_closed
  · apply PresenceGuardSource.fresh_append_closed
    · exact afterAlias
    · exact locationApart
    · exact LiteralQuerySource.handle_freeVars firstHandle
  · exact apart.2.symm
  · simp [Effects.boolean, encode, Mettapedia.Logic.LP.Term.freeVars]

theorem first_unbound (caller : Control) (result temporary : String) (firstHandle secondHandle : NamedSpaces.Handle)
    (first second : Atom) (principal : Environment) (resolved : resolve caller.bindings = some principal)
    (freshTemporary : FreshFor temporary caller.bindings) :
    ∃ environment representative, resolve (firstCaller caller result temporary firstHandle secondHandle first second).bindings = some environment ∧
      read environment (.var (joined caller result temporary firstHandle secondHandle first second)) = .var representative := by
  have apart : joined caller result temporary firstHandle secondHandle first second ∉ (encode (.var temporary)).freeVars := by
    simpa [encode, Mettapedia.Logic.LP.Term.freeVars] using (joined_apart caller result temporary firstHandle secondHandle first second).1
  obtain ⟨environment, representative, ready, temporaryUnbound⟩ := ScopedMutationSource.unbound_after_fresh_operand
    caller.bindings principal (.var temporary) (.var temporary) temporary (joined caller result temporary firstHandle secondHandle first second)
    resolved (ClosedOnceQueryFrame.fresh_read _ _ _ freshTemporary resolved)
    (joined_fresh caller result temporary firstHandle secondHandle first second) apart apart
  have equal := resolve_sound ready (.var temporary, .var (joined caller result temporary firstHandle secondHandle first second))
    (List.mem_append_right _ (by simp))
  exact ⟨environment, representative, ready, equal.symm.trans temporaryUnbound⟩

/-- The first effect is reached before the second insertion is entered.
This eight-step prefix keeps the exact world and pending source body. -/
theorem first_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (result temporary : String)
    (firstHandle secondHandle : NamedSpaces.Handle) (firstCode secondCode firstValue : Atom)
    (principal : Environment) (middle : Effects.State)
    (resolved : resolve caller.bindings = some principal) (freshTemporary : FreshFor temporary caller.bindings)
    (firstRead : read principal firstCode = firstValue)
    (firstClosed : ∀ environment, read environment firstValue = firstValue)
    (firstOrdinary : ScopedQuerySource.mutationPayload false firstValue = true)
    (insertedFirst : Effects.insert world.state firstHandle firstValue = some middle) :
    (ScopedQuerySource.machine .relational program).run 8
      (placed allocator world scope parents (entry caller result temporary firstHandle secondHandle firstCode secondCode) context origins pending) =
      ([], .exhausted (placed allocator {world with state := middle} scope parents
        (afterFirst caller result temporary firstHandle secondHandle firstCode secondCode) context (origins ++ [0]) pending)) := by
  obtain ⟨environment, representative, ready, joinedRead⟩ :=
    first_unbound caller result temporary firstHandle secondHandle firstCode secondCode principal resolved freshTemporary
  have inherited : Solves environment caller.bindings := by
    intro pair member
    exact resolve_sound ready pair (List.mem_append_left _ member)
  have payload := CapturedQueryOperands.resolved_forces resolved firstCode firstValue firstRead firstClosed environment inherited
  have inserted := ScopedInsertionSource.source_prefix program allocator world scope parents
    (firstCaller caller result temporary firstHandle secondHandle firstCode secondCode) context origins pending
    (.var (joined caller result temporary firstHandle secondHandle firstCode secondCode)) firstHandle firstCode firstValue
    environment representative middle ready joinedRead payload firstClosed firstOrdinary insertedFirst
  have began := preparation program allocator world scope parents caller context origins pending result temporary firstHandle secondHandle firstCode secondCode
    ⟨principal, resolve_sound resolved⟩
  have combined := (ScopedQuerySource.machine .relational program).established_and_pending 3 5 _ _ [] began
  rw [inserted] at combined
  simpa [afterFirst] using combined

theorem after_first_consistent (caller : Control) (result temporary : String)
    (firstHandle secondHandle : NamedSpaces.Handle) (firstCode secondCode : Atom)
    (principal : Environment) (resolved : resolve caller.bindings = some principal)
    (freshTemporary : FreshFor temporary caller.bindings) :
    ∃ environment, Solves environment (afterFirst caller result temporary firstHandle secondHandle firstCode secondCode).bindings := by
  obtain ⟨environment, representative, ready, joinedRead⟩ :=
    first_unbound caller result temporary firstHandle secondHandle firstCode secondCode principal resolved freshTemporary
  exact ScopedInsertionSource.returned_consistent (firstCaller caller result temporary firstHandle secondHandle firstCode secondCode)
    (.var (joined caller result temporary firstHandle secondHandle firstCode secondCode)) firstHandle firstCode
    environment representative ready joinedRead

/-- The complete authored body has thirteen source inspections: three for
the local let and five per insertion. Both effects and both result equations
are retained before the original caller resumes. -/
theorem source_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (result temporary : String)
    (firstHandle secondHandle : NamedSpaces.Handle) (firstCode secondCode firstValue secondValue : Atom)
    (principal : Environment) (middle after : Effects.State)
    (resolved : resolve caller.bindings = some principal)
    (freshTemporary : FreshFor temporary caller.bindings) (freshResult : FreshFor result caller.bindings)
    (distinct : temporary ≠ result)
    (firstRead : read principal firstCode = firstValue) (secondRead : read principal secondCode = secondValue)
    (firstClosed : ∀ environment, read environment firstValue = firstValue)
    (secondClosed : ∀ environment, read environment secondValue = secondValue)
    (firstOrdinary : ScopedQuerySource.mutationPayload false firstValue = true)
    (secondOrdinary : ScopedQuerySource.mutationPayload false secondValue = true)
    (insertedFirst : Effects.insert world.state firstHandle firstValue = some middle)
    (insertedSecond : Effects.insert middle secondHandle secondValue = some after) :
    (ScopedQuerySource.machine .relational program).run 13
      (placed allocator world scope parents (entry caller result temporary firstHandle secondHandle firstCode secondCode) context origins pending) =
      ([], .exhausted (placed allocator {world with state := after} scope parents
        (returned caller result temporary firstHandle secondHandle firstCode secondCode) context (origins ++ [0, 0]) pending)) := by
  have throughFirst := first_prefix program allocator world scope parents caller context origins pending result temporary
    firstHandle secondHandle firstCode secondCode firstValue principal middle resolved freshTemporary firstRead firstClosed firstOrdinary insertedFirst
  obtain ⟨secondEnvironment, secondResolved⟩ := resolve_complete
    (after_first_consistent caller result temporary firstHandle secondHandle firstCode secondCode principal resolved freshTemporary)
  have stillFresh := result_fresh_after_first caller result temporary firstHandle secondHandle firstCode secondCode freshResult distinct
  have resultRead := ClosedOnceQueryFrame.fresh_read _ result secondEnvironment stillFresh secondResolved
  have secondInherited : Solves secondEnvironment caller.bindings := by
    intro pair member
    exact resolve_sound secondResolved pair
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ member)))
  have secondPayload := CapturedQueryOperands.resolved_forces resolved secondCode secondValue secondRead secondClosed
    secondEnvironment secondInherited
  have secondRun := ScopedInsertionSource.source_prefix program allocator {world with state := middle} scope parents
    (secondCaller caller result temporary firstHandle secondHandle firstCode secondCode) context (origins ++ [0]) pending
    (.var result) secondHandle secondCode secondValue secondEnvironment result after secondResolved resultRead secondPayload
    secondClosed secondOrdinary insertedSecond
  change (ScopedQuerySource.machine .relational program).run 5
    (placed allocator {world with state := middle} scope parents
      (afterFirst caller result temporary firstHandle secondHandle firstCode secondCode) context (origins ++ [0]) pending) = _ at secondRun
  have combined := (ScopedQuerySource.machine .relational program).established_and_pending 8 5 _ _ [] throughFirst
  rw [secondRun] at combined
  simpa [returned, List.append_assoc] using combined

/-- If the second target is unavailable, the first publication and its
reached equations survive at an explicit reference-service boundary. -/
theorem second_unavailable_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (result temporary : String)
    (firstHandle secondHandle : NamedSpaces.Handle) (firstCode secondCode firstValue : Atom)
    (principal : Environment) (middle : Effects.State)
    (resolved : resolve caller.bindings = some principal) (freshTemporary : FreshFor temporary caller.bindings)
    (firstRead : read principal firstCode = firstValue)
    (firstClosed : ∀ environment, read environment firstValue = firstValue)
    (firstOrdinary : ScopedQuerySource.mutationPayload false firstValue = true)
    (insertedFirst : Effects.insert world.state firstHandle firstValue = some middle)
    (unavailable : middle.read secondHandle = none) :
    let later := secondCaller caller result temporary firstHandle secondHandle firstCode secondCode
    (ScopedQuerySource.machine .relational program).run 12
      (placed allocator world scope parents (entry caller result temporary firstHandle secondHandle firstCode secondCode) context origins pending) =
      ([], .suspended (.branch (.invoke "add-atom"
        [.var (ScopedInsertionSource.location later (.var result) secondHandle secondCode), secondCode] (.var result)))
        (placed allocator {world with state := middle} scope parents
          (ScopedInsertionSource.ready later (.var result) secondHandle secondCode) context (origins ++ [0]) pending)) := by
  dsimp only
  have first := first_prefix program allocator world scope parents caller context origins pending result temporary
    firstHandle secondHandle firstCode secondCode firstValue principal middle resolved freshTemporary firstRead firstClosed firstOrdinary insertedFirst
  have last := ScopedInsertionSource.unavailable_prefix program allocator {world with state := middle} scope parents
    (secondCaller caller result temporary firstHandle secondHandle firstCode secondCode) context (origins ++ [0]) pending
    (.var result) secondHandle secondCode
    (after_first_consistent caller result temporary firstHandle secondHandle firstCode secondCode principal resolved freshTemporary) unavailable
  change (ScopedQuerySource.machine .relational program).run 4
    (placed allocator {world with state := middle} scope parents
      (afterFirst caller result temporary firstHandle secondHandle firstCode secondCode) context (origins ++ [0]) pending) = _ at last
  have combined := (ScopedQuerySource.machine .relational program).established_and_pending 8 4 _ _ [] first
  rw [last] at combined
  simpa using combined

theorem returned_consistent (caller : Control) (result temporary : String) (firstHandle secondHandle : NamedSpaces.Handle)
    (first second : Atom) (principal : Environment) (resolved : resolve caller.bindings = some principal)
    (freshTemporary : FreshFor temporary caller.bindings) (freshResult : FreshFor result caller.bindings)
    (distinct : temporary ≠ result) :
    ∃ environment, Solves environment (returned caller result temporary firstHandle secondHandle first second).bindings := by
  obtain ⟨firstEnvironment, representative, firstResolved, joinedRead⟩ :=
    first_unbound caller result temporary firstHandle secondHandle first second principal resolved freshTemporary
  obtain ⟨secondEnvironment, secondResolved⟩ := resolve_complete
    (ScopedInsertionSource.returned_consistent (firstCaller caller result temporary firstHandle secondHandle first second)
      (.var (joined caller result temporary firstHandle secondHandle first second)) firstHandle first firstEnvironment representative firstResolved joinedRead)
  have stillFresh := result_fresh_after_first caller result temporary firstHandle secondHandle first second freshResult distinct
  exact ScopedInsertionSource.returned_consistent (secondCaller caller result temporary firstHandle secondHandle first second)
    (.var result) secondHandle second secondEnvironment result secondResolved
    (ClosedOnceQueryFrame.fresh_read _ result secondEnvironment stillFresh secondResolved)

theorem returned_value (caller : Control) (result temporary : String) (firstHandle secondHandle : NamedSpaces.Handle)
    (first second : Atom) (environment : Environment)
    (solved : Solves environment (returned caller result temporary firstHandle secondHandle first second).bindings) :
    read environment (.var result) = Effects.boolean true := by
  have bound := solved (Effects.boolean true, .var result) (List.mem_append_right _ (by simp))
  rw [PresenceGuardSource.read_boolean] at bound
  exact bound.symm

/-- Separate targets each receive their own occurrence; all other spaces and
the state-cell table remain unchanged. This is sequential publication, not a
claim that the two writes form one atomic transaction. -/
theorem separate_store_receipt (before middle after : Effects.State)
    (firstHandle secondHandle : NamedSpaces.Handle) (firstValue secondValue : Atom)
    (firstRows secondRows : List Atom) (distinct : firstHandle ≠ secondHandle)
    (firstSnapshot : before.read firstHandle = some firstRows) (secondSnapshot : before.read secondHandle = some secondRows)
    (insertedFirst : Effects.insert before firstHandle firstValue = some middle)
    (insertedSecond : Effects.insert middle secondHandle secondValue = some after) :
    after.read firstHandle = some (firstRows ++ [firstValue]) ∧
      after.read secondHandle = some (secondRows ++ [secondValue]) ∧
      (∀ other, other ≠ firstHandle → other ≠ secondHandle → after.read other = before.read other) ∧
      after.cells = before.cells := by
  obtain ⟨storedFirst, oldFirst, newFirst⟩ := Effects.insert_reads_back insertedFirst
  have firstEq : storedFirst = firstRows := Option.some.inj (oldFirst.symm.trans firstSnapshot)
  subst storedFirst
  have middleSecond := (Effects.insert_read_other insertedFirst distinct.symm).trans secondSnapshot
  obtain ⟨storedSecond, oldSecond, newSecond⟩ := Effects.insert_reads_back insertedSecond
  have secondEq : storedSecond = secondRows := Option.some.inj (oldSecond.symm.trans middleSecond)
  subst storedSecond
  refine ⟨(Effects.insert_read_other insertedSecond distinct).trans newFirst, newSecond, ?_, ?_⟩
  · intro other apartFirst apartSecond
    exact (Effects.insert_read_other insertedSecond apartSecond).trans (Effects.insert_read_other insertedFirst apartFirst)
  · exact (Effects.insert_preserves_cells insertedSecond).trans (Effects.insert_preserves_cells insertedFirst)

private theorem insert_read_append (before after : Effects.State) (target observed : NamedSpaces.Handle)
    (value : Atom) (inserted : Effects.insert before target value = some after) :
    after.read observed = (before.read observed).map
      (fun rows => rows ++ if observed = target then [value] else []) := by
  by_cases same : observed = target
  · subst observed
    obtain ⟨rows, initial, final⟩ := Effects.insert_reads_back inserted
    simp [initial, final]
  · rw [Effects.insert_read_other inserted same]
    cases before.read observed <;> simp [same]

/-- One observation law covers distinct targets and aliasing targets. Missing
unrelated handles remain missing; existing row order and duplicates survive. -/
theorem pair_store_receipt (before middle after : Effects.State)
    (firstHandle secondHandle : NamedSpaces.Handle) (firstValue secondValue : Atom)
    (insertedFirst : Effects.insert before firstHandle firstValue = some middle)
    (insertedSecond : Effects.insert middle secondHandle secondValue = some after)
    (observed : NamedSpaces.Handle) :
    after.read observed = (before.read observed).map (fun rows => rows ++
      (if observed = firstHandle then [firstValue] else []) ++
      (if observed = secondHandle then [secondValue] else [])) := by
  rw [insert_read_append middle after secondHandle observed secondValue insertedSecond,
    insert_read_append before middle firstHandle observed firstValue insertedFirst, Option.map_map]
  rfl

/-- Available source handles suffice to construct both primitive receipts;
the second availability is transported through the first actual insertion. -/
theorem pair_exists (before : Effects.State) (firstHandle secondHandle : NamedSpaces.Handle)
    (firstValue secondValue : Atom) (firstRows secondRows : List Atom)
    (firstSnapshot : before.read firstHandle = some firstRows)
    (secondSnapshot : before.read secondHandle = some secondRows) :
    ∃ middle after, Effects.insert before firstHandle firstValue = some middle ∧
      Effects.insert middle secondHandle secondValue = some after := by
  obtain ⟨middle, first⟩ := Effects.insert_exists_of_read_some firstSnapshot firstValue
  have available : ∃ rows, middle.read secondHandle = some rows := by
    by_cases same : secondHandle = firstHandle
    · subst secondHandle
      obtain ⟨rows, _initial, final⟩ := Effects.insert_reads_back first
      exact ⟨rows ++ [firstValue], final⟩
    · exact ⟨secondRows, (Effects.insert_read_other first same).trans secondSnapshot⟩
  obtain ⟨rows, readable⟩ := available
  obtain ⟨after, second⟩ := Effects.insert_exists_of_read_some readable secondValue
  exact ⟨middle, after, first, second⟩

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedInsertionSequence
