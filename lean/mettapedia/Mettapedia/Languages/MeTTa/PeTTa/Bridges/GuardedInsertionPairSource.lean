import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedPresenceSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedInsertionSequence

/-! Source candidates guarded by complete presence, followed by two ordered
insertions. Producer occurrences, fresh answers and allocation refusal are
distinct observations throughout the composition. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedInsertionPairSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open LiteralQuerySource (Request)
open ClosedOnceQueryFrame (FreshFor placed)

theorem goal_atom_support (control : Control) (atom : Atom) (name : String)
    (member : atom ∈ control.goals.flatMap Goal.atoms) (used : name ∈ (encode atom).freeVars) :
    name ∈ control.support := by
  apply Finset.mem_union_right
  apply (ClosedOnceQueryFrame.fold_support_iff _ _ _).mpr
  exact Or.inr ⟨atom, List.mem_cons_of_mem _ (List.mem_append_right _ member), used⟩

theorem prepend_support (control : Control) (leading : List Goal) :
    control.support ⊆ ({control with goals := leading ++ control.goals} : Control).support := by
  intro name member
  rcases Finset.mem_union.mp member with reserved | used
  · exact Finset.mem_union_left _ reserved
  · apply Finset.mem_union_right
    apply (ClosedOnceQueryFrame.fold_support_iff _ _ _).mpr
    rcases (ClosedOnceQueryFrame.fold_support_iff _ _ _).mp used with empty | ⟨atom, present, occurs⟩
    · exact (Finset.notMem_empty name empty).elim
    · refine Or.inr ⟨atom, ?_, occurs⟩
      rcases List.mem_cons.mp present with same | later
      · exact List.mem_cons.mpr (Or.inl same)
      · apply List.mem_cons_of_mem
        rcases List.mem_append.mp later with binding | goal
        · exact List.mem_append_left _ binding
        · apply List.mem_append_right
          rw [List.flatMap_append]
          exact List.mem_append_right _ goal

theorem fresh_apart_of_support (control : Control) (name : String) (index : Nat)
    (member : name ∈ control.support) : name ≠ freshName control index := by
  intro same
  exact freshName_not_mem control index (same ▸ member)

/-- Guard-local slots cannot capture a retained source name. Both entry and
waiting support are supplied by the actual branch syntax, not a caller oracle. -/
theorem retained_fresh (caller : Control) (destination : Atom) (request : Request) (yes no : Atom)
    (present : Bool) (name : String) (fresh : FreshFor name caller.bindings)
    (entryMember : name ∈ (PresenceConditionalSource.entry caller destination request yes no).support)
    (waitingMember : name ∈ (PresenceConditionalSource.waiting caller destination request yes no).support) :
    FreshFor name (PresenceConditionalSource.returned caller destination request yes no present).bindings := by
  let kept := PresenceConditionalSource.waiting caller destination request yes no
  let result := Atom.var (PresenceConditionalSource.slot caller destination request yes no)
  have conditionApart := fresh_apart_of_support (PresenceConditionalSource.entry caller destination request yes no)
    name 0 entryMember
  have notMember : name ∈ (PresenceGuardSource.start kept result request).support := by
    exact prepend_support kept [.evaluate (PresenceGuardSource.source request) result] waitingMember
  have argumentMember : name ∈ (PresenceGuardSource.equalityControl kept result request).support := by
    exact prepend_support kept _ waitingMember
  have notApart := fresh_apart_of_support (PresenceGuardSource.start kept result request) name 0 notMember
  have leftApart := fresh_apart_of_support (PresenceGuardSource.equalityControl kept result request) name 0 argumentMember
  have rightApart := fresh_apart_of_support (PresenceGuardSource.equalityControl kept result request) name 1 argumentMember
  apply PresenceGuardSource.fresh_append_closed
  · apply PresenceGuardSource.fresh_append_closed
    · apply PresenceGuardSource.fresh_append_closed
      · apply PresenceGuardSource.fresh_append_closed
        · exact fresh
        · exact leftApart
        · exact PresenceGuardSource.tuple_freeVars request present
      · exact rightApart
      · decide +kernel
    · exact notApart
    · simp [Effects.boolean, encode, Mettapedia.Logic.LP.Term.freeVars]
  · exact conditionApart
  · simp [Effects.boolean, encode, Mettapedia.Logic.LP.Term.freeVars]

theorem branch_name_retained (caller : Control) (destination : Atom) (request : Request) (yes no : Atom)
    (name : String) (member : name ∈ (encode no).freeVars) :
    name ∈ (PresenceConditionalSource.entry caller destination request yes no).support ∧
      name ∈ (PresenceConditionalSource.waiting caller destination request yes no).support := by
  constructor
  · apply goal_atom_support _ (PresenceConditionalSource.source request yes no) name (by simp [PresenceConditionalSource.entry, Goal.atoms])
    rw [PresenceConditionalSource.source, CapturedPatternSupport.mem_expression_names]
    exact ⟨no, by simp, member⟩
  · exact goal_atom_support _ no name (by simp [PresenceConditionalSource.waiting, Goal.atoms]) member

theorem destination_name_retained (caller : Control) (result : String) (request : Request) (yes no : Atom) :
    result ∈ (PresenceConditionalSource.entry caller (.var result) request yes no).support ∧
      result ∈ (PresenceConditionalSource.waiting caller (.var result) request yes no).support := by
  constructor
  · exact goal_atom_support _ (.var result) result (by simp [PresenceConditionalSource.entry, Goal.atoms])
      (by simp [encode, Mettapedia.Logic.LP.Term.freeVars])
  · exact goal_atom_support _ (.var result) result (by simp [PresenceConditionalSource.waiting, Goal.atoms])
      (by simp [encode, Mettapedia.Logic.LP.Term.freeVars])

def empty : Atom := .expression [.symbol "empty"]
def body (request : Request) (secondHandle : NamedSpaces.Handle) (temporary : String) (first second : Atom) : Atom :=
  ScopedInsertionSequence.source temporary request.handle secondHandle first second
def source (request : Request) (secondHandle : NamedSpaces.Handle) (temporary : String) (first second : Atom) : Atom :=
  CapturedPresenceSource.conditional request first empty (body request secondHandle temporary first second)
def entry (caller : Control) (result : String) (request : Request) (secondHandle : NamedSpaces.Handle) (temporary : String) (first second : Atom) : Control :=
  CapturedPresenceSource.conditionalEntry caller (.var result) request first empty (body request secondHandle temporary first second)
def afterGuard (caller : Control) (result : String) (request : Request) (secondHandle : NamedSpaces.Handle) (temporary : String) (first second : Atom) (present : Bool) : Control :=
  {(PresenceConditionalSource.returned caller (.var result) request empty (body request secondHandle temporary first second) present) with
    goals := caller.goals}

theorem after_guard_fresh (caller : Control) (result : String) (request : Request) (secondHandle : NamedSpaces.Handle) (temporary : String)
    (first second : Atom) (present : Bool) (freshTemporary : FreshFor temporary caller.bindings)
    (freshResult : FreshFor result caller.bindings) :
    FreshFor temporary (afterGuard caller result request secondHandle temporary first second present).bindings ∧
      FreshFor result (afterGuard caller result request secondHandle temporary first second present).bindings := by
  have temporaryUsed : temporary ∈ (encode (body request secondHandle temporary first second)).freeVars := by
    rw [body, ScopedInsertionSequence.source, CapturedPatternSupport.mem_expression_names]
    exact ⟨.var temporary, by simp, by simp [encode, Mettapedia.Logic.LP.Term.freeVars]⟩
  have tempNames := branch_name_retained caller (.var result) request empty (body request secondHandle temporary first second) temporary temporaryUsed
  have resultNames := destination_name_retained caller result request empty (body request secondHandle temporary first second)
  exact ⟨retained_fresh caller (.var result) request empty (body request secondHandle temporary first second) present temporary freshTemporary tempNames.1 tempNames.2,
    retained_fresh caller (.var result) request empty (body request secondHandle temporary first second) present result freshResult resultNames.1 resultNames.2⟩

theorem after_guard_consistent (caller : Control) (result : String) (request : Request) (secondHandle : NamedSpaces.Handle) (temporary : String)
    (first second : Atom) (present : Bool) (consistent : ∃ environment, Solves environment caller.bindings) :
    ∃ environment, Solves environment (afterGuard caller result request secondHandle temporary first second present).bindings :=
  ClosedOnceQueryFrame.refined_consistent _ _ _
    (PresenceConditionalSource.returned_refined caller (.var result) request empty (body request secondHandle temporary first second) present consistent)

theorem after_guard_inherited (caller : Control) (result : String) (request : Request) (secondHandle : NamedSpaces.Handle) (temporary : String)
    (first second : Atom) (present : Bool) (environment : Environment)
    (solved : Solves environment (afterGuard caller result request secondHandle temporary first second present).bindings) :
    Solves environment caller.bindings := by
  intro pair member
  exact solved pair (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ member))))

def afterInsert (caller : Control) (result : String) (request : Request) (secondHandle : NamedSpaces.Handle) (temporary : String) (first second : Atom) : Control :=
  ScopedInsertionSequence.returned (afterGuard caller result request secondHandle temporary first second false)
    result temporary request.handle secondHandle first second

/-- A genuinely absent candidate follows the actual guard and then both
insertions. The private guard has no witness to copy, even at zero copy
capacity. The caller resumes with the complete reached equations. -/
theorem fresh_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (result temporary : String)
    (request : Request) (secondHandle : NamedSpaces.Handle) (firstCode secondCode secondValue : Atom) (principal : Environment)
    (middle after : Effects.State)
    (resolved : resolve caller.bindings = some principal)
    (firstRead : read principal firstCode = request.pattern) (secondRead : read principal secondCode = secondValue)
    (secondClosed : ∀ environment, read environment secondValue = secondValue)
    (freshTemporary : FreshFor temporary caller.bindings) (freshResult : FreshFor result caller.bindings)
    (distinct : temporary ≠ result) (rows : List Atom) (snapshot : world.state.read request.handle = some rows)
    (closed : ClosedQueryAdmission.rowsReady request.pattern rows = true) (absent : request.pattern ∉ rows)
    (firstOrdinary : ScopedQuerySource.mutationPayload false request.pattern = true)
    (secondOrdinary : ScopedQuerySource.mutationPayload false secondValue = true)
    (insertedFirst : Effects.insert world.state request.handle request.pattern = some middle)
    (insertedSecond : Effects.insert middle secondHandle secondValue = some after) :
    (ScopedQuerySource.machine .relational program).run 32
      (placed allocator world scope parents (entry caller result request secondHandle temporary firstCode secondCode) context origins pending) =
      ([], .exhausted (placed allocator {world with state := after} scope parents
        (afterInsert caller result request secondHandle temporary firstCode secondCode) context (origins ++ [0, 0, 0, 0]) pending)) := by
  have tested := CapturedPresenceSource.conditional_prefix program allocator world scope parents caller context origins pending
    (.var result) request firstCode empty (body request secondHandle temporary firstCode secondCode) principal resolved firstRead rows snapshot closed
  simp only [absent, decide_false, CollectedOnceQuerySource.childBudget, Bool.false_eq_true, ↓reduceIte,
    PresenceGuardSource.copyAllocator] at tested
  change (ScopedQuerySource.machine .relational program).run 19
    (placed allocator world scope parents (entry caller result request secondHandle temporary firstCode secondCode) context origins pending) =
    ([], .exhausted (placed allocator world scope parents
      (ScopedInsertionSequence.entry (afterGuard caller result request secondHandle temporary firstCode secondCode false)
        result temporary request.handle secondHandle firstCode secondCode) context (origins ++ [0, 0]) pending)) at tested
  obtain ⟨environment, ready⟩ := resolve_complete (after_guard_consistent caller result request secondHandle temporary firstCode secondCode false
    ⟨principal, resolve_sound resolved⟩)
  have inherited := after_guard_inherited caller result request secondHandle temporary firstCode secondCode false environment (resolve_sound ready)
  obtain ⟨temporaryFresh, resultFresh⟩ := after_guard_fresh caller result request secondHandle temporary firstCode secondCode false freshTemporary freshResult
  have firstPayload := CapturedQueryOperands.resolved_forces resolved firstCode request.pattern firstRead
    (LiteralQuerySource.read_pattern request) environment inherited
  have secondPayload := CapturedQueryOperands.resolved_forces resolved secondCode secondValue secondRead secondClosed environment inherited
  have inserted := ScopedInsertionSequence.source_prefix program allocator world scope parents
    (afterGuard caller result request secondHandle temporary firstCode secondCode false) context (origins ++ [0, 0]) pending result temporary
    request.handle secondHandle firstCode secondCode request.pattern secondValue environment middle after ready temporaryFresh resultFresh distinct
    firstPayload secondPayload (LiteralQuerySource.read_pattern request) secondClosed firstOrdinary secondOrdinary insertedFirst insertedSecond
  have combined := (ScopedQuerySource.machine .relational program).established_and_pending 19 13 _ _ [] tested
  rw [inserted] at combined
  simpa [afterInsert, List.append_assoc] using combined

/-- A held candidate emits no body answer and performs no insertion. A
refused witness copy remains an allocation suspension, not zero progress. -/
theorem held_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (result temporary : String)
    (request : Request) (secondHandle : NamedSpaces.Handle) (firstCode secondCode : Atom) (principal : Environment)
    (resolved : resolve caller.bindings = some principal) (reading : read principal firstCode = request.pattern)
    (rows : List Atom) (snapshot : world.state.read request.handle = some rows)
    (closed : ClosedQueryAdmission.rowsReady request.pattern rows = true) (present : request.pattern ∈ rows) :
    (ScopedQuerySource.machine .relational program).run 24
      (placed allocator world scope parents (entry caller result request secondHandle temporary firstCode secondCode) context origins pending) =
      ([], match PresenceGuardSource.copyAllocator allocator true with
        | some next => .exhausted (next, ⟨world, {scope with frontier := pending} :: parents⟩)
        | none => .suspended .allocation (PresenceGuardSource.collectionEnd allocator world scope parents
            (PresenceConditionalSource.waiting caller (.var result) request empty (body request secondHandle temporary firstCode secondCode))
            context origins pending (.var (PresenceConditionalSource.slot caller (.var result) request empty (body request secondHandle temporary firstCode secondCode)))
            request true)) := by
  have tested := CapturedPresenceSource.conditional_prefix program allocator world scope parents caller context origins pending
    (.var result) request firstCode empty (body request secondHandle temporary firstCode secondCode) principal resolved reading rows snapshot closed
  simp only [present, decide_true, CollectedOnceQuerySource.childBudget, ↓reduceIte] at tested
  cases copied : PresenceGuardSource.copyAllocator allocator true with
  | none =>
      rw [copied] at tested
      have stable := (ScopedQuerySource.machine .relational program).run_stable 23 1 _ (fun residual => by rw [tested]; simp)
      rw [tested] at stable
      simpa only [entry] using stable
  | some next =>
      rw [copied] at tested
      let reached := PresenceConditionalSource.reached caller (.var result) request empty (body request secondHandle temporary firstCode secondCode) true
      have last : (ScopedQuerySource.machine .relational program).step
          (placed next world scope parents reached context (origins ++ [0, 0]) pending) =
          some (.silent (next, ⟨world, {scope with frontier := pending} :: parents⟩)) := by
        rw [ScopedQuerySource.Guards.placed_ordinary_step .relational program next world scope parents reached context
          (origins ++ [0, 0]) pending (.evaluate empty (.var result)) caller.goals rfl rfl]
        exact congrArg some (scope_empty .relational program next world _ parents reached context (origins ++ [0, 0]) pending
          (.var result) caller.goals rfl rfl)
      have combined := (ScopedQuerySource.machine .relational program).established_and_pending 23 1 _ _ [] tested
      rw [Machine.run_succ_silent _ last] at combined
      simpa [entry, Machine.run] using combined

theorem after_insert_consistent (caller : Control) (result : String) (request : Request) (secondHandle : NamedSpaces.Handle) (temporary : String)
    (first second : Atom) (principal : Environment) (resolved : resolve caller.bindings = some principal)
    (freshTemporary : FreshFor temporary caller.bindings) (freshResult : FreshFor result caller.bindings)
    (distinct : temporary ≠ result) :
    ∃ environment, Solves environment (afterInsert caller result request secondHandle temporary first second).bindings := by
  obtain ⟨environment, ready⟩ := resolve_complete (after_guard_consistent caller result request secondHandle temporary first second false
    ⟨principal, resolve_sound resolved⟩)
  obtain ⟨tempFresh, resultFresh⟩ := after_guard_fresh caller result request secondHandle temporary first second false freshTemporary freshResult
  exact ScopedInsertionSequence.returned_consistent (afterGuard caller result request secondHandle temporary first second false)
    result temporary request.handle secondHandle first second environment ready tempFresh resultFresh distinct

theorem after_insert_value (caller : Control) (result : String) (request : Request) (secondHandle : NamedSpaces.Handle) (temporary : String)
    (first second : Atom) (environment : Environment)
    (solved : Solves environment (afterInsert caller result request secondHandle temporary first second).bindings) :
    read environment (.var result) = Effects.boolean true :=
  ScopedInsertionSequence.returned_value (afterGuard caller result request secondHandle temporary first second false)
    result temporary request.handle secondHandle first second environment solved

/-- A fresh candidate delivers exactly one true answer, although it writes
two rows. Inside a collection this packet is recorded, not publicly emitted. -/
theorem fresh_return {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (result temporary : String)
    (request : Request) (secondHandle : NamedSpaces.Handle) (firstCode secondCode secondValue : Atom) (principal : Environment)
    (middle after : Effects.State)
    (resolved : resolve caller.bindings = some principal)
    (firstRead : read principal firstCode = request.pattern) (secondRead : read principal secondCode = secondValue)
    (secondClosed : ∀ environment, read environment secondValue = secondValue)
    (freshTemporary : FreshFor temporary caller.bindings) (freshResult : FreshFor result caller.bindings)
    (distinct : temporary ≠ result) (finished : caller.goals = []) (output : caller.destination = .var result)
    (rows : List Atom) (snapshot : world.state.read request.handle = some rows)
    (closed : ClosedQueryAdmission.rowsReady request.pattern rows = true) (absent : request.pattern ∉ rows)
    (firstOrdinary : ScopedQuerySource.mutationPayload false request.pattern = true)
    (secondOrdinary : ScopedQuerySource.mutationPayload false secondValue = true)
    (insertedFirst : Effects.insert world.state request.handle request.pattern = some middle)
    (insertedSecond : Effects.insert middle secondHandle secondValue = some after) :
    let answer : CollectedAnswer := ⟨Effects.boolean true, (afterInsert caller result request secondHandle temporary firstCode secondCode).bindings,
      origins ++ [0, 0, 0, 0], []⟩
    (ScopedQuerySource.machine .relational program).run 33
      (placed allocator world scope parents (entry caller result request secondHandle temporary firstCode secondCode) context origins pending) =
      (if scope.caller.isNone then [answer] else [],
        .exhausted (allocator, ⟨{world with state := after}, EagerDFS.Scope.record scope pending answer :: parents⟩)) := by
  dsimp only
  let returned := afterInsert caller result request secondHandle temporary firstCode secondCode
  let answer : CollectedAnswer := ⟨Effects.boolean true, returned.bindings, origins ++ [0, 0, 0, 0], []⟩
  let finalCursor : ScopedCursor Context := (allocator, ⟨{world with state := after}, EagerDFS.Scope.record scope pending answer :: parents⟩)
  obtain ⟨environment, ready⟩ := resolve_complete
    (after_insert_consistent caller result request secondHandle temporary firstCode secondCode principal resolved freshTemporary freshResult distinct)
  have value := after_insert_value caller result request secondHandle temporary firstCode secondCode environment (resolve_sound ready)
  have terminal : returned.goals = [] := finished
  have actualValue : read environment returned.destination = Effects.boolean true := by
    change read environment caller.destination = Effects.boolean true
    rw [output]
    exact value
  have last : (ScopedQuerySource.machine .relational program).step
      (placed allocator {world with state := after} scope parents returned context (origins ++ [0, 0, 0, 0]) pending) =
      some (if scope.caller.isNone then .publish [answer] finalCursor else .silent finalCursor) := by
    simp only [placed]
    rw [ScopedQuerySource.Guards.empty_goals_step .relational program allocator {world with state := after}
      {scope with frontier := (returned, context, origins ++ [0, 0, 0, 0]) :: pending} parents returned
      context (origins ++ [0, 0, 0, 0]) pending rfl terminal]
    have delivered := scope_terminal_value .relational program allocator {world with state := after}
      {scope with frontier := (returned, context, origins ++ [0, 0, 0, 0]) :: pending} parents returned context
      (origins ++ [0, 0, 0, 0]) pending environment rfl terminal ready
    simp only [actualValue] at delivered
    simpa [placed, answer, finalCursor, EagerDFS.Scope.record] using congrArg some delivered
  have finalStep : (ScopedQuerySource.machine .relational program).run 1
      (placed allocator {world with state := after} scope parents returned context (origins ++ [0, 0, 0, 0]) pending) =
      (if scope.caller.isNone then [answer] else [], .exhausted finalCursor) := by
    cases parent : scope.caller <;> simp [Machine.run, last, parent]
  have before := fresh_prefix program allocator world scope parents caller context origins pending result temporary request secondHandle
    firstCode secondCode secondValue principal middle after resolved firstRead secondRead secondClosed freshTemporary freshResult
    distinct rows snapshot closed absent firstOrdinary secondOrdinary insertedFirst insertedSecond
  have combined := (ScopedQuerySource.machine .relational program).established_and_pending 32 1 _ _ [] before
  rw [finalStep] at combined
  simpa only [List.nil_append] using combined

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedInsertionPairSource
