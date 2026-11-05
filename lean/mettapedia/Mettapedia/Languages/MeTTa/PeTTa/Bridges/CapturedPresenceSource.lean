import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedCollectedOnceSource

/-!
# Presence guards over captured source patterns

Only the raw query-pattern position is related to its principal literal
reading. The reached equations retain its names, so outer preparation uses
the existing literal guard's slots. After the captured child completes, the
existing copy boundary and Boolean readout apply to the identical state.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedPresenceSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open LiteralQuerySource (Request)
open ClosedOnceQueryFrame (FreshFor placed)
open CapturedPatternSupport (mem_expression_names evaluate_support source_names_retained literal_names_empty)

def equality (request : Request) (patternCode : Atom) : Atom :=
  .expression [.symbol "==", CapturedCollectedOnceSource.source request patternCode, .expression []]

def source (request : Request) (patternCode : Atom) : Atom :=
  .expression [.symbol "not", equality request patternCode]

def start (caller : Control) (destination : Atom) (request : Request) (patternCode : Atom) : Control :=
  {caller with goals := .evaluate (source request patternCode) destination :: caller.goals}

def equalityControl (caller : Control) (destination : Atom) (request : Request) (patternCode : Atom) : Control :=
  {caller with goals := [
    .evaluate (equality request patternCode) (.var (PresenceGuardSource.notSlot caller destination request)),
    .invoke "not" [.var (PresenceGuardSource.notSlot caller destination request)] destination] ++ caller.goals}

def collecting (caller : Control) (destination : Atom) (request : Request) (patternCode : Atom) : Control :=
  {caller with
    goals := .evaluate (CapturedCollectedOnceSource.source request patternCode)
      (.var (PresenceGuardSource.leftSlot caller destination request)) :: PresenceGuardSource.suffix caller destination request}

theorem collected_names (request : Request) (patternCode : Atom) :
    (encode (CapturedCollectedOnceSource.source request patternCode)).freeVars = (encode patternCode).freeVars := by
  ext name
  rw [CapturedCollectedOnceSource.source, mem_expression_names]
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  rw [CapturedPatternSupport.once_names]
  simp [encode, Mettapedia.Logic.LP.Term.freeVars]

theorem equality_names (request : Request) (patternCode : Atom) :
    (encode (equality request patternCode)).freeVars = (encode patternCode).freeVars := by
  ext name
  rw [equality, mem_expression_names]
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  rw [collected_names]
  simp [encode, Mettapedia.Logic.LP.Term.freeVars]

theorem source_names (request : Request) (patternCode : Atom) :
    (encode (source request patternCode)).freeVars = (encode patternCode).freeVars := by
  ext name
  rw [source, mem_expression_names]
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  rw [equality_names]
  simp [encode, Mettapedia.Logic.LP.Term.freeVars]

theorem start_support (caller : Control) (destination : Atom) (request : Request) (patternCode : Atom)
    (principal : Environment) (resolved : resolve caller.bindings = some principal)
    (reading : read principal patternCode = request.pattern) :
    (start caller destination request patternCode).support =
      (PresenceGuardSource.start caller destination request).support := by
  have bounded := source_names_retained caller principal patternCode request resolved reading
  change ({caller with goals := .evaluate (source request patternCode) destination :: caller.goals} : Control).support =
    ({caller with goals := .evaluate (source request request.pattern) destination :: caller.goals} : Control).support
  rw [evaluate_support, evaluate_support, source_names, source_names, literal_names_empty _ request.literal,
    Finset.union_eq_left.mpr bounded, Finset.union_empty]

theorem equality_support (caller : Control) (destination : Atom) (request : Request) (patternCode : Atom)
    (principal : Environment) (resolved : resolve caller.bindings = some principal)
    (reading : read principal patternCode = request.pattern) :
    (equalityControl caller destination request patternCode).support =
      (PresenceGuardSource.equalityControl caller destination request).support := by
  let base : Control := {caller with
    goals := .invoke "not" [.var (PresenceGuardSource.notSlot caller destination request)] destination :: caller.goals}
  have bounded := source_names_retained base principal patternCode request resolved reading
  change ({base with goals := .evaluate (equality request patternCode) (.var (PresenceGuardSource.notSlot caller destination request)) :: base.goals} : Control).support =
    ({base with goals := .evaluate (equality request request.pattern) (.var (PresenceGuardSource.notSlot caller destination request)) :: base.goals} : Control).support
  rw [evaluate_support, evaluate_support, equality_names, equality_names, literal_names_empty _ request.literal,
    Finset.union_eq_left.mpr bounded, Finset.union_empty]

theorem collecting_support (caller : Control) (destination : Atom) (request : Request) (patternCode : Atom)
    (principal : Environment) (resolved : resolve caller.bindings = some principal)
    (reading : read principal patternCode = request.pattern) :
    (collecting caller destination request patternCode).support =
      (PresenceGuardSource.collecting caller destination request).support := by
  let base : Control := {caller with goals := PresenceGuardSource.suffix caller destination request}
  have bounded := source_names_retained base principal patternCode request resolved reading
  change ({base with goals := .evaluate (CapturedCollectedOnceSource.source request patternCode) (.var (PresenceGuardSource.leftSlot caller destination request)) :: base.goals} : Control).support =
    ({base with goals := .evaluate (CapturedCollectedOnceSource.source request request.pattern) (.var (PresenceGuardSource.leftSlot caller destination request)) :: base.goals} : Control).support
  rw [evaluate_support, evaluate_support, collected_names, collected_names, literal_names_empty _ request.literal,
    Finset.union_eq_left.mpr bounded, Finset.union_empty]

theorem not_slot (caller : Control) (destination : Atom) (request : Request) (patternCode : Atom)
    (principal : Environment) (resolved : resolve caller.bindings = some principal)
    (reading : read principal patternCode = request.pattern) :
    freshName (start caller destination request patternCode) 0 = PresenceGuardSource.notSlot caller destination request := by
  simp only [freshName, start_support caller destination request patternCode principal resolved reading, PresenceGuardSource.notSlot]

theorem equality_slot (caller : Control) (destination : Atom) (request : Request) (patternCode : Atom)
    (principal : Environment) (resolved : resolve caller.bindings = some principal)
    (reading : read principal patternCode = request.pattern) (index : Nat) :
    freshName (equalityControl caller destination request patternCode) index =
      freshName (PresenceGuardSource.equalityControl caller destination request) index := by
  simp only [freshName, equality_support caller destination request patternCode principal resolved reading]

set_option maxHeartbeats 1200000 in
theorem preparation {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom)
    (request : Request) (patternCode : Atom) (principal : Environment)
    (resolved : resolve caller.bindings = some principal) (reading : read principal patternCode = request.pattern) :
    (ScopedQuerySource.machine .relational program).run 2
      (placed allocator world scope parents (start caller destination request patternCode) context origins pending) =
      ([], .exhausted (placed allocator world scope parents (collecting caller destination request patternCode) context origins pending)) := by
  have firstName := not_slot caller destination request patternCode principal resolved reading
  have leftName := equality_slot caller destination request patternCode principal resolved reading 0
  have rightName := equality_slot caller destination request patternCode principal resolved reading 1
  simp only [start, source, equalityControl, equality, PresenceGuardSource.notSlot,
    PresenceGuardSource.start, PresenceGuardSource.source, PresenceGuardSource.equalityControl,
    PresenceGuardSource.equality, List.cons_append, List.nil_append] at firstName leftName rightName
  simp [Machine.run, ScopedQuerySource.machine, ScopedQuerySource.step, ScopedQuerySource.syntaxStep,
    ScopedQuerySource.constrainedCall, ScopedQuerySource.mutationCall, ScopedQuerySource.queryStep,
    placed, start, source, equality, scopeStep, enterCollapse?, enterSuperpose?, EagerDFS.Destination.machine,
    prepare, replace, installChild, retainChild, callable, StdLib.known, Eval.ioHead, callArguments,
    freshSlots, List.range_succ, Eval.argumentIsRaw, StdLib.rawArgument, collecting,
    PresenceGuardSource.suffix, PresenceGuardSource.notSlot, PresenceGuardSource.leftSlot,
    PresenceGuardSource.rightSlot, PresenceGuardSource.start, PresenceGuardSource.source,
    PresenceGuardSource.equalityControl, PresenceGuardSource.equality, firstName, leftName, rightName]

def collectionScope {Context : Type} (scope : CollectionScope Context) (caller : Control)
    (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (destination : Atom) (request : Request) (patternCode : Atom) : CollectionScope Context :=
  {scope with frontier := (collecting caller destination request patternCode, context, origins) :: pending}

theorem collection_support {Context : Type} (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom)
    (request : Request) (patternCode : Atom) (principal : Environment)
    (resolved : resolve caller.bindings = some principal) (reading : read principal patternCode = request.pattern) :
    collectionSupport ⟨world, collectionScope scope caller context origins pending destination request patternCode :: parents⟩ =
      collectionSupport ⟨world, PresenceGuardSource.collectionScope scope caller context origins pending destination request :: parents⟩ := by
  simp only [collectionSupport, List.foldr_cons, CollectionScope.support, collectionScope,
    PresenceGuardSource.collectionScope, List.foldr_cons,
    collecting_support caller destination request patternCode principal resolved reading]

/-- Once the child syntax has been consumed, the full retained source cursor
is the existing literal guard's collection endpoint, before any copy attempt. -/
theorem completed_eq {Context : Type} (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom)
    (request : Request) (patternCode : Atom) (principal : Environment) (present : Bool)
    (resolved : resolve caller.bindings = some principal) (reading : read principal patternCode = request.pattern) :
    CollectedOnceQuerySource.completed allocator world
      (collectionScope scope caller context origins pending destination request patternCode) parents
      (collecting caller destination request patternCode) context origins pending
      (.var (PresenceGuardSource.leftSlot caller destination request)) (PresenceGuardSource.suffix caller destination request)
      request present =
    PresenceGuardSource.collectionEnd allocator world scope parents caller context origins pending destination request present := by
  have boundary := collection_support world scope parents caller context origins pending destination request patternCode principal resolved reading
  have names := collecting_support caller destination request patternCode principal resolved reading
  have child : childName (collecting caller destination request patternCode)
      (collectionSupport ⟨world, collectionScope scope caller context origins pending destination request patternCode :: parents⟩) =
    childName (PresenceGuardSource.collecting caller destination request)
      (collectionSupport ⟨world, PresenceGuardSource.collectionScope scope caller context origins pending destination request :: parents⟩) := by
    change freshName (protectControl _ _) 0 = freshName (protectControl _ _) 0
    simp only [freshName, protectControl_support, boundary, names]
  rw [boundary] at child
  simp only [PresenceGuardSource.collectionEnd, CollectedOnceQuerySource.completed, CollectedOnceQuerySource.frame,
    boundary, names, child]
  simp only [collectionScope, PresenceGuardSource.collectionScope, CollectedOnceQuerySource.caller,
    collecting, PresenceGuardSource.collecting]

theorem source_to_copy_boundary {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom)
    (request : Request) (patternCode : Atom) (principal : Environment)
    (resolved : resolve caller.bindings = some principal) (reading : read principal patternCode = request.pattern)
    (rows : List Atom) (snapshot : world.state.read request.handle = some rows)
    (closed : ClosedQueryAdmission.rowsReady request.pattern rows = true) :
    let present := decide (request.pattern ∈ rows)
    (ScopedQuerySource.machine .relational program).run (CollectedOnceQuerySource.childBudget present + 4)
      (placed allocator world scope parents (start caller destination request patternCode) context origins pending) =
      ([], match PresenceGuardSource.copyAllocator allocator present with
        | some next => .exhausted (placed next world scope parents
            (PresenceGuardSource.afterCopy caller destination request present) context origins pending)
        | none => .suspended .allocation
            (PresenceGuardSource.collectionEnd allocator world scope parents caller context origins pending destination request present)) := by
  dsimp only
  have queried := CapturedCollectedOnceSource.source_return_boundary program allocator world
    (collectionScope scope caller context origins pending destination request patternCode) parents
    (collecting caller destination request patternCode) context origins pending
    (.var (PresenceGuardSource.leftSlot caller destination request)) (PresenceGuardSource.suffix caller destination request)
    request patternCode principal rfl rfl resolved reading rows snapshot closed
  dsimp only at queried
  rw [completed_eq allocator world scope parents caller context origins pending destination request patternCode principal _ resolved reading,
    PresenceGuardSource.finish_collectionEnd] at queried
  have combined := (ScopedQuerySource.machine .relational program).established_and_pending
    2 (CollectedOnceQuerySource.childBudget (decide (request.pattern ∈ rows)) + 2) _ _ []
    (preparation program allocator world scope parents caller context origins pending destination request patternCode principal resolved reading)
  change (ScopedQuerySource.machine .relational program).run _
    (placed allocator world scope parents (collecting caller destination request patternCode) context origins pending) = _ at queried
  rw [queried] at combined
  have count : 2 + (CollectedOnceQuerySource.childBudget (decide (request.pattern ∈ rows)) + 2) =
    CollectedOnceQuerySource.childBudget (decide (request.pattern ∈ rows)) + 4 := by omega
  rw [count] at combined
  cases copied : PresenceGuardSource.copyAllocator allocator (decide (request.pattern ∈ rows)) <;>
    simpa [copied] using combined

theorem source_guard_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (result : String)
    (request : Request) (patternCode : Atom) (principal : Environment)
    (resolved : resolve caller.bindings = some principal) (reading : read principal patternCode = request.pattern)
    (rows : List Atom) (snapshot : world.state.read request.handle = some rows)
    (closed : ClosedQueryAdmission.rowsReady request.pattern rows = true)
    (freshResult : FreshFor result (PresenceGuardSource.comparisonBindings caller (.var result) request
      (decide (request.pattern ∈ rows)))) :
    let present := decide (request.pattern ∈ rows)
    (ScopedQuerySource.machine .relational program).run (CollectedOnceQuerySource.childBudget present + 10)
      (placed allocator world scope parents (start caller (.var result) request patternCode) context origins pending) =
      ([], match PresenceGuardSource.copyAllocator allocator present with
        | some next => .exhausted (placed next world scope parents
            (PresenceGuardSource.delivered caller (.var result) request present) context (origins ++ [0, 0]) pending)
        | none => .suspended .allocation
            (PresenceGuardSource.collectionEnd allocator world scope parents caller context origins pending (.var result) request present)) := by
  dsimp only
  have returned := source_to_copy_boundary program allocator world scope parents caller context origins pending
    (.var result) request patternCode principal resolved reading rows snapshot closed
  dsimp only at returned
  cases copied : PresenceGuardSource.copyAllocator allocator (decide (request.pattern ∈ rows)) with
  | some next =>
      rw [copied] at returned
      have combined := (ScopedQuerySource.machine .relational program).established_and_pending
        (CollectedOnceQuerySource.childBudget (decide (request.pattern ∈ rows)) + 4) 6 _ _ [] returned
      rw [ScopedQuerySource.Guards.readout_prefix program next world scope parents caller context origins pending result request _
        ⟨principal, resolve_sound resolved⟩ freshResult] at combined
      simpa only [List.nil_append, Nat.add_assoc] using combined
  | none =>
      rw [copied] at returned
      have stable := (ScopedQuerySource.machine .relational program).run_stable
        (CollectedOnceQuerySource.childBudget (decide (request.pattern ∈ rows)) + 4) 6
        (placed allocator world scope parents (start caller (.var result) request patternCode) context origins pending)
        (fun residual => by rw [returned]; simp)
      rw [returned] at stable
      simpa only [Nat.add_assoc] using stable

def conditional (request : Request) (patternCode yes no : Atom) : Atom :=
  .expression [.symbol "if", source request patternCode, yes, no]

def conditionalEntry (caller : Control) (destination : Atom) (request : Request) (patternCode yes no : Atom) : Control :=
  {caller with goals := .evaluate (conditional request patternCode yes no) destination :: caller.goals}

theorem conditional_names (request : Request) (patternCode yes no : Atom) :
    (encode (conditional request patternCode yes no)).freeVars =
      (encode patternCode).freeVars ∪ (encode yes).freeVars ∪ (encode no).freeVars := by
  ext name
  rw [conditional, mem_expression_names]
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  rw [source_names]
  simp [encode, Mettapedia.Logic.LP.Term.freeVars]

theorem conditional_support (caller : Control) (destination : Atom) (request : Request) (patternCode yes no : Atom)
    (principal : Environment) (resolved : resolve caller.bindings = some principal)
    (reading : read principal patternCode = request.pattern) :
    (conditionalEntry caller destination request patternCode yes no).support =
      (PresenceConditionalSource.entry caller destination request yes no).support := by
  have bounded := source_names_retained caller principal patternCode request resolved reading
  change ({caller with goals := .evaluate (conditional request patternCode yes no) destination :: caller.goals} : Control).support =
    ({caller with goals := .evaluate (conditional request request.pattern yes no) destination :: caller.goals} : Control).support
  rw [evaluate_support, evaluate_support, conditional_names, conditional_names, literal_names_empty _ request.literal]
  simp only [← Finset.union_assoc, Finset.union_empty, Finset.union_eq_left.mpr bounded]

theorem conditional_slot (caller : Control) (destination : Atom) (request : Request) (patternCode yes no : Atom)
    (principal : Environment) (resolved : resolve caller.bindings = some principal)
    (reading : read principal patternCode = request.pattern) :
    freshName (conditionalEntry caller destination request patternCode yes no) 0 =
      PresenceConditionalSource.slot caller destination request yes no := by
  simp only [freshName, conditional_support caller destination request patternCode yes no principal resolved reading,
    PresenceConditionalSource.slot]

theorem conditional_entry_step {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom)
    (request : Request) (patternCode yes no : Atom) (principal : Environment)
    (resolved : resolve caller.bindings = some principal) (reading : read principal patternCode = request.pattern) :
    (ScopedQuerySource.machine .relational program).step
      (placed allocator world scope parents (conditionalEntry caller destination request patternCode yes no) context origins pending) =
      some (.silent (placed allocator world scope parents
        (start (PresenceConditionalSource.waiting caller destination request yes no)
          (.var (PresenceConditionalSource.slot caller destination request yes no)) request patternCode) context origins pending)) := by
  have name := conditional_slot caller destination request patternCode yes no principal resolved reading
  simp only [conditionalEntry, conditional, PresenceConditionalSource.slot,
    PresenceConditionalSource.entry, PresenceConditionalSource.source] at name
  simp [ScopedQuerySource.machine, ScopedQuerySource.step, ScopedQuerySource.syntaxStep,
    ScopedQuerySource.constrainedCall, ScopedQuerySource.mutationCall, ScopedQuerySource.queryStep,
    placed, conditionalEntry, conditional, scopeStep, enterCollapse?, enterSuperpose?,
    EagerDFS.Destination.machine, prepare, replace, installChild, retainChild, start,
    PresenceConditionalSource.waiting, PresenceConditionalSource.slot,
    PresenceConditionalSource.entry, PresenceConditionalSource.source, name]

/-- Arbitrary authored branches stay pending until the captured guard returns.
The unselected branch is never evaluated, including at an allocation pause. -/
theorem conditional_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom)
    (request : Request) (patternCode yes no : Atom) (principal : Environment)
    (resolved : resolve caller.bindings = some principal) (reading : read principal patternCode = request.pattern)
    (rows : List Atom) (snapshot : world.state.read request.handle = some rows)
    (closed : ClosedQueryAdmission.rowsReady request.pattern rows = true) :
    let present := decide (request.pattern ∈ rows)
    let kept := PresenceConditionalSource.waiting caller destination request yes no
    let result := Atom.var (PresenceConditionalSource.slot caller destination request yes no)
    (ScopedQuerySource.machine .relational program).run (1 + (CollectedOnceQuerySource.childBudget present + 10) + 2)
      (placed allocator world scope parents (conditionalEntry caller destination request patternCode yes no) context origins pending) =
      ([], match PresenceGuardSource.copyAllocator allocator present with
        | some next => .exhausted (placed next world scope parents
            (PresenceConditionalSource.reached caller destination request yes no present) context (origins ++ [0, 0]) pending)
        | none => .suspended .allocation
            (PresenceGuardSource.collectionEnd allocator world scope parents kept context origins pending result request present)) := by
  dsimp only
  have first : (ScopedQuerySource.machine .relational program).run 1
      (placed allocator world scope parents (conditionalEntry caller destination request patternCode yes no) context origins pending) =
      ([], .exhausted (placed allocator world scope parents
        (start (PresenceConditionalSource.waiting caller destination request yes no)
          (.var (PresenceConditionalSource.slot caller destination request yes no)) request patternCode) context origins pending)) := by
    rw [Machine.run_succ_silent _ (conditional_entry_step program allocator world scope parents caller context origins pending
      destination request patternCode yes no principal resolved reading)]
    rfl
  have queried := source_guard_prefix program allocator world scope parents
    (PresenceConditionalSource.waiting caller destination request yes no) context origins pending
    (PresenceConditionalSource.slot caller destination request yes no) request patternCode principal resolved reading rows snapshot closed
    (PresenceConditionalSource.slot_fresh caller destination request yes no _)
  dsimp only at queried
  have joined := (ScopedQuerySource.machine .relational program).established_and_pending 1
    (CollectedOnceQuerySource.childBudget (decide (request.pattern ∈ rows)) + 10) _ _ [] first
  rw [queried] at joined
  simp only [List.nil_append] at joined
  cases copied : PresenceGuardSource.copyAllocator allocator (decide (request.pattern ∈ rows)) with
  | none =>
      rw [copied] at joined
      have stable := (ScopedQuerySource.machine .relational program).run_stable _ 2 _ (fun residual => by rw [joined]; simp)
      rw [joined] at stable
      exact stable
  | some next =>
      rw [copied] at joined
      have last := (ScopedQuerySource.machine .relational program).established_and_pending _ 2 _ _ [] joined
      rw [ScopedQuerySource.Guards.conditional_select program next world scope parents caller context (origins ++ [0, 0]) pending
        destination request yes no _ ⟨principal, resolve_sound resolved⟩] at last
      exact last

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedPresenceSource
