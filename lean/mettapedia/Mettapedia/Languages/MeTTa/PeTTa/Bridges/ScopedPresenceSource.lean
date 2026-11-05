import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedOnceSource

/-! Collected literal presence in the captured-query source profile, retaining
the source allocator and caller at both successful and refused copy boundaries. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource.Guards

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open LiteralQuerySource (Request)
open ClosedOnceQueryFrame (placed FreshFor)
open CollectedOnceQuerySource

theorem collected_child_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom) (older : List Goal)
    (request : Request) (consistent : ∃ environment, Solves environment control.bindings)
    (rows : List Atom) (snapshot : world.state.read request.handle = some rows)
    (closed : ClosedQueryAdmission.rowsReady request.pattern rows = true) :
    let present := decide (request.pattern ∈ rows)
    (machine .relational program).run (childBudget present)
      (entered allocator world scope parents control context origins pending destination older request) =
      ([], .exhausted (completed allocator world scope parents control context origins pending destination older request present)) := by
  let childFrame := frame control (collectionSupport ⟨world, scope :: parents⟩)
  let childScope : CollectionScope Context := {frontier := [], caller := some (caller control destination older context origins)}
  let parentScopes := {scope with frontier := pending} :: parents
  have entry := framed_entry program allocator world childScope parentScopes childFrame context origins [] request consistent
  by_cases present : request.pattern ∈ rows
  · have hit := framed_hit program allocator world childScope parentScopes childFrame context origins [] request
      consistent (frame_fresh _ _) rows snapshot closed present
    have actual := (machine .relational program).established_and_pending 5 5 _ _ [] entry
    rw [hit] at actual
    simpa [childBudget, present, entered, EagerDFS.Scope.enter, placed, completed, childScope,
      parentScopes, childFrame, frame_initial, EagerDFS.Scope.record] using actual
  · have missed := framed_miss program allocator world childScope parentScopes childFrame context origins [] request
      consistent rows snapshot closed present
    have actual := (machine .relational program).established_and_pending 5 1 _ _ [] entry
    rw [Machine.run_succ_silent _ missed] at actual
    simpa [childBudget, present, entered, EagerDFS.Scope.enter, placed, completed, childScope,
      parentScopes, childFrame, frame_initial, Machine.run] using actual

theorem collected_source_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom) (older : List Goal)
    (request : Request)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (head : control.goals = .evaluate (source request) destination :: older)
    (consistent : ∃ environment, Solves environment control.bindings) (rows : List Atom)
    (snapshot : world.state.read request.handle = some rows)
    (closed : ClosedQueryAdmission.rowsReady request.pattern rows = true) :
    let present := decide (request.pattern ∈ rows)
    (machine .relational program).run (childBudget present + 1) (allocator, ⟨world, scope :: parents⟩) =
      ([], .exhausted (completed allocator world scope parents control context origins pending destination older request present)) := by
  dsimp only
  have entry : (machine .relational program).step (allocator, ⟨world, scope :: parents⟩) =
      some (.silent (entered allocator world scope parents control context origins pending destination older request)) := by
    rw [ordinary_step .relational program allocator world scope parents control context origins pending
      (.evaluate (source request) destination) older frontier head rfl,
      entry_step program allocator world scope parents control context origins pending destination older request frontier head]
  rw [Machine.run_succ_silent _ entry]
  exact collected_child_prefix program allocator world scope parents control context origins pending destination older request
    consistent rows snapshot closed

theorem collected_return_boundary {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom) (older : List Goal)
    (request : Request)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (head : control.goals = .evaluate (source request) destination :: older)
    (consistent : ∃ environment, Solves environment control.bindings) (rows : List Atom)
    (snapshot : world.state.read request.handle = some rows)
    (closed : ClosedQueryAdmission.rowsReady request.pattern rows = true) :
    let present := decide (request.pattern ∈ rows)
    let retained := completed allocator world scope parents control context origins pending destination older request present
    (machine .relational program).run (childBudget present + 2) (allocator, ⟨world, scope :: parents⟩) =
      ([], match finishAllocated? retained with
        | some next => .exhausted next
        | none => .suspended .allocation retained) := by
  dsimp only
  have reached := collected_source_prefix program allocator world scope parents control context origins pending destination older
    request frontier head consistent rows snapshot closed
  have composed := (machine .relational program).established_and_pending
    (childBudget (decide (request.pattern ∈ rows)) + 1) 1 _ _ [] reached
  let retained := completed allocator world scope parents control context origins pending destination older
    request (decide (request.pattern ∈ rows))
  have actual : (machine .relational program).step retained =
      some (match finishAllocated? retained with
        | some next => .silent next
        | none => .call .allocation retained) := by
    have same : (machine .relational program).step retained = some (scopeStep .relational program retained) := by
      exact empty_frontier_step .relational program allocator world _ _ rfl
    rw [same]
    exact congrArg some (completed_step program allocator world scope parents control context origins pending destination older
      request (decide (request.pattern ∈ rows)))
  have one : (machine .relational program).run 1 retained =
      ([], match finishAllocated? retained with
        | some next => .exhausted next
        | none => .suspended .allocation retained) := by
    cases allocated : finishAllocated? retained <;> simp only [Machine.run, actual, allocated]
  rw [one] at composed
  simpa only [List.nil_append, Nat.add_assoc] using composed

open PresenceGuardSource

set_option maxHeartbeats 1200000 in
theorem guard_to_collection {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom) (request : Request) :
    (machine .relational program).run 2
      (placed allocator world scope parents (start caller destination request) context origins pending) =
      ([], .exhausted (placed allocator world scope parents (collecting caller destination request) context origins pending)) := by
  simp [Machine.run, machine, step, syntaxStep, constrainedCall, mutationCall, queryStep,
    placed, PresenceGuardSource.start, PresenceGuardSource.source, equality, scopeStep, enterCollapse?, enterSuperpose?,
    EagerDFS.Destination.machine, prepare, replace, installChild, retainChild, callable, StdLib.known, Eval.ioHead,
    callArguments, freshSlots, List.range_succ, Eval.argumentIsRaw, StdLib.rawArgument,
    collecting, suffix, notSlot, leftSlot, rightSlot, equalityControl]

theorem guard_to_copy_boundary {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom) (request : Request)
    (consistent : ∃ environment, Solves environment caller.bindings)
    (rows : List Atom) (snapshot : world.state.read request.handle = some rows)
    (closed : ClosedQueryAdmission.rowsReady request.pattern rows = true) :
    let present := decide (request.pattern ∈ rows)
    (machine .relational program).run (childBudget present + 4)
      (placed allocator world scope parents (start caller destination request) context origins pending) =
      ([], match copyAllocator allocator present with
        | some next => .exhausted (placed next world scope parents (afterCopy caller destination request present) context origins pending)
        | none => .suspended .allocation
            (collectionEnd allocator world scope parents caller context origins pending destination request present)) := by
  dsimp only
  have queried := collected_return_boundary program allocator world
    (collectionScope scope caller context origins pending destination request) parents
    (collecting caller destination request) context origins pending (.var (leftSlot caller destination request))
    (suffix caller destination request) request rfl rfl consistent rows snapshot closed
  have composed := (machine .relational program).established_and_pending
    2 (childBudget (decide (request.pattern ∈ rows)) + 2) _ _ []
    (guard_to_collection program allocator world scope parents caller context origins pending destination request)
  change (machine .relational program).run (childBudget (decide (request.pattern ∈ rows)) + 2)
    (placed allocator world scope parents (collecting caller destination request) context origins pending) =
    ([], match finishAllocated? (collectionEnd allocator world scope parents caller context origins pending
      destination request (decide (request.pattern ∈ rows))) with
      | some next => .exhausted next
      | none => .suspended .allocation _) at queried
  rw [queried, finish_collectionEnd] at composed
  have count : 2 + (childBudget (decide (request.pattern ∈ rows)) + 2) =
      childBudget (decide (request.pattern ∈ rows)) + 4 := by omega
  rw [count] at composed
  cases copied : copyAllocator allocator (decide (request.pattern ∈ rows)) <;>
    simpa [copied, collectionEnd] using composed

/-- The complete presence guard keeps the source's generative copy boundary.
A missing copy budget suspends there; it cannot become a false answer. -/
theorem guard_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (result : String) (request : Request)
    (consistent : ∃ environment, Solves environment caller.bindings)
    (rows : List Atom) (snapshot : world.state.read request.handle = some rows)
    (closed : ClosedQueryAdmission.rowsReady request.pattern rows = true)
    (freshResult : FreshFor result (comparisonBindings caller (.var result) request (decide (request.pattern ∈ rows)))) :
    let present := decide (request.pattern ∈ rows)
    (machine .relational program).run (childBudget present + 10)
      (placed allocator world scope parents (start caller (.var result) request) context origins pending) =
      ([], match copyAllocator allocator present with
        | some next => .exhausted (placed next world scope parents (delivered caller (.var result) request present)
            context (origins ++ [0, 0]) pending)
        | none => .suspended .allocation
            (collectionEnd allocator world scope parents caller context origins pending (.var result) request present)) := by
  dsimp only
  have returned := guard_to_copy_boundary program allocator world scope parents caller context origins pending
    (.var result) request consistent rows snapshot closed
  dsimp only at returned
  cases copied : copyAllocator allocator (decide (request.pattern ∈ rows)) with
  | some next =>
      rw [copied] at returned
      have composed := (machine .relational program).established_and_pending
        (childBudget (decide (request.pattern ∈ rows)) + 4) 6 _ _ [] returned
      rw [readout_prefix program next world scope parents caller context origins pending result request _ consistent freshResult] at composed
      simpa only [List.nil_append, Nat.add_assoc] using composed
  | none =>
      rw [copied] at returned
      have stable := (machine .relational program).run_stable
        (childBudget (decide (request.pattern ∈ rows)) + 4) 6
        (placed allocator world scope parents (start caller (.var result) request) context origins pending)
        (fun residual => by rw [returned]; simp)
      rw [returned] at stable
      simpa only [Nat.add_assoc] using stable

theorem conditional_select {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom)
    (request : Request) (yes no : Atom) (present : Bool)
    (consistent : ∃ environment, Solves environment caller.bindings) :
    (machine .relational program).run 2
      (placed allocator world scope parents
        (delivered (PresenceConditionalSource.waiting caller destination request yes no)
          (.var (PresenceConditionalSource.slot caller destination request yes no)) request present) context origins pending) =
      ([], .exhausted (placed allocator world scope parents
        (PresenceConditionalSource.reached caller destination request yes no present) context origins pending)) := by
  have refined := PresenceConditionalSource.returned_refined caller destination request yes no present consistent
  obtain ⟨environment, resolved⟩ := resolve_complete (ClosedOnceQueryFrame.refined_consistent _ _ _ refined)
  have value := bound_closed_value _ (Effects.boolean present)
    (PresenceConditionalSource.slot caller destination request yes no) environment resolved (by simp) (read_boolean present environment)
  let kept := PresenceConditionalSource.waiting caller destination request yes no
  let result := Atom.var (PresenceConditionalSource.slot caller destination request yes no)
  let returned := PresenceConditionalSource.returned caller destination request yes no present
  let reached := PresenceConditionalSource.reached caller destination request yes no present
  have first : (machine .relational program).step
      (placed allocator world scope parents (delivered kept result request present) context origins pending) =
      some (.silent (placed allocator world scope parents returned context origins pending)) := by
    rw [placed_ordinary_step .relational program allocator world scope parents
      (delivered kept result request present) context origins pending _ _ rfl rfl]
    simp only [placed, delivered, scopeStep, enterCollapse?, enterSuperpose?, EagerDFS.Destination.machine,
      show refine (comparisonBindings kept result request present) (Effects.boolean present) result = some returned.bindings from refined,
      installChild, retainChild]
    rfl
  have second : (machine .relational program).step
      (placed allocator world scope parents returned context origins pending) =
      some (.silent (placed allocator world scope parents reached context origins pending)) := by
    rw [placed_ordinary_step .relational program allocator world scope parents returned context origins pending
      (.branch result yes no destination) caller.goals rfl rfl]
    have selected := PresenceConditionalSource.branch_step program allocator world scope parents returned context origins pending
      result yes no destination caller.goals environment rfl resolved
    change read environment result = Effects.boolean present at value
    rw [value] at selected
    cases present <;> exact congrArg some selected
  rw [Machine.run_succ_silent _ first, Machine.run_succ_silent _ second]
  rfl

/-- The condition is evaluated once before selecting either arbitrary source
body. The copy boundary and all older work remain in the resulting cursor. -/
theorem conditional_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom)
    (request : Request) (yes no : Atom) (consistent : ∃ environment, Solves environment caller.bindings)
    (rows : List Atom) (snapshot : world.state.read request.handle = some rows)
    (closed : ClosedQueryAdmission.rowsReady request.pattern rows = true) :
    let present := decide (request.pattern ∈ rows)
    let kept := PresenceConditionalSource.waiting caller destination request yes no
    let result := Atom.var (PresenceConditionalSource.slot caller destination request yes no)
    (machine .relational program).run (1 + (childBudget present + 10) + 2)
      (placed allocator world scope parents (PresenceConditionalSource.entry caller destination request yes no) context origins pending) =
      ([], match copyAllocator allocator present with
        | some next => .exhausted (placed next world scope parents
            (PresenceConditionalSource.reached caller destination request yes no present) context (origins ++ [0, 0]) pending)
        | none => .suspended .allocation
            (collectionEnd allocator world scope parents kept context origins pending result request present)) := by
  dsimp only
  have firstStep : (machine .relational program).step
      (placed allocator world scope parents (PresenceConditionalSource.entry caller destination request yes no) context origins pending) =
      some (.silent (placed allocator world scope parents
        (start (PresenceConditionalSource.waiting caller destination request yes no)
          (.var (PresenceConditionalSource.slot caller destination request yes no)) request) context origins pending)) := by
    rw [placed_ordinary_step .relational program allocator world scope parents
      (PresenceConditionalSource.entry caller destination request yes no) context origins pending _ _ rfl rfl]
    exact congrArg some (PresenceConditionalSource.entry_step program allocator world scope parents caller context origins pending
      destination request yes no)
  have firstRun : (machine .relational program).run 1
      (placed allocator world scope parents (PresenceConditionalSource.entry caller destination request yes no) context origins pending) =
      ([], .exhausted (placed allocator world scope parents
        (start (PresenceConditionalSource.waiting caller destination request yes no)
          (.var (PresenceConditionalSource.slot caller destination request yes no)) request) context origins pending)) := by
    rw [Machine.run_succ_silent _ firstStep]
    rfl
  have queried := guard_prefix program allocator world scope parents
    (PresenceConditionalSource.waiting caller destination request yes no) context origins pending
    (PresenceConditionalSource.slot caller destination request yes no) request consistent rows snapshot closed
    (PresenceConditionalSource.slot_fresh caller destination request yes no _)
  dsimp only at queried
  have first := (machine .relational program).established_and_pending 1
    (childBudget (decide (request.pattern ∈ rows)) + 10) _ _ [] firstRun
  rw [queried] at first
  simp only [List.nil_append] at first
  cases copied : copyAllocator allocator (decide (request.pattern ∈ rows)) with
  | none =>
      rw [copied] at first
      have stable := (machine .relational program).run_stable _ 2 _ (fun residual => by rw [first]; simp)
      rw [first] at stable
      exact stable
  | some next =>
      rw [copied] at first
      have last := (machine .relational program).established_and_pending _ 2 _ _ [] first
      rw [conditional_select program next world scope parents caller context (origins ++ [0, 0]) pending
        destination request yes no _ consistent] at last
      exact last

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource.Guards
