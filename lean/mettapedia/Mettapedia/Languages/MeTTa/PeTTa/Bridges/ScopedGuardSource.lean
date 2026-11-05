import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryContinuation
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceConditionalSource

/-!
# Presence-guard steps in the captured-query source profile

Ordinary control steps share the existing source machine. Primitive result
slots require an actual freshness proof; pure query absence additionally
requires a complete admitted current-domain read.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource.Guards

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open ClosedOnceQueryFrame (placed FreshFor)

def ordinaryGoal : Goal → Bool
  | .invoke .. => false
  | .evaluate (.expression (.symbol "let*" :: _)) _ => false
  | _ => true

theorem ordinary_step {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (goal : Goal) (older : List Goal)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atGoal : control.goals = goal :: older) (ordinary : ordinaryGoal goal = true) :
    (machine policy program).step (allocator, ⟨world, scope :: parents⟩) =
      some (scopeStep policy program (allocator, ⟨world, scope :: parents⟩)) := by
  have syntaxNone : syntaxStep (allocator, ⟨world, scope :: parents⟩) = none := by
    simp only [syntaxStep, frontier, atGoal]
    split
    next arguments destination rest equation =>
      cases equation
      simp [ordinaryGoal] at ordinary
    next => rfl
  have constrainedNone : constrainedCall (allocator, ⟨world, scope :: parents⟩) = none := by
    cases goal <;> simp_all [ordinaryGoal, constrainedCall]
  have mutationNone : mutationCall (allocator, ⟨world, scope :: parents⟩) = none := by
    cases goal <;> simp_all [ordinaryGoal, mutationCall]
  have queryNone : queryStep (allocator, ⟨world, scope :: parents⟩) = none := by
    cases goal <;> simp_all [ordinaryGoal, queryStep]
  simp [machine, step, syntaxNone, constrainedNone, mutationNone, queryNone]

theorem placed_ordinary_step {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (goal : Goal) (older : List Goal)
    (atGoal : control.goals = goal :: older) (ordinary : ordinaryGoal goal = true) :
    (machine policy program).step (placed allocator world scope parents control context origins pending) =
      some (scopeStep policy program (placed allocator world scope parents control context origins pending)) :=
  ordinary_step policy program allocator world _ parents control context origins pending goal older rfl atGoal ordinary

theorem empty_goals_step {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (frontier : scope.frontier = (control, context, origins) :: pending) (finished : control.goals = []) :
    (machine policy program).step (allocator, ⟨world, scope :: parents⟩) =
      some (scopeStep policy program (allocator, ⟨world, scope :: parents⟩)) := by
  simp [machine, step, syntaxStep, constrainedCall, mutationCall, queryStep, frontier, finished]

theorem empty_frontier_step {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (finished : scope.frontier = []) :
    (machine policy program).step (allocator, ⟨world, scope :: parents⟩) =
      some (scopeStep policy program (allocator, ⟨world, scope :: parents⟩)) := by
  simp [machine, step, syntaxStep, constrainedCall, mutationCall, queryStep, finished]

theorem commit_first_answer {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (younger kept : List (CollectionWork Context)) (previousBoundary : Nat)
    (environment : Environment)
    (frontier : scope.frontier = (control, context, origins) :: younger ++ kept)
    (atGoal : control.goals = [.commit, .restoreCommit previousBoundary])
    (boundary : control.cutBoundary = kept.length) (resolved : resolve control.bindings = some environment) :
    let answer : CollectedAnswer := ⟨read environment control.destination, control.bindings, origins, []⟩
    let after : ScopedCursor Context := (allocator, ⟨world, EagerDFS.Scope.record scope kept answer :: parents⟩)
    (machine policy program).run 3 (allocator, ⟨world, scope :: parents⟩) =
      (if scope.caller.isNone then [answer] else [], .exhausted after) := by
  let stopped : Control := {control with goals := [.restoreCommit previousBoundary]}
  let returned : Control := {control with goals := [], cutBoundary := previousBoundary}
  let scope₁ := {scope with frontier := (stopped, context, origins) :: kept}
  let scope₂ := {scope with frontier := (returned, context, origins) :: kept}
  have first : (machine policy program).step (allocator, ⟨world, scope :: parents⟩) =
      some (.silent (allocator, ⟨world, scope₁ :: parents⟩)) := by
    rw [ordinary_step policy program allocator world scope parents control context origins (younger ++ kept)
      .commit [.restoreCommit previousBoundary] frontier atGoal rfl]
    exact congrArg some (scope_commit_split policy program allocator world scope parents control context origins
      younger kept [.restoreCommit previousBoundary] frontier atGoal boundary)
  have second : (machine policy program).step (allocator, ⟨world, scope₁ :: parents⟩) =
      some (.silent (allocator, ⟨world, scope₂ :: parents⟩)) := by
    rw [ordinary_step policy program allocator world scope₁ parents stopped context origins kept
      (.restoreCommit previousBoundary) [] rfl rfl rfl]
    simp [scopeStep, scope₁, scope₂, stopped, returned, enterCollapse?, enterSuperpose?,
      EagerDFS.Destination.machine, installChild, retainChild]
  have last : (machine policy program).step (allocator, ⟨world, scope₂ :: parents⟩) =
      some (let answer : CollectedAnswer := ⟨read environment control.destination, control.bindings, origins, []⟩
       let after : ScopedCursor Context := (allocator, ⟨world, EagerDFS.Scope.record scope kept answer :: parents⟩)
       if scope.caller.isNone then .publish [answer] after else .silent after) := by
    rw [empty_goals_step policy program allocator world scope₂ parents returned context origins kept rfl rfl]
    simp [scopeStep, scope₂, returned, enterCollapse?, enterSuperpose?,
      EagerDFS.Destination.machine, resolved, installChild, EagerDFS.Scope.record]
  rw [Machine.run_succ_silent _ first, Machine.run_succ_silent _ second]
  cases caller : scope.caller <;> simp [Machine.run, last, caller]

/-- A single-result primitive commits its effect and refines a fresh result
slot before resuming the exact older work. No completed effect is replayed. -/
theorem fresh_primitive_prefix {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (head : String) (arguments : List Atom) (result : String) (older : List Goal)
    (environment : Environment) (state : Effects.State) (value : Atom)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke head arguments (.var result) :: older)
    (resolved : resolve control.bindings = some environment) (fresh : FreshFor result control.bindings)
    (closedValue : ∀ environment, read environment value = value)
    (known : StdLib.known head = true) (ordinary : head ≠ "parse") (notQuery : head ≠ "match")
    (mutation : head = "add-atom" ∨ head = "remove-atom" →
      mutationReady world head (arguments.map (read environment)) = true)
    (applied : StdLib.apply world.state head (arguments.map (read environment)) = .ok (state, [value])) :
    (machine policy program).run 2 (allocator, ⟨world, scope :: parents⟩) =
      ([], .exhausted (allocator, ⟨{world with state}, {scope with frontier :=
        ({control with bindings := control.bindings ++ [(value, .var result)], goals := older},
          context, origins ++ [0]) :: pending} :: parents⟩)) := by
  let returned : Control := {control with goals := .equate value (.var result) :: older}
  let nextScope : CollectionScope Context :=
    {scope with frontier := (returned, context, origins ++ [0]) :: pending}
  have invoked := Caller.primitive_step policy program allocator world scope parents control context origins pending
    head arguments (.var result) older environment state [value] result frontier atCall resolved
    (ClosedOnceQueryFrame.fresh_read _ _ _ fresh resolved) known ordinary notQuery mutation applied
  have first : (machine policy program).step (allocator, ⟨world, scope :: parents⟩) =
      some (.silent (allocator, ⟨{world with state}, nextScope :: parents⟩)) := by
    simpa [nextScope, returned, primitiveWork] using invoked
  have refined := ClosedOnceQueryFrame.refine_fresh_closed control.bindings result value fresh
    ⟨environment, resolve_sound resolved⟩ closedValue
  have second : (machine policy program).step (allocator, ⟨{world with state}, nextScope :: parents⟩) =
      some (.silent (allocator, ⟨{world with state}, {scope with frontier :=
        ({control with bindings := control.bindings ++ [(value, .var result)], goals := older},
          context, origins ++ [0]) :: pending} :: parents⟩)) := by
    rw [ordinary_step policy program allocator {world with state} nextScope parents returned context (origins ++ [0])
      pending (.equate value (.var result)) older rfl rfl rfl]
    simp [nextScope, returned, scopeStep, enterCollapse?, enterSuperpose?, EagerDFS.Destination.machine,
      refined, installChild, retainChild]
  rw [Machine.run_succ_silent _ first, Machine.run_succ_silent _ second]
  rfl

open PresenceGuardSource

set_option maxHeartbeats 1200000 in
/-- Boolean readout after the actual collection copy. Freshness is a finite
syntactic condition on the reached equations, not an assumed guard result. -/
theorem readout_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (result : String)
    (request : LiteralQuerySource.Request) (present : Bool)
    (consistent : ∃ environment, Solves environment caller.bindings)
    (freshResult : FreshFor result (comparisonBindings caller (.var result) request present)) :
    (machine .relational program).run 6
      (placed allocator world scope parents (afterCopy caller (.var result) request present) context origins pending) =
      ([], .exhausted (placed allocator world scope parents (delivered caller (.var result) request present)
        context (origins ++ [0, 0]) pending)) := by
  obtain ⟨equalEnvironment, equalResolved⟩ := resolve_complete
    (ClosedOnceQueryFrame.refined_consistent _ _ _ (empty_refined caller (.var result) request present consistent))
  obtain ⟨notEnvironment, notResolved⟩ := resolve_complete
    (ClosedOnceQueryFrame.refined_consistent _ _ _ (comparison_refined caller (.var result) request present consistent))
  have freshEqual : FreshFor (notSlot caller (.var result) request)
      (emptyBindings caller (.var result) request present) := by
    apply fresh_append_closed
    · exact fresh_append_closed _ _ _ _ (not_fresh caller (.var result) request)
        (not_ne_left caller (.var result) request) (tuple_freeVars request present)
    · exact not_ne_right caller (.var result) request
    · decide +kernel
  let s0 := placed allocator world scope parents (afterCopy caller (.var result) request present) context origins pending
  let s1 := placed allocator world scope parents (afterTuple caller (.var result) request present) context origins pending
  let s2 := placed allocator world scope parents (emptyPrepared caller (.var result) request present) context origins pending
  let s3 := placed allocator world scope parents (beforeEquality caller (.var result) request present) context origins pending
  let s4 := placed allocator world scope parents (equalityReturned caller (.var result) request present) context (origins ++ [0]) pending
  let s5 := placed allocator world scope parents (beforeNegation caller (.var result) request present) context (origins ++ [0]) pending
  let s6 := placed allocator world scope parents (delivered caller (.var result) request present) context (origins ++ [0, 0]) pending
  have step1 : (machine .relational program).step s0 = some (.silent s1) := by
    rw [placed_ordinary_step .relational program allocator world scope parents
      (afterCopy caller (.var result) request present) context origins pending _ _ rfl rfl]
    simp [s1, placed, afterCopy, afterTuple, scopeStep, enterCollapse?, enterSuperpose?,
      EagerDFS.Destination.machine, tuple_refined caller (.var result) request present consistent, installChild, retainChild]
  have step2 : (machine .relational program).step s1 = some (.silent s2) := by
    rw [placed_ordinary_step .relational program allocator world scope parents
      (afterTuple caller (.var result) request present) context origins pending _ _ rfl rfl]
    simp [s2, placed, afterTuple, emptyPrepared, suffix, scopeStep, enterCollapse?, enterSuperpose?,
      EagerDFS.Destination.machine, prepare, replace, dataGoals, freshSlots, installChild, retainChild]
  have step3 : (machine .relational program).step s2 = some (.silent s3) := by
    rw [placed_ordinary_step .relational program allocator world scope parents
      (emptyPrepared caller (.var result) request present) context origins pending _ _ rfl rfl]
    simp [s3, placed, emptyPrepared, beforeEquality, scopeStep, enterCollapse?, enterSuperpose?,
      EagerDFS.Destination.machine, empty_refined caller (.var result) request present consistent, installChild, retainChild]
  have step4 : (machine .relational program).step s3 = some (.silent s4) := by
    have actual := Caller.primitive_step .relational program allocator world
      {scope with frontier := (beforeEquality caller (.var result) request present, context, origins) :: pending}
      parents (beforeEquality caller (.var result) request present) context origins pending "=="
      [.var (leftSlot caller (.var result) request), .var (rightSlot caller (.var result) request)]
      (.var (notSlot caller (.var result) request))
      (.invoke "not" [.var (notSlot caller (.var result) request)] (.var result) :: caller.goals)
      equalEnvironment world.state [Effects.boolean (!present)] (notSlot caller (.var result) request)
      rfl rfl equalResolved (ClosedOnceQueryFrame.fresh_read _ _ _ freshEqual equalResolved)
      (by decide) (by decide) (by decide) (by simp)
      (by rw [comparison_arguments caller (.var result) request present equalEnvironment equalResolved, equality_readout])
    simpa [s3, s4, placed, beforeEquality, equalityReturned, primitiveWork] using actual
  have step5 : (machine .relational program).step s4 = some (.silent s5) := by
    rw [placed_ordinary_step .relational program allocator world scope parents
      (equalityReturned caller (.var result) request present) context (origins ++ [0]) pending _ _ rfl rfl]
    simp [s5, placed, equalityReturned, beforeNegation, scopeStep, enterCollapse?, enterSuperpose?,
      EagerDFS.Destination.machine, comparison_refined caller (.var result) request present consistent, installChild, retainChild]
  have step6 : (machine .relational program).step s5 = some (.silent s6) := by
    have actual := Caller.primitive_step .relational program allocator world
      {scope with frontier := (beforeNegation caller (.var result) request present, context, origins ++ [0]) :: pending}
      parents (beforeNegation caller (.var result) request present) context (origins ++ [0]) pending "not"
      [.var (notSlot caller (.var result) request)] (.var result) caller.goals
      notEnvironment world.state [Effects.boolean present] result rfl rfl notResolved
      (ClosedOnceQueryFrame.fresh_read _ _ _ freshResult notResolved)
      (by decide) (by decide) (by decide) (by simp)
      (by rw [negation_argument caller (.var result) request present notEnvironment notResolved, negation_readout])
    simpa [s5, s6, placed, beforeNegation, delivered, primitiveWork, List.append_assoc] using actual
  change (machine .relational program).run 6 s0 = ([], .exhausted s6)
  rw [Machine.run_succ_silent _ step1, Machine.run_succ_silent _ step2,
    Machine.run_succ_silent _ step3, Machine.run_succ_silent _ step4,
    Machine.run_succ_silent _ step5, Machine.run_succ_silent _ step6]
  rfl

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource.Guards
