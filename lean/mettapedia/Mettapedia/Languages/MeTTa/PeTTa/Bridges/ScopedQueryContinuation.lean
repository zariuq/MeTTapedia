import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource

/-!
# Captured query entry under a retained caller

Query capture commutes with attaching older source work. The equality retains
the complete occurrence list, bindings and refusal; it does not run bodies or
turn their captured values back into source code. Collection entry and return
are separate boundaries: a collection's caller is not attached to every child.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open EagerDFS (World)
open EagerDFS.Destination

namespace Caller

open EagerDFSStreaming.Scoped

theorem bodyControl_attach (suffix : List Goal) (caller : Control) (captured : Subst)
    (body destination : Atom) (older : List Goal) :
    bodyControl (ProtectedContinuation.attach suffix caller) captured body destination
        (older.map (ProtectedContinuation.shift suffix.length) ++ suffix) =
      ProtectedContinuation.attach suffix (bodyControl caller captured body destination older) := by
  simp only [bodyControl, ProtectedContinuation.attach, List.map_cons, ProtectedContinuation.shift, List.cons_append]

/-- Both successful and refused captures are preserved, not only their count. -/
theorem capture_attach (suffix : List Goal) (caller : Control)
    (pattern body destination : Atom) (older : List Goal) (offset : Nat) (rows : List Atom) :
    capture (ProtectedContinuation.attach suffix caller) pattern body destination
        (older.map (ProtectedContinuation.shift suffix.length) ++ suffix) offset rows =
      (capture caller pattern body destination older offset rows).map
        (List.map fun entry => (entry.1, ProtectedContinuation.attach suffix entry.2)) := by
  induction rows generalizing offset with
  | nil => rfl
  | cons row rows ih =>
      simp only [capture, ProtectedContinuation.attach_bindings]
      cases matched : SpaceSemantics.matchValue [] pattern row with
      | none => simpa only [matched] using ih (offset + 1)
      | some bindings =>
          by_cases ready : (resolve (extend caller.bindings bindings)).isSome = true
          · simp only [if_pos ready]
            rw [ih, bodyControl_attach]
            cases capture caller pattern body destination older (offset + 1) rows <;> simp [ready]
          · simp [ready]

theorem choices_attach {caller : Control} {pattern body destination : Atom} {older : List Goal}
    {offset : Nat} {rows : List Atom} {selected : List (Nat × Control)}
    (source : Choices caller pattern body destination older offset rows selected) (suffix : List Goal) :
    Choices (ProtectedContinuation.attach suffix caller) pattern body destination
      (older.map (ProtectedContinuation.shift suffix.length) ++ suffix) offset rows
      (selected.map fun entry => (entry.1, ProtectedContinuation.attach suffix entry.2)) := by
  apply capture_has_source
  rw [capture_attach, source.execution]
  rfl

theorem work_attach {Context : Type} (suffix : List Goal) (context : Context) (origins : List Nat)
    (selected : List (Nat × Control)) :
    work context origins (selected.map fun entry => (entry.1, ProtectedContinuation.attach suffix entry.2)) =
      (work context origins selected).map (ProtectedContinuation.attachWork suffix) := by
  simp only [work, List.map_map, Function.comp_def, ProtectedContinuation.attachWork]

/-- The actual query-entry transition commutes with attaching the caller.
No query body is executed here, and the world and allocator are unchanged. -/
theorem captured_step_attach {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (space pattern body destination : Atom) (older suffix : List Goal) (environment : Environment)
    (rows : List Atom) (selected : List (Nat × Control))
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke "match" [space, pattern, body] destination :: older)
    (resolved : resolve control.bindings = some environment)
    (unfused : fused (read environment pattern) body = false)
    (snapshot : (Effects.readHandle (read environment space) >>= world.state.read) = some rows)
    (ready : ClosedQueryAdmission.rowsReady (read environment pattern) rows = true)
    (captured : Choices control (read environment pattern) body destination older 0 rows selected) :
    (machine policy program).step (ProtectedContinuation.attachState suffix (allocator, ⟨world, scope :: parents⟩)) =
      some (.silent (ProtectedContinuation.attachState suffix (allocator, ⟨world,
        {scope with frontier := work context origins selected ++ pending} :: parents⟩))) := by
  have attached := captured_step policy program allocator world (ProtectedContinuation.attachScope suffix scope) parents
    (ProtectedContinuation.attach suffix control) context origins (pending.map (ProtectedContinuation.attachWork suffix))
    space pattern body destination (older.map (ProtectedContinuation.shift suffix.length) ++ suffix) environment rows
    (selected.map fun entry => (entry.1, ProtectedContinuation.attach suffix entry.2))
    (by simp only [ProtectedContinuation.attachScope, frontier, List.map_cons, ProtectedContinuation.attachWork])
    (by simp only [ProtectedContinuation.attach, atCall, List.map_cons, ProtectedContinuation.shift, List.cons_append])
    resolved unfused snapshot ready (choices_attach captured suffix)
  simpa only [ProtectedContinuation.attachState, ProtectedContinuation.attachScope, List.map_append, work_attach] using attached

/-- A captured binding constrains every model of the reached frame. -/
theorem captured_read (inherited : Equations) (captured : Subst) (environment : Environment)
    (solved : Solves environment (extend inherited captured)) (name : String) (value : Atom)
    (member : (name, value) ∈ captured) :
    read environment (.var name) = read environment value := by
  exact solved (.var name, value)
    (List.mem_append_right _ (List.mem_map.mpr ⟨(name, value), member, rfl⟩))

theorem inherited_models (inherited : Equations) (captured : Subst) (environment : Environment)
    (solved : Solves environment (extend inherited captured)) : Solves environment inherited := by
  intro pair member
  exact solved pair (List.mem_append_left _ member)

theorem captured_literal_read (inherited : Equations) (captured : Subst) (environment : Environment)
    (solved : Solves environment (extend inherited captured)) (name : String) (value : Atom)
    (member : (name, value) ∈ captured) (literal : SpaceSemantics.Literal value) :
    read environment (.var name) = value := by
  rw [captured_read inherited captured environment solved name value member,
    LiteralQuerySource.read_literal value literal environment]

/-- Captured alternatives inherit the caller's protection of saved names. -/
theorem choices_protected {caller : Control} {pattern body destination : Atom} {older : List Goal}
    {offset : Nat} {rows : List Atom} {selected : List (Nat × Control)}
    (source : Choices caller pattern body destination older offset rows selected)
    (suffix : List Goal) (protectedNames : ProtectedContinuation.names suffix ⊆ caller.reserved)
    (entry : Nat × Control) (member : entry ∈ selected) :
    ProtectedContinuation.names suffix ⊆ entry.2.reserved := by
  rw [(source.frames entry member).2.2.2.2.1]
  exact protectedNames

theorem primitiveWork_attach {Context : Type} (suffix : List Goal) (control : Control)
    (context : Context) (origins : List Nat) (destination : Atom) (older : List Goal)
    (values : List Atom) :
    primitiveWork (ProtectedContinuation.attach suffix control) context origins destination
        (older.map (ProtectedContinuation.shift suffix.length) ++ suffix) values =
      (primitiveWork control context origins destination older values).map
        (ProtectedContinuation.attachWork suffix) := by
  simp only [primitiveWork, List.map_map, Function.comp_def,
    ProtectedContinuation.attachWork, ProtectedContinuation.attach, List.map_cons,
    ProtectedContinuation.shift, List.cons_append]

/-- An admitted primitive runs once with the reached operands. Its result is
installed as a value, while the authored continuation and all alternatives remain. -/
theorem primitive_step {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (environment : Environment) (state : Effects.State) (values : List Atom) (resultName : String)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke head arguments destination :: older)
    (resolved : resolve control.bindings = some environment)
    (unbound : read environment destination = .var resultName)
    (known : StdLib.known head = true) (ordinary : head ≠ "parse") (notQuery : head ≠ "match")
    (mutation : head = "add-atom" ∨ head = "remove-atom" →
      mutationReady world head (arguments.map (read environment)) = true)
    (applied : StdLib.apply world.state head (arguments.map (read environment)) = .ok (state, values)) :
    (machine policy program).step (allocator, ⟨world, scope :: parents⟩) =
      some (.silent (allocator, ⟨{world with state},
        {scope with frontier := primitiveWork control context origins destination older values ++ pending} :: parents⟩)) := by
  have unchanged : mutationCall (allocator, ⟨world, scope :: parents⟩) = none := by
    by_cases effect : head = "add-atom" ∨ head = "remove-atom"
    · simp [mutationCall, frontier, atCall, effect, resolved, mutation effect]
    · simp [mutationCall, frontier, atCall, effect]
  have noQuery : queryStep (allocator, ⟨world, scope :: parents⟩) = none := by
    simp [queryStep, frontier, atCall, notQuery]
  have ordinarySyntax : syntaxStep (allocator, ⟨world, scope :: parents⟩) = none := by
    simp [syntaxStep, frontier, atCall]
  have unconstrained : constrainedCall (allocator, ⟨world, scope :: parents⟩) = none := by
    simp [constrainedCall, frontier, atCall, notQuery, resolved, unbound]
  simp only [machine, step, ordinarySyntax, unconstrained, unchanged, noQuery]
  exact congrArg some (scope_primitive_success policy program allocator world scope parents control context
    origins pending head arguments destination older environment state values frontier atCall resolved known ordinary applied)

theorem primitive_step_attach {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (head : String) (arguments : List Atom) (destination : Atom) (older suffix : List Goal)
    (environment : Environment) (state : Effects.State) (values : List Atom) (resultName : String)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke head arguments destination :: older)
    (resolved : resolve control.bindings = some environment)
    (unbound : read environment destination = .var resultName)
    (known : StdLib.known head = true) (ordinary : head ≠ "parse") (notQuery : head ≠ "match")
    (mutation : head = "add-atom" ∨ head = "remove-atom" →
      mutationReady world head (arguments.map (read environment)) = true)
    (applied : StdLib.apply world.state head (arguments.map (read environment)) = .ok (state, values)) :
    (machine policy program).step
        (ProtectedContinuation.attachState suffix (allocator, ⟨world, scope :: parents⟩)) =
      some (.silent (ProtectedContinuation.attachState suffix (allocator, ⟨{world with state},
        {scope with frontier := primitiveWork control context origins destination older values ++ pending} :: parents⟩))) := by
  have attached := primitive_step policy program allocator world
    (ProtectedContinuation.attachScope suffix scope) parents
    (ProtectedContinuation.attach suffix control) context origins
    (pending.map (ProtectedContinuation.attachWork suffix)) head arguments destination
    (older.map (ProtectedContinuation.shift suffix.length) ++ suffix) environment state values resultName
    (by simp only [ProtectedContinuation.attachScope, frontier, List.map_cons, ProtectedContinuation.attachWork])
    (by simp only [ProtectedContinuation.attach, atCall, List.map_cons, ProtectedContinuation.shift, List.cons_append])
    resolved unbound known ordinary notQuery mutation applied
  simpa only [ProtectedContinuation.attachState, ProtectedContinuation.attachScope,
    List.map_append, primitiveWork_attach] using attached

/-- A literal guard with a complete admitted domain uses the inherited pure
query step even when its written operands obtain their values from captures. -/
theorem literal_query_step {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (space pattern destination : Atom) (older : List Goal) (environment : Environment)
    (request : LiteralQuerySource.Request) (rows : List Atom)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke "match" [space, pattern, request.payload] destination :: older)
    (resolved : resolve control.bindings = some environment)
    (location : read environment space = Effects.handleValue request.handle)
    (reading : read environment pattern = request.pattern)
    (snapshot : world.state.read request.handle = some rows)
    (ready : ClosedQueryAdmission.rowsReady request.pattern rows = true) :
    (machine policy program).step (allocator, ⟨world, scope :: parents⟩) =
      some (scopeStep policy program (allocator, ⟨world, scope :: parents⟩)) := by
  have literal := (LiteralQuerySource.checkLiteral_iff request.pattern).mpr request.literal
  have scalar := (ConstantQuerySource.isScalar_iff request.payload).mpr request.scalar
  simp [machine, step, syntaxStep, constrainedCall, mutationCall, queryStep,
    frontier, atCall, resolved, location, reading, Effects.readHandle_handleValue,
    snapshot, ready, fused, literal, scalar]

/-- Absence drops this query branch only after a complete current-domain
inspection. Previously captured alternatives, the caller world and allocator
survive unchanged. This is one source step, not an evaluation of later work. -/
theorem literal_absence_step {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (space pattern destination : Atom) (older : List Goal) (environment : Environment)
    (request : LiteralQuerySource.Request) (rows : List Atom)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke "match" [space, pattern, request.payload] destination :: older)
    (resolved : resolve control.bindings = some environment)
    (location : read environment space = Effects.handleValue request.handle)
    (reading : read environment pattern = request.pattern)
    (snapshot : world.state.read request.handle = some rows)
    (ready : ClosedQueryAdmission.rowsReady request.pattern rows = true)
    (absent : request.pattern ∉ rows) :
    (machine policy program).step (allocator, ⟨world, scope :: parents⟩) =
      some (.silent (allocator, ⟨world, {scope with frontier := pending} :: parents⟩)) := by
  rw [literal_query_step policy program allocator world scope parents control context origins pending
    space pattern destination older environment request rows frontier atCall resolved location reading snapshot ready]
  have missed := FirstQueryCursor.complete [] request.pattern 0 rows
  rw [(LiteralQuerySource.reference_absent request rows).mpr absent] at missed
  exact congrArg some (ConstantQuerySource.empty_query_keeps_outer_work policy program allocator world scope parents
    control context origins pending [space, pattern, request.payload] destination request.pattern request.payload
    older request.handle rows (rows.length + 1) environment frontier atCall resolved
    (by simp [location, reading, LiteralQuerySource.read_payload]) snapshot missed)

end Caller
end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource
