import Mettapedia.Languages.MeTTa.PeTTa.Bridges.LiteralQuerySource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedCaseSource

/-!
# Captured, effectful query bodies in retained source frames

The query captures its ordered row choices before a body runs. Each choice
extends the reached logical frame and schedules the original body as code;
it does not substitute a computed value into a new source expression. Later
bodies run through the same shared-world scheduler.

This explicit profile extends the raw-template component. Literal queries
with scalar bodies keep that component's fused rule. Unsupported open stored
rows or inconsistent captured frames request reference service at the same
invocation, with its world and continuation intact. Native source-loading,
open-fact freshening and host servicing of those requests remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination

def extend (inherited : Equations) (captured : Subst) : Equations :=
  inherited ++ captured.map (fun binding => (.var binding.1, binding.2))

def bodyControl (caller : Control) (captured : Subst) (body destination : Atom) (older : List Goal) : Control :=
  {caller with bindings := extend caller.bindings captured, goals := .evaluate body destination :: older}

def capture (caller : Control) (pattern body destination : Atom) (older : List Goal) :
    Nat → List Atom → Option (List (Nat × Control))
  | _, [] => some []
  | offset, row :: rows =>
      match SpaceSemantics.matchValue [] pattern row with
      | none => capture caller pattern body destination older (offset + 1) rows
      | some bindings =>
          if (resolve (extend caller.bindings bindings)).isSome then
            (capture caller pattern body destination older (offset + 1) rows).map
              ((offset, bodyControl caller bindings body destination older) :: ·)
          else none

/-- Independent ordered query choices: matching uses the source judgment,
and a body enters only a satisfiable extension of the incoming frame. -/
inductive Choices (caller : Control) (pattern body destination : Atom) (older : List Goal) :
    Nat → List Atom → List (Nat × Control) → Prop where
  | nil (offset : Nat) : Choices caller pattern body destination older offset [] []
  | miss (offset : Nat) (row : Atom) (rows : List Atom) (rest : List (Nat × Control))
      (unmatched : ∀ bindings, ¬SpaceSemantics.ValueMatch [] pattern row bindings)
      (tail : Choices caller pattern body destination older (offset + 1) rows rest) :
      Choices caller pattern body destination older offset (row :: rows) rest
  | hit (offset : Nat) (row : Atom) (rows : List Atom) (bindings : Subst) (rest : List (Nat × Control))
      (matched : SpaceSemantics.ValueMatch [] pattern row bindings)
      (consistent : ∃ environment, Solves environment (extend caller.bindings bindings))
      (tail : Choices caller pattern body destination older (offset + 1) rows rest) :
      Choices caller pattern body destination older offset (row :: rows)
        ((offset, bodyControl caller bindings body destination older) :: rest)

theorem resolve_present (bindings : Equations) :
    (resolve bindings).isSome = true ↔ ∃ environment, Solves environment bindings := by
  constructor
  · intro present
    cases found : resolve bindings with
    | none => simp [found] at present
    | some environment => exact ⟨environment, resolve_sound found⟩
  · intro consistent
    obtain ⟨environment, found⟩ := resolve_complete consistent
    simp [found]

theorem Choices.execution {caller : Control} {pattern body destination : Atom} {older : List Goal}
    {offset : Nat} {rows : List Atom} {selected : List (Nat × Control)}
    (source : Choices caller pattern body destination older offset rows selected) :
    capture caller pattern body destination older offset rows = some selected := by
  induction source with
  | nil => rfl
  | miss offset row rows rest unmatched tail ih =>
      have missing : SpaceSemantics.matchValue [] pattern row = none := by
        cases matched : SpaceSemantics.matchValue [] pattern row with
        | none => rfl
        | some bindings => exact (unmatched bindings (SpaceSemantics.matchValue_sound matched)).elim
      simp [capture, missing, ih]
  | hit offset row rows bindings rest matched consistent tail ih =>
      simp [capture, SpaceSemantics.matchValue_complete matched, (resolve_present _).mpr consistent, ih]

theorem capture_has_source (caller : Control) (pattern body destination : Atom) (older : List Goal)
    (offset : Nat) (rows : List Atom) (selected : List (Nat × Control))
    (completed : capture caller pattern body destination older offset rows = some selected) :
    Choices caller pattern body destination older offset rows selected := by
  induction rows generalizing offset selected with
  | nil => cases Option.some.inj completed; exact .nil offset
  | cons row rows ih =>
      simp only [capture] at completed
      cases matched : SpaceSemantics.matchValue [] pattern row with
      | none =>
          simp only [matched] at completed
          exact .miss offset row rows selected (fun bindings source => by
            have found := SpaceSemantics.matchValue_complete source
            rw [matched] at found
            cases found) (ih (offset + 1) selected completed)
      | some bindings =>
          simp only [matched] at completed
          split at completed
          next ready =>
            obtain ⟨rest, later, rfl⟩ := Option.map_eq_some_iff.mp completed
            exact .hit offset row rows bindings rest (SpaceSemantics.matchValue_sound matched)
              ((resolve_present _).mp ready) (ih (offset + 1) rest later)
          next => cases completed

theorem capture_exact (caller : Control) (pattern body destination : Atom) (older : List Goal)
    (offset : Nat) (rows : List Atom) (selected : List (Nat × Control)) :
    capture caller pattern body destination older offset rows = some selected ↔
      Choices caller pattern body destination older offset rows selected :=
  ⟨capture_has_source caller pattern body destination older offset rows selected, Choices.execution⟩

/-- Successful preparation covers the complete authored scan. It cannot
drop a matched row merely because installing that row's frame was difficult. -/
theorem Choices.scan {caller : Control} {pattern body destination : Atom} {older : List Goal}
    {offset : Nat} {rows : List Atom} {selected : List (Nat × Control)}
    (source : Choices caller pattern body destination older offset rows selected) :
    selected = (FlatQueryRelationCompilation.sourceScan [] pattern offset rows).map
      (fun entry => (entry.1, bodyControl caller entry.2 body destination older)) := by
  induction source with
  | nil => rfl
  | miss offset row rows rest unmatched tail ih =>
      have missing : SpaceSemantics.matchValue [] pattern row = none := by
        cases matched : SpaceSemantics.matchValue [] pattern row with
        | none => rfl
        | some bindings => exact (unmatched bindings (SpaceSemantics.matchValue_sound matched)).elim
      simpa [FlatQueryRelationCompilation.sourceScan, missing] using ih
  | hit offset row rows bindings rest matched consistent tail ih =>
      simp [FlatQueryRelationCompilation.sourceScan, SpaceSemantics.matchValue_complete matched, ih]

theorem capture_occurrence_count (caller : Control) (pattern body destination : Atom) (older : List Goal)
    (offset : Nat) (rows : List Atom) (selected : List (Nat × Control))
    (completed : capture caller pattern body destination older offset rows = some selected) :
    selected.length = (FlatQueryRelationCompilation.sourceScan [] pattern offset rows).length := by
  rw [(capture_has_source caller pattern body destination older offset rows selected completed).scan, List.length_map]

/-- Complete row-wise source matching and solvable frame extensions construct
the captured frontier. No successful capture or body result is assumed. -/
theorem capture_of_consistent_matches (caller : Control) (pattern body destination : Atom)
    (older : List Goal) (offset : Nat) (rows : List Atom)
    (consistent : ∀ row ∈ rows, ∀ bindings, SpaceSemantics.ValueMatch [] pattern row bindings →
      ∃ environment, Solves environment (extend caller.bindings bindings)) :
    capture caller pattern body destination older offset rows =
      some ((FlatQueryRelationCompilation.sourceScan [] pattern offset rows).map
        (fun entry => (entry.1, bodyControl caller entry.2 body destination older))) := by
  induction rows generalizing offset with
  | nil => rfl
  | cons row rows ih =>
      have tail := ih (offset + 1) (fun value member => consistent value (List.mem_cons_of_mem _ member))
      cases matched : SpaceSemantics.matchValue [] pattern row with
      | none => simpa [capture, FlatQueryRelationCompilation.sourceScan, matched] using tail
      | some bindings =>
          have ready := (resolve_present _).mpr
            (consistent row List.mem_cons_self bindings (SpaceSemantics.matchValue_sound matched))
          simp [capture, FlatQueryRelationCompilation.sourceScan, matched, ready, tail]

/-- Every selected occurrence retains its incoming constraints and original
body syntax. Equal-valued rows remain separate positions. -/
theorem Choices.frames {caller : Control} {pattern body destination : Atom} {older : List Goal}
    {offset : Nat} {rows : List Atom} {selected : List (Nat × Control)}
    (source : Choices caller pattern body destination older offset rows selected)
    (entry : Nat × Control) (member : entry ∈ selected) :
    offset ≤ entry.1 ∧ entry.1 < offset + rows.length ∧
      entry.2.goals = .evaluate body destination :: older ∧
      entry.2.destination = caller.destination ∧ entry.2.reserved = caller.reserved ∧
      entry.2.cutBoundary = caller.cutBoundary ∧
      (∃ suffix, entry.2.bindings = caller.bindings ++ suffix) ∧
      (∃ environment, Solves environment entry.2.bindings) := by
  induction source with
  | nil => cases member
  | miss offset row rows rest unmatched tail ih =>
      obtain ⟨lower, upper, properties⟩ := ih member
      exact ⟨by omega, by simp only [List.length_cons]; omega, properties⟩
  | hit offset row rows bindings rest matched consistent tail ih =>
      rcases List.mem_cons.mp member with same | later
      · subst entry
        exact ⟨by omega, by simp, rfl, rfl, rfl, rfl, ⟨_, rfl⟩, consistent⟩
      · obtain ⟨lower, upper, properties⟩ := ih later
        exact ⟨by omega, by simp only [List.length_cons]; omega, properties⟩

def work {Context : Type} (context : Context) (origins : List Nat)
    (selected : List (Nat × Control)) : List (CollectionWork Context) :=
  selected.map fun entry => (entry.2, context, origins ++ [entry.1])

def fused (pattern body : Atom) : Bool :=
  LiteralQuerySource.checkLiteral pattern && ConstantQuerySource.isScalar body

abbrev Action (Context : Type) :=
  Transition (ScopedCursor Context) CollectedAnswer (ScopedCursor Context) ScopeBoundary

/-- The source's sequential binding form uses the existing checked syntax
expansion. Malformed forms retain reference service, rather than evaluating
their apparent children as an ordinary data constructor. -/
def syntaxStep {Context : Type} (source : ScopedCursor Context) : Option (Action Context) := do
  let scope :: parents := source.2.scopes | none
  let (control, context, origins) :: pending := scope.frontier | none
  let .evaluate (.expression (.symbol "let*" :: arguments)) destination :: older := control.goals | none
  let fallback : Action Context := .call (.branch (.invoke "let*" arguments destination)) source
  match arguments with
  | [.expression pairs, body] =>
      match Eval.nestedLets pairs body with
      | none => some fallback
      | some nested => some (.silent (source.1, ⟨source.2.world,
          {scope with frontier := ({control with goals := .evaluate nested destination :: older},
            context, origins) :: pending} :: parents⟩))
  | _ => some fallback

/-- The eager primitive component does not implement every source predicate's
output-head protocol. A constrained result therefore retains reference entry
before invoking it. Queries can still capture their pure row choices; any
subsequent constrained body call is checked at its own boundary. -/
def constrainedCall {Context : Type} (source : ScopedCursor Context) : Option (Action Context) := do
  let scope :: _ := source.2.scopes | none
  let (control, _, _) :: _ := scope.frontier | none
  let .invoke head arguments destination :: _ := control.goals | none
  if head = "match" then none else do
    let environment ← resolve control.bindings
    match read environment destination with
    | .var _ => none
    | _ => some (.call (.branch (.invoke head arguments destination)) source)

def mutationPayload (removal : Bool) (payload : Atom) : Bool :=
  Mettapedia.Languages.ProcessCalculi.MORK.isGroundAtom payload &&
    match payload with
    | .expression (.symbol head :: _) => head != "=" && head != ":"
    | .expression (_ :: _) => true
    | _ => !removal

/-- Only ordinary ground fact mutations use the inherited primitive model.
Code/declaration edits, variable freshening and primitive-row removal retain
their reference service. Removal additionally checks its complete candidate
domain, not merely the rows which an earlier query happened to inspect. -/
def mutationReady (world : World) (head : String) (arguments : List Atom) : Bool :=
  match arguments with
  | [space, payload] =>
      match Effects.readHandle space >>= world.state.read with
      | none => false
      | some rows => mutationPayload (head == "remove-atom") payload &&
          (head != "remove-atom" || ClosedQueryAdmission.rowsReady payload rows)
  | _ => false

def mutationCall {Context : Type} (source : ScopedCursor Context) : Option (Action Context) := do
  let scope :: _ := source.2.scopes | none
  let (control, _, _) :: _ := scope.frontier | none
  let .invoke head arguments destination :: _ := control.goals | none
  if head = "add-atom" ∨ head = "remove-atom" then do
    let environment ← resolve control.bindings
    if mutationReady source.2.world head (arguments.map (read environment)) then none
    else some (.call (.branch (.invoke head arguments destination)) source)
  else none

/-- Only a ready query invocation is intercepted. A reference request keeps
its original operands and complete cursor, including effects of evaluating
the space operand. It must not restart that operand. -/
def queryStep {Context : Type} (source : ScopedCursor Context) : Option (Action Context) := do
  let scope :: parents := source.2.scopes | none
  let (control, context, origins) :: pending := scope.frontier | none
  let .invoke "match" [space, pattern, body] destination :: older := control.goals | none
  let environment ← resolve control.bindings
  let resolvedPattern := read environment pattern
  let fallback : Action Context := .call (.branch (.invoke "match" [space, pattern, body] destination)) source
  match Effects.readHandle (read environment space) >>= source.2.world.state.read with
  | none => some (.call (.fault .invalidSpace) source)
  | some rows =>
      if ClosedQueryAdmission.rowsReady resolvedPattern rows then
        if fused resolvedPattern body then none else
          match capture control resolvedPattern body destination older 0 rows with
          | none => some fallback
          | some selected => some (.silent (source.1, ⟨source.2.world,
              {scope with frontier := work context origins selected ++ pending} :: parents⟩))
      else some fallback

def step {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) : Action Context :=
  match syntaxStep source with
  | some action => action
  | none => match constrainedCall source with
    | some action => action
    | none => match mutationCall source with
      | some action => action
      | none => match queryStep source with
        | some action => action
        | none => scopeStep policy program source

def machine {Context : Type} (policy : Policy) (program : SpaceSemantics.Program) :
    Machine (ScopedCursor Context) CollectedAnswer (ScopedCursor Context) ScopeBoundary where
  step source := some (step policy program source)

theorem untouched_step {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) (ordinarySyntax : syntaxStep source = none)
    (unconstrained : constrainedCall source = none)
    (ordinaryMutation : mutationCall source = none)
    (ordinary : queryStep source = none) :
    (machine policy program).step source =
      (EagerDFSStreaming.machine program (.scopedDestination Context policy)).step source := by
  simp [machine, step, ordinarySyntax, unconstrained, ordinaryMutation, ordinary, EagerDFSStreaming.Scoped.step_scope]

theorem sequence_entry {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (pairs : List Atom) (body nested destination : Atom) (older : List Goal)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atGoal : control.goals = .evaluate (.expression [.symbol "let*", .expression pairs, body]) destination :: older)
    (expanded : Eval.nestedLets pairs body = some nested) :
    (machine policy program).step (allocator, ⟨world, scope :: parents⟩) =
      some (.silent (allocator, ⟨world,
        {scope with frontier := ({control with goals := .evaluate nested destination :: older},
          context, origins) :: pending} :: parents⟩)) := by
  simp [machine, step, syntaxStep, frontier, atGoal, expanded]

theorem captured_step {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (space pattern body destination : Atom) (older : List Goal) (environment : Environment)
    (rows : List Atom) (selected : List (Nat × Control))
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke "match" [space, pattern, body] destination :: older)
    (resolved : resolve control.bindings = some environment)
    (unfused : fused (read environment pattern) body = false)
    (snapshot : (Effects.readHandle (read environment space) >>= world.state.read) = some rows)
    (ready : ClosedQueryAdmission.rowsReady (read environment pattern) rows = true)
    (captured : Choices control (read environment pattern) body destination older 0 rows selected) :
    (machine policy program).step (allocator, ⟨world, scope :: parents⟩) =
      some (.silent (allocator, ⟨world,
        {scope with frontier := work context origins selected ++ pending} :: parents⟩)) := by
  obtain ⟨handle, location, reading⟩ := Option.bind_eq_some_iff.mp snapshot
  simp [machine, step, syntaxStep, constrainedCall, mutationCall, queryStep, frontier, atCall, resolved, unfused, location, reading, ready, captured.execution]

theorem unsupported_rows_retain_invocation {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (space pattern body destination : Atom) (older : List Goal) (environment : Environment) (rows : List Atom)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke "match" [space, pattern, body] destination :: older)
    (resolved : resolve control.bindings = some environment)
    (snapshot : (Effects.readHandle (read environment space) >>= world.state.read) = some rows)
    (unsupported : ClosedQueryAdmission.rowsReady (read environment pattern) rows = false) :
    (machine policy program).step (allocator, ⟨world, scope :: parents⟩) =
      some (.call (.branch (.invoke "match" [space, pattern, body] destination))
        (allocator, ⟨world, scope :: parents⟩)) := by
  obtain ⟨handle, location, reading⟩ := Option.bind_eq_some_iff.mp snapshot
  simp [machine, step, syntaxStep, constrainedCall, mutationCall, queryStep, frontier, atCall, resolved, location, reading, unsupported]

theorem inconsistent_capture_retains_invocation {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (space pattern body destination : Atom) (older : List Goal) (environment : Environment) (rows : List Atom)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke "match" [space, pattern, body] destination :: older)
    (resolved : resolve control.bindings = some environment)
    (unfused : fused (read environment pattern) body = false)
    (snapshot : (Effects.readHandle (read environment space) >>= world.state.read) = some rows)
    (ready : ClosedQueryAdmission.rowsReady (read environment pattern) rows = true)
    (incompatible : capture control (read environment pattern) body destination older 0 rows = none) :
    (machine policy program).step (allocator, ⟨world, scope :: parents⟩) =
      some (.call (.branch (.invoke "match" [space, pattern, body] destination))
        (allocator, ⟨world, scope :: parents⟩)) := by
  obtain ⟨handle, location, reading⟩ := Option.bind_eq_some_iff.mp snapshot
  simp [machine, step, syntaxStep, constrainedCall, mutationCall, queryStep, frontier, atCall, resolved, unfused, location, reading, ready, incompatible]

theorem unsupported_mutation_retains_reference_entry {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal) (environment : Environment)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke head arguments destination :: older)
    (effect : head = "add-atom" ∨ head = "remove-atom")
    (resolved : resolve control.bindings = some environment)
    (unconstrained : constrainedCall (allocator, ⟨world, scope :: parents⟩) = none)
    (unsupported : mutationReady world head (arguments.map (read environment)) = false) :
    (machine policy program).step (allocator, ⟨world, scope :: parents⟩) =
      some (.call (.branch (.invoke head arguments destination)) (allocator, ⟨world, scope :: parents⟩)) := by
  simp only [machine, step, syntaxStep, frontier, atCall, unconstrained]
  simp [mutationCall, frontier, atCall, effect, resolved, unsupported]

theorem constrained_result_retains_reference_entry {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal) (environment : Environment)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke head arguments destination :: older)
    (notQuery : head ≠ "match") (resolved : resolve control.bindings = some environment)
    (constrained : ∀ name, read environment destination ≠ .var name) :
    (machine policy program).step (allocator, ⟨world, scope :: parents⟩) =
      some (.call (.branch (.invoke head arguments destination)) (allocator, ⟨world, scope :: parents⟩)) := by
  simp only [machine, step, syntaxStep, constrainedCall, frontier, atCall, if_neg notQuery, resolved]
  cases value : read environment destination <;> simp_all

/-- Capturing a query schedules its bodies; it never recursively runs them
inside one transition. Every later body step remains subject to the driver. -/
theorem split_resume {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (first second : Nat) (source saved : ScopedCursor Context) (events : List CollectedAnswer)
    (paused : (machine policy program).run first source = (events, .exhausted saved)) :
    (machine policy program).run (first + second) source =
      (events ++ ((machine policy program).run second saved).1, ((machine policy program).run second saved).2) :=
  (machine policy program).established_and_pending first second source saved events paused

/-! ## Owned finite two-way extension

The earlier completed profile is retained verbatim. This entrance fills only
an explicit canonical-query request, after checking the structural carrier.
It shares the same syntax, producer, world and continuation owners.
-/

/-- Pattern views requiring a separate native codec do not become ordinary
first-order constructors. Stored variables themselves are supported. -/
def plainQueryPattern : Atom → Bool
  | .expression children =>
      !LiteralQuerySource.consView children &&
        (match children with | .symbol "quote" :: _ => false | _ => true) &&
        children.attach.all (fun child => plainQueryPattern child.1)
  | atom => finiteStructural atom
termination_by atom => sizeOf atom
decreasing_by
  simp_wf
  exact Nat.lt_trans (List.sizeOf_lt_of_mem child.property) (by omega)

def unifyingReady (pattern : Atom) (rows : List Atom) : Bool :=
  plainQueryPattern pattern &&
    (match pattern with
      | .expression (.symbol "," :: _) | .expression (.symbol "|" :: _) => false
      | _ => true) && rows.all finiteStructural

/-- Ownership is checked at the actual call stage. The retained control
distinguishes source evaluation from ready invocation; argument production
is not replayed when the ready boundary needs canonical service. -/
def ownershipStep {Context : Type} (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) : Option (Action Context) := do
  if queryOwned program then none else do
    let scope :: _ := source.2.scopes | none
    let (control, _, _) :: _ := scope.frontier | none
    match control.goals with
    | .evaluate (.expression [.symbol "match", space, pattern, body]) destination :: _
    | .invoke "match" [space, pattern, body] destination :: _ =>
        some (.call (.branch (.invoke "match" [space, pattern, body] destination)) source)
    | _ => none

/-- An admitted request enters the existing query continuation. Its pattern
and template remain recipes in the reached record, not substituted source. -/
def unifyingQueryStep {Context : Type} (source : ScopedCursor Context) : Option (Action Context) := do
  let scope :: parents := source.2.scopes | none
  let (control, context, origins) :: pending := scope.frontier | none
  let .invoke "match" [space, pattern, body] destination :: older := control.goals | none
  let environment ← resolve control.bindings
  let rows ← Effects.readHandle (read environment space) >>= source.2.world.state.read
  if unifyingReady (read environment pattern) rows then
    let next := {control with goals := .query space pattern body destination :: older}
    some (.silent (source.1, ⟨source.2.world,
      {scope with frontier := (next, context, origins) :: pending} :: parents⟩))
  else none

/-- Case enters its source key/selection continuation before ordinary
dispatch. Outside those entrances, completed old steps are retained; only
an explicit query-reference request gains the admitted finite unifier. -/
def ownedStep {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) : Action Context :=
  match ScopedCaseSource.entryStep source with
  | some entered => entered
  | none =>
      match ScopedCaseSource.readyStep plainQueryPattern source with
      | some selected => selected
      | none =>
          match ownershipStep program source with
          | some retained => retained
          | none =>
              let ordinary := step policy program source
              match ordinary with
              | .call (.branch (.invoke "match" [_, _, _] _)) _ =>
                  (unifyingQueryStep source).getD ordinary
              | _ => ordinary

def ownedMachine {Context : Type} (policy : Policy) (program : SpaceSemantics.Program) :
    Machine (ScopedCursor Context) CollectedAnswer (ScopedCursor Context) ScopeBoundary where
  step source := some (ownedStep policy program source)

theorem owned_keeps_completed_step {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (source after : ScopedCursor Context) (owned : ownershipStep program source = none)
    (noCaseEntry : ScopedCaseSource.entryStep source = none)
    (noCaseSelection : ScopedCaseSource.readyStep plainQueryPattern source = none)
    (completed : step policy program source = .silent after) :
    ownedStep policy program source = .silent after := by simp [ownedStep, noCaseEntry, noCaseSelection, owned, completed]

theorem owned_keeps_publication {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (source after : ScopedCursor Context) (events : List CollectedAnswer)
    (owned : ownershipStep program source = none)
    (noCaseEntry : ScopedCaseSource.entryStep source = none)
    (noCaseSelection : ScopedCaseSource.readyStep plainQueryPattern source = none)
    (completed : step policy program source = .publish events after) :
    ownedStep policy program source = .publish events after := by simp [ownedStep, noCaseEntry, noCaseSelection, owned, completed]

theorem unifying_entry {Context : Type} (allocator : Allocator) (world : World)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (control : Control) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (space pattern body destination : Atom) (older : List Goal) (environment : Environment) (rows : List Atom)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke "match" [space, pattern, body] destination :: older)
    (resolved : resolve control.bindings = some environment)
    (readRows : (Effects.readHandle (read environment space) >>= world.state.read) = some rows)
    (admitted : unifyingReady (read environment pattern) rows = true) :
    unifyingQueryStep (allocator, ⟨world, scope :: parents⟩) =
      some (.silent (allocator, ⟨world, {scope with frontier :=
        ({control with goals := .query space pattern body destination :: older}, context, origins) :: pending} :: parents⟩)) := by
  obtain ⟨handle, location, reading⟩ := Option.bind_eq_some_iff.mp readRows
  simp [unifyingQueryStep, frontier, atCall, resolved, location, reading, admitted]

theorem ownership_source_stage_retained {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (space pattern body destination : Atom)
    (older : List Goal) (unowned : queryOwned program = false)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atSource : control.goals = .evaluate (.expression [.symbol "match", space, pattern, body]) destination :: older) :
    ownershipStep program (allocator, ⟨world, scope :: parents⟩) =
      some (.call (.branch (.invoke "match" [space, pattern, body] destination))
        (allocator, ⟨world, scope :: parents⟩)) := by
  simp [ownershipStep, unowned, frontier, atSource]

theorem ownership_ready_stage_retained {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (space pattern body destination : Atom)
    (older : List Goal) (unowned : queryOwned program = false)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atReady : control.goals = .invoke "match" [space, pattern, body] destination :: older) :
    ownershipStep program (allocator, ⟨world, scope :: parents⟩) =
      some (.call (.branch (.invoke "match" [space, pattern, body] destination))
        (allocator, ⟨world, scope :: parents⟩)) := by
  simp [ownershipStep, unowned, frontier, atReady]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource
