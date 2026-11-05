import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryContinuation

/-!
# Named equation entry in the captured-query source profile

The source's complete clause frontier determines entry, including rejected
equations and duplicate occurrences. Selected bodies retain their freshened
syntax, reached equations, caller goals and predicate cut delimiter. This is
an entry theorem, not an inlining law or a claim about the bodies' results.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource.Equations

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open EagerDFS (World)
open EagerDFS.Destination
open EagerDFSStreaming.Scoped

/-- An unresolved output of a nonprimitive call reaches the existing scoped
equation dispatcher without being intercepted as a mutation or query. -/
theorem ordinary_call {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (environment : Environment) (resultName : String)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke head arguments destination :: older)
    (resolved : resolve control.bindings = some environment)
    (unbound : read environment destination = .var resultName)
    (unknown : StdLib.known head = false) :
    (machine policy program).step (allocator, ⟨world, scope :: parents⟩) =
      some (scopeStep policy program (allocator, ⟨world, scope :: parents⟩)) := by
  have notMatch : head ≠ "match" := by
    intro same
    subst head
    simp [StdLib.known] at unknown
  have notAdd : head ≠ "add-atom" := by
    intro same
    subst head
    simp [StdLib.known] at unknown
  have notRemove : head ≠ "remove-atom" := by
    intro same
    subst head
    simp [StdLib.known] at unknown
  have queryNone : queryStep (allocator, ⟨world, scope :: parents⟩) = none := by
    simp only [queryStep, frontier, atCall]
    split
    next space pattern body result rest same =>
      cases same
      exact (notMatch rfl).elim
    next => rfl
  simp [machine, step, syntaxStep, constrainedCall, mutationCall, frontier,
    atCall, resolved, unbound, notMatch, notAdd, notRemove, queryNone]

/-- One actual named invocation installs every selected equation occurrence
in source order. No source-result assumption substitutes for clause coverage. -/
theorem enter {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (environment : Environment) (resultName : String) (selected : List (Nat × Control))
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke head arguments destination :: older)
    (resolved : resolve control.bindings = some environment)
    (unbound : read environment destination = .var resultName)
    (ordinary : head ≠ "parse") (unknown : StdLib.known head = false)
    (notIO : Eval.ioHead head = false)
    (declared : program.equations.any (·.head == head) = true)
    (coverage : ClauseChoice.Frontier program
      (protectControl control (collectionSupport ⟨world, scope :: parents⟩)) head
      (arguments.map (read environment)) destination older
      (List.range program.equations.length) selected) :
    (machine policy program).step (allocator, ⟨world, scope :: parents⟩) =
      some (.silent (allocator, ⟨world, {scope with
        frontier := selected.map (fun row => (predicateEntry pending.length row.2, context,
          origins ++ [row.1])) ++ pending} :: parents⟩)) := by
  rw [ordinary_call policy program allocator world scope parents control context origins pending
    head arguments destination older environment resultName frontier atCall resolved unbound unknown]
  exact congrArg some (ProtectedContinuation.PreReturnStep.source
    (.equations allocator world scope parents control context origins pending head arguments
      destination older environment selected frontier atCall resolved ordinary unknown notIO
      declared coverage)).execution

/-- A retained alternative is an original equation occurrence with the
caller's reached equations extended, not an independently evaluated body. -/
theorem selected_body (program : SpaceSemantics.Program) (control : Control)
    (boundary : Finset String) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List Goal) (selected : List (Nat × Control))
    (occurrence : Nat) (next : Control)
    (coverage : ClauseChoice.Frontier program (protectControl control boundary)
      head arguments destination older (List.range program.equations.length) selected)
    (member : (occurrence, next) ∈ selected) :
    ∃ equation, program.equations[occurrence]? = some equation ∧
      next.destination = control.destination ∧
      next.reserved = control.reserved ∪ boundary ∧
      next.goals = .evaluate (ClauseChoice.freshBody (protectControl control boundary)
        occurrence equation) destination :: older ∧
      next.bindings = control.bindings ++
        [(.expression (.symbol head :: arguments),
          ClauseChoice.freshPattern (protectControl control boundary) occurrence equation)] ∧
      ∃ environment, resolve next.bindings = some environment := by
  have actual := (ClauseChoice.choices_iff_frontier _ _ _ _ _ _ _).mpr coverage
  rw [← actual] at member
  obtain ⟨equation, row, attempted⟩ := (ClauseChoice.mem_choices_iff _ _ _ _ _ _ _ _).mp member
  obtain ⟨dest, reserved, goals, bindings⟩ :=
    ClauseChoice.attempt_preserves_caller _ _ _ _ _ _ _ _ attempted
  have source := (ClauseChoice.selection_iff_attempt _ _ _ _ _ _ _ _ _ row).mpr attempted
  exact ⟨equation, row, dest, reserved, goals, bindings, ClauseChoice.selected_resolves source⟩

/-- The predicate delimiter is restored before older caller goals execute. -/
theorem entered_goals (retained : Nat) (next : Control) (body destination : Atom)
    (older : List Goal) (scheduled : next.goals = .evaluate body destination :: older) :
    (predicateEntry retained next).goals =
      .evaluate body destination :: .restoreCommit next.cutBoundary :: older := by
  simp only [predicateEntry, scheduled]

/-- Clause selection preserves the caller's cut floor before predicate entry
installs its temporary floor. The restoration marker names this old floor. -/
theorem selected_cut_boundary {program : SpaceSemantics.Program} {control : Control}
    {head : String} {arguments : List Atom} {destination : Atom} {older : List Goal}
    {occurrence : Nat} {left body : Atom} {next : Control}
    (selected : ClauseChoice.Selection program control head arguments destination older
      occurrence left body next) : next.cutBoundary = control.cutBoundary := by
  cases selected
  rfl

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource.Equations
