import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryContinuation
import Mettapedia.Languages.MeTTa.PeTTa.DestinationMatchSource

/-!
# Two-way query selection with a retained source caller

The existing protected-continuation operation transports the full ordered
query frontier, including rejected rows. Caller protection makes the row
allocator identical, so open stored variables cannot capture a saved name.
This extends the existing captured-query owner; it is not another scheduler.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource.Caller

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS (World)
open EagerDFS.Destination
open EagerDFSStreaming.Scoped.ProtectedContinuation

theorem queryRow_attach (suffix : List Goal) (control : Control)
    (protectedNames : names suffix ⊆ control.reserved) (occurrence : Nat) (row : Atom) :
    queryRow (attach suffix control) occurrence row = queryRow control occurrence row := by
  have renamer : ClauseChoice.rename (attach suffix control) occurrence [row] =
      ClauseChoice.rename control occurrence [row] := by
    funext name
    exact attach_freshName suffix control protectedNames _
  unfold queryRow
  rw [renamer]

theorem query_frontier_attach {control : Control} {pattern template destination : Atom}
    {older : List Goal} {start : Nat} {rows : List Atom} {selected : List (Nat × Control)}
    (source : QueryFrontier control pattern template destination older start rows selected)
    (suffix : List Goal) (protectedNames : names suffix ⊆ control.reserved) :
    QueryFrontier (attach suffix control) pattern template destination
      (older.map (shift suffix.length) ++ suffix) start rows
      (selected.map fun row => (row.1, attach suffix row.2)) := by
  induction source with
  | nil => exact .nil _
  | selected start row rest bindings tail accepted following ih =>
      have compatible : Refinement (attach suffix control).bindings pattern
          (queryRow (attach suffix control) start row) (some bindings) := by
        simpa only [attach_bindings, queryRow_attach suffix control protectedNames] using accepted
      simpa only [List.map_cons, attach, List.map_cons, shift, List.cons_append] using
        QueryFrontier.selected start row rest bindings _ compatible ih
  | refused start row rest tail rejected following ih =>
      have incompatible : Refinement (attach suffix control).bindings pattern
          (queryRow (attach suffix control) start row) none := by
        simpa only [attach_bindings, queryRow_attach suffix control protectedNames] using rejected
      exact .refused start row rest _ incompatible ih

theorem query_choices_attach (suffix : List Goal) (control : Control)
    (protectedNames : names suffix ⊆ control.reserved) (pattern template destination : Atom)
    (older : List Goal) (rows : List Atom) (start : Nat) :
    queryChoices (attach suffix control) pattern template destination
        (older.map (shift suffix.length) ++ suffix) rows start =
      (queryChoices control pattern template destination older rows start).map
        (fun row => (row.1, attach suffix row.2)) :=
  (query_frontier_attach (queryChoices_has_source _ _ _ _ _ _ _) suffix protectedNames).execution

theorem query_work_attach {Context : Type} (suffix : List Goal) (control : Control)
    (protectedNames : names suffix ⊆ control.reserved) (context : Context) (origins : List Nat)
    (pattern template destination : Atom) (older : List Goal) (rows : List Atom) :
    queryWork (attach suffix control) context origins pattern template destination
        (older.map (shift suffix.length) ++ suffix) rows =
      (queryWork control context origins pattern template destination older rows).map (attachWork suffix) := by
  simp only [queryWork, query_choices_attach suffix control protectedNames,
    List.map_map, Function.comp_def, attachWork]

theorem query_selected_protected {control : Control} {pattern template destination : Atom}
    {older : List Goal} {start : Nat} {rows : List Atom} {selected : List (Nat × Control)}
    (source : QueryFrontier control pattern template destination older start rows selected)
    (suffix : List Goal) (protectedNames : names suffix ⊆ control.reserved) :
    ∀ chosen ∈ selected, names suffix ⊆ chosen.2.reserved := by
  induction source with
  | nil => simp
  | selected start row rest bindings tail accepted following ih =>
      intro chosen present
      rcases List.mem_cons.mp present with rfl | later
      · exact protectedNames
      · exact ih chosen later
  | refused start row rest tail rejected following ih => exact ih

theorem owned_query_step {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (space pattern body destination : Atom) (older : List Goal) (environment : Environment)
    (rows : List Atom) (selected : List (Nat × Control))
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atQuery : control.goals = .query space pattern body destination :: older)
    (resolved : resolve control.bindings = some environment)
    (snapshot : (Effects.readHandle (read environment space) >>= world.state.read) = some rows)
    (coverage : QueryFrontier (protectControl control (collectionSupport ⟨world, scope :: parents⟩))
      pattern body destination older 0 rows selected) :
    (ownedMachine policy program).step (allocator, ⟨world, scope :: parents⟩) =
      some (.silent (allocator, ⟨world, {scope with frontier :=
        (selected.map (fun row => (row.2, context, origins ++ [row.1]))) ++ pending} :: parents⟩)) := by
  have actual := Source.ScopedStep.execution
    (Source.ScopedStep.active (fresh := Source.FreshOperations.owned) (policy := policy) (program := program)
      allocator world scope parents control context origins pending _ frontier
      (.queried space pattern body destination older environment rows selected atQuery resolved snapshot coverage))
  simp [ownedMachine, ownedStep, ownershipStep, step, syntaxStep, constrainedCall,
    ScopedCaseSource.entryStep, ScopedCaseSource.readyStep,
    mutationCall, queryStep, frontier, atQuery, actual]

/-- An actual two-way query entry, with current-space reading and its complete
ordered scan, commutes with appending a protected caller continuation. -/
theorem owned_query_step_attach {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (space pattern body destination : Atom) (older suffix : List Goal) (environment : Environment)
    (rows : List Atom) (selected : List (Nat × Control))
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atQuery : control.goals = .query space pattern body destination :: older)
    (resolved : resolve control.bindings = some environment)
    (snapshot : (Effects.readHandle (read environment space) >>= world.state.read) = some rows)
    (coverage : QueryFrontier (protectControl control (collectionSupport ⟨world, scope :: parents⟩))
      pattern body destination older 0 rows selected)
    (protectedNames : Protected suffix (allocator, ⟨world, scope :: parents⟩)) :
    (ownedMachine policy program).step (attachState suffix (allocator, ⟨world, scope :: parents⟩)) =
      some (.silent (attachState suffix (allocator, ⟨world, {scope with frontier :=
        (selected.map (fun row => (row.2, context, origins ++ [row.1]))) ++ pending} :: parents⟩))) := by
  have protectedControl : names suffix ⊆ control.reserved :=
    protectedNames (control, context, origins) (frontier ▸ List.mem_cons_self)
  have attachedSupport : collectionSupport (⟨world, attachScope suffix scope :: parents⟩ : CollectionConfiguration Context) =
      collectionSupport (⟨world, scope :: parents⟩ : CollectionConfiguration Context) := by
    exact attachState_support suffix (allocator, ⟨world, scope :: parents⟩) protectedNames
  have attachedCoverage := query_frontier_attach coverage suffix
    (protectedControl.trans Finset.subset_union_left)
  have targetCoverage : QueryFrontier
      (protectControl (attach suffix control) (collectionSupport ⟨world, attachScope suffix scope :: parents⟩))
      pattern body destination (older.map (shift suffix.length) ++ suffix) 0 rows
      (selected.map fun row => (row.1, attach suffix row.2)) := by
    simpa only [attachedSupport, attach_protectControl] using attachedCoverage
  have actual := owned_query_step policy program allocator world (attachScope suffix scope) parents
    (attach suffix control) context origins (pending.map (attachWork suffix)) space pattern body destination
    (older.map (shift suffix.length) ++ suffix) environment rows
    (selected.map fun row => (row.1, attach suffix row.2))
    (by simp only [attachScope, frontier, List.map_cons, attachWork])
    (by simp only [attach, atQuery, List.map_cons, shift, List.cons_append])
    resolved snapshot targetCoverage
  simpa only [attachState, attachScope, List.map_append, List.map_map, Function.comp_def, attachWork] using actual

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource.Caller
