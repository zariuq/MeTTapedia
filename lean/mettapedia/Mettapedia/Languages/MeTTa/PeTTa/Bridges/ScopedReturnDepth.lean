import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedUnifyingQueryContinuation

/-!
# A retained return continuation at its owning collection depth

An inner collection's values are not returns of the outer call. The pending
outer continuation belongs to its suspended caller. These operations reuse
the existing protected-goal attachment and transport it through the actual
collection-entry and returned-work constructions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnDepth

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open EagerDFS (World Scope)
open EagerDFS.Destination
open EagerDFSStreaming.Scoped.ProtectedContinuation

def attachCaller {Context : Type} (suffix : List Goal) (caller : CollectionCaller Context) : CollectionCaller Context :=
  (attach suffix caller.1, caller.2)

def attachSavedCaller {Context : Type} (suffix : List Goal) (scope : CollectionScope Context) : CollectionScope Context :=
  {scope with caller := scope.caller.map (attachCaller suffix)}

/-- Offset zero is the active call scope. At a deeper offset, only the
immediate child's saved caller and the owning scope's frontier are changed. -/
def attachScopes {Context : Type} (suffix : List Goal) : Nat → List (CollectionScope Context) → List (CollectionScope Context)
  | _, [] => []
  | 0, scope :: parents => attachScope suffix scope :: parents
  | 1, child :: parents => attachSavedCaller suffix child :: attachScopes suffix 0 parents
  | offset + 2, child :: parents => child :: attachScopes suffix (offset + 1) parents

def attachAt {Context : Type} (offset : Nat) (suffix : List Goal) (source : ScopedCursor Context) : ScopedCursor Context :=
  (source.1, {source.2 with scopes := attachScopes suffix offset source.2.scopes})

theorem attachAt_zero {Context : Type} (suffix : List Goal) (source : ScopedCursor Context) :
    attachAt 0 suffix source = attachState suffix source := by
  cases scopes : source.2.scopes <;> simp [attachAt, attachScopes, attachState, scopes]

theorem attachAt_world {Context : Type} (offset : Nat) (suffix : List Goal) (source : ScopedCursor Context) :
    (attachAt offset suffix source).1 = source.1 ∧ (attachAt offset suffix source).2.world = source.2.world := ⟨rfl, rfl⟩

theorem attachScopes_length {Context : Type} (suffix : List Goal) (offset : Nat) (scopes : List (CollectionScope Context)) :
    (attachScopes suffix offset scopes).length = scopes.length := by
  induction scopes generalizing offset with
  | nil => simp [attachScopes]
  | cons scope parents ih =>
      cases offset with
      | zero => simp [attachScopes]
      | succ offset => cases offset <;> simp [attachScopes, ih]

theorem immediate_child_frontier_unchanged {Context : Type} (suffix : List Goal)
    (child parent : CollectionScope Context) (parents : List (CollectionScope Context)) :
    ((attachScopes suffix 1 (child :: parent :: parents)).head?).map (fun scope => scope.frontier) =
      some child.frontier := by
  simp [attachScopes, attachSavedCaller]

theorem immediate_child_caller_attached {Context : Type} (suffix : List Goal)
    (child parent : CollectionScope Context) (parents : List (CollectionScope Context)) :
    ((attachScopes suffix 1 (child :: parent :: parents)).head?).map (fun scope => scope.caller) =
      some (child.caller.map (attachCaller suffix)) := by simp [attachScopes, attachSavedCaller]

theorem childName_attach (suffix : List Goal) (control : Control) (boundary : Finset String)
    (protectedNames : names suffix ⊆ control.reserved) :
    childName (attach suffix control) boundary = childName control boundary := by
  change freshName (protectControl (attach suffix control) boundary) 0 =
    freshName (protectControl control boundary) 0
  rw [← attach_protectControl]
  exact attach_freshName suffix _ (protectedNames.trans Finset.subset_union_left) 0

theorem collapseChild_attach (suffix : List Goal) (control : Control) (boundary : Finset String) (expression : Atom)
    (protectedNames : names suffix ⊆ control.reserved) :
    collapseChild (attach suffix control) boundary expression = collapseChild control boundary expression := by
  simp only [collapseChild, attach_bindings, childName_attach suffix control boundary protectedNames,
    attach_support_eq suffix control protectedNames]

theorem collection_entry_moves_obligation_to_saved_caller {Context : Type}
    (suffix : List Goal) (allocator : Allocator) (world : World)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (pending : List (CollectionWork Context)) (child : CollectionWork Context) (caller : CollectionCaller Context) :
    (allocator, Scope.enter world (attachScope suffix scope) (pending.map (attachWork suffix)) parents
      child (attachCaller suffix caller)) =
      attachAt 1 suffix (allocator, Scope.enter world scope pending parents child caller) := by
  simp [Scope.enter, attachAt, attachScopes, attachSavedCaller, attachScope]

theorem allocated_return_keeps_pending_caller {Context : Type} (suffix : List Goal)
    (copies : List (Token × (Atom × List Atom))) (caller : CollectionCaller Context) :
    allocatedWork copies (attachCaller suffix caller) = attachWork suffix (allocatedWork copies caller) := by
  simp only [allocatedWork, attachCaller, attachWork, attach, List.map_cons, shift, List.cons_append]

theorem copied_return_keeps_pending_caller {Context : Type} (suffix : List Goal)
    (boundary : Finset String) (answers : List CollectedAnswer) (caller : CollectionCaller Context) :
    copiedWork boundary answers (attachCaller suffix caller) = attachWork suffix (copiedWork boundary answers caller) := by
  simp only [copiedWork, attachCaller, attachWork, attach, List.map_cons, shift, List.cons_append]

theorem attachSavedCaller_support {Context : Type} (suffix : List Goal) (scope : CollectionScope Context)
    (protectedNames : ∀ caller, scope.caller = some caller → names suffix ⊆ caller.1.reserved) :
    (attachSavedCaller suffix scope).support = scope.support := by
  cases saved : scope.caller with
  | none => simp [attachSavedCaller, CollectionScope.support, saved]
  | some caller =>
      simp only [attachSavedCaller, CollectionScope.support, saved, Option.map_some,
        Option.getD_some, attachCaller, attach_support_eq suffix caller.1 (protectedNames caller saved)]

theorem attachAt_one_support {Context : Type} (suffix : List Goal) (allocator : Allocator) (world : World)
    (child parent : CollectionScope Context) (parents : List (CollectionScope Context))
    (savedNames : ∀ caller, child.caller = some caller → names suffix ⊆ caller.1.reserved)
    (pendingNames : ∀ work ∈ parent.frontier, names suffix ⊆ work.1.reserved) :
    collectionSupport (attachAt 1 suffix (allocator, ⟨world, child :: parent :: parents⟩)).2 =
      collectionSupport (⟨world, child :: parent :: parents⟩ : CollectionConfiguration Context) := by
  simp only [attachAt, attachScopes, collectionSupport, List.foldr_cons,
    attachSavedCaller_support suffix child savedNames, attachScope_support suffix parent pendingNames]

/-- The actual generative finish operation takes precisely the same copy
path, including failure to serve it. Only the resumed caller receives the
retained suffix; collected values and their order are untouched. -/
theorem finishAllocated_attach {Context : Type} (suffix : List Goal) (allocator : Allocator) (world : World)
    (answers : List CollectedAnswer) (caller : CollectionCaller Context)
    (parent : CollectionScope Context) (parents : List (CollectionScope Context))
    (savedNames : names suffix ⊆ caller.1.reserved)
    (pendingNames : ∀ work ∈ parent.frontier, names suffix ⊆ work.1.reserved) :
    finishAllocated? (attachAt 1 suffix (allocator, ⟨world, ⟨[], answers, some caller⟩ :: parent :: parents⟩)) =
      (finishAllocated? (allocator, ⟨world, ⟨[], answers, some caller⟩ :: parent :: parents⟩)).map (attachAt 0 suffix) := by
  have sameBoundary := attachAt_one_support suffix allocator world ⟨[], answers, some caller⟩ parent parents
    (by intro found saved; cases Option.some.inj saved; exact savedNames) pendingNames
  change collectionSupport (⟨world, attachSavedCaller suffix ⟨[], answers, some caller⟩ ::
    attachScope suffix parent :: parents⟩ : CollectionConfiguration Context) = _ at sameBoundary
  simp only [finishAllocated?, attachAt, attachScopes, attachSavedCaller, Option.map_some, attachScope]
  split
  · rfl
  · dsimp only [bind, Option.bind]
    change collectionSupport (⟨world,
      {frontier := [], collected := answers, caller := some (attachCaller suffix caller)} ::
        {parent with frontier := parent.frontier.map (attachWork suffix)} :: parents⟩ : CollectionConfiguration Context) = _ at sameBoundary
    rw [sameBoundary]
    cases copied : EagerDFS.Collection.copyOwnedAnswers? allocator
        (collectionSupport (⟨world, ⟨[], answers, some caller⟩ :: parent :: parents⟩ : CollectionConfiguration Context))
        (answers.map fun answer => (answer.value, answer.associated)) with
    | none => rfl
    | some packet =>
        rcases packet with ⟨after, copies⟩
        simp only [pure, Option.map_some, attachAt, attachScopes, attachScope, List.map_cons,
          allocated_return_keeps_pending_caller]

/-- Actual source collapse entry moves the caller obligation down one scope.
The child's code, destination, record and allocator are not contaminated by
the outer continuation. -/
theorem collapse_entry_attach {Context : Type} (suffix : List Goal) (allocator : Allocator)
    (world : World) (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (control : Control) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (expression destination : Atom) (older : List Goal)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atEntry : control.goals = .evaluate (.expression [.symbol "collapse", expression]) destination :: older)
    (protectedNames : Protected suffix (allocator, ⟨world, scope :: parents⟩)) :
    enterCollapse? (attachAt 0 suffix (allocator, ⟨world, scope :: parents⟩)).2 =
      some (attachAt 1 suffix (allocator, Scope.enter world scope pending parents
        (collapseChild control (collectionSupport ⟨world, scope :: parents⟩) expression, context, origins)
        ({control with goals := older}, destination, context, origins))).2 := by
  have protectedControl : names suffix ⊆ control.reserved :=
    protectedNames (control, context, origins) (frontier ▸ List.mem_cons_self)
  have sameBoundary : collectionSupport (⟨world, attachScope suffix scope :: parents⟩ : CollectionConfiguration Context) =
      collectionSupport (⟨world, scope :: parents⟩ : CollectionConfiguration Context) :=
    attachState_support suffix (allocator, ⟨world, scope :: parents⟩) protectedNames
  have entered := enterCollapse_constructs world (attachScope suffix scope) parents (attach suffix control)
    context origins (pending.map (attachWork suffix)) expression destination
    (older.map (shift suffix.length) ++ suffix)
    (by simp only [attachScope, frontier, List.map_cons, attachWork])
    (by simp only [attach, atEntry, List.map_cons, shift, List.cons_append])
  rw [sameBoundary, collapseChild_attach suffix control _ _ protectedControl] at entered
  simpa only [attachAt, attachScopes, Scope.enter, attachSavedCaller, Option.map_some,
    attachCaller, attachScope, attach] using entered

/-- Attaching the outer return to the active child's frontier is observably
a different construction whenever real child work and a real suffix remain.
It would make the child execute work belonging to its suspended caller. -/
theorem active_child_is_not_the_suspended_caller {Context : Type} (suffix : List Goal)
    (nonempty : suffix ≠ []) (allocator : Allocator) (world : World)
    (child parent : CollectionScope Context) (parents : List (CollectionScope Context))
    (work : CollectionWork Context) (pending : List (CollectionWork Context))
    (frontier : child.frontier = work :: pending) :
    attachAt 0 suffix (allocator, ⟨world, child :: parent :: parents⟩) ≠
      attachAt 1 suffix (allocator, ⟨world, child :: parent :: parents⟩) := by
  intro same
  have observed := congrArg (fun source : ScopedCursor Context => source.2.scopes.head?.bind
    fun scope => scope.frontier.head?.map fun item => item.1.goals.length) same
  simp only [attachAt, attachScopes, List.head?_cons, Option.bind_some, attachScope,
    attachSavedCaller, frontier, List.map_cons, Option.map_some, attachWork, attach,
    List.length_append, List.length_map, Option.some.injEq] at observed
  have zero : suffix.length = 0 := by omega
  exact nonempty (List.length_eq_zero_iff.mp zero)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnDepth
