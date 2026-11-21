import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedMutationSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedQueryOperands

/-!
# Raw source removal through a retained caller

The canonical handle operand is prepared before the ordinary ground-fact
mutation. The payload remains raw source and is read in the reached frame.
Removal deletes every matching copy and answers whether the target changed:
true exactly when some stored row matches, false when the fact is already
absent. Current destination admission and a readable target construct the
successful receipt; no future successful primitive or already-prepared frame
is assumed by `source_exists`. This is a local source prefix, not a complete
drop call.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedRemovalSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open ClosedOnceQueryFrame (FreshFor placed)

def source (handle : NamedSpaces.Handle) (payloadCode : Atom) : Atom :=
  .expression [.symbol "remove-atom", Effects.handleValue handle, payloadCode]

def entry (caller : Control) (destination : Atom) (handle : NamedSpaces.Handle) (payloadCode : Atom) : Control :=
  {caller with goals := .evaluate (source handle payloadCode) destination :: caller.goals}

def location (caller : Control) (destination : Atom) (handle : NamedSpaces.Handle) (payloadCode : Atom) : String :=
  freshName (entry caller destination handle payloadCode) 0

def ready (caller : Control) (destination : Atom) (handle : NamedSpaces.Handle) (payloadCode : Atom) : Control :=
  {caller with
    bindings := caller.bindings ++ [(Effects.handleValue handle, .var (location caller destination handle payloadCode))]
    goals := .invoke "remove-atom" [.var (location caller destination handle payloadCode), payloadCode] destination :: caller.goals}

/-- The caller after the removal reply `changed` is equated with its destination. -/
def returned (caller : Control) (destination : Atom) (handle : NamedSpaces.Handle) (payloadCode : Atom)
    (changed : Bool) : Control :=
  {caller with bindings := (ready caller destination handle payloadCode).bindings ++ [(Effects.boolean changed, destination)]}

theorem location_fresh (caller : Control) (destination : Atom) (handle : NamedSpaces.Handle) (payloadCode : Atom) :
    FreshFor (location caller destination handle payloadCode) caller.bindings :=
  ClosedOnceQueryFrame.fresh_for_bindings (entry caller destination handle payloadCode) _ (freshName_not_mem _ _)

theorem location_apart (caller : Control) (destination : Atom) (handle : NamedSpaces.Handle) (payloadCode : Atom) :
    location caller destination handle payloadCode ∉ (encode destination).freeVars := by
  intro member
  apply freshName_not_mem (entry caller destination handle payloadCode) 0
  apply Finset.mem_union_right
  apply (ClosedOnceQueryFrame.fold_support_iff _ _ _).mpr
  exact Or.inr ⟨destination, by simp [entry, Goal.atoms], member⟩

theorem location_refined (caller : Control) (destination : Atom) (handle : NamedSpaces.Handle) (payloadCode : Atom)
    (consistent : ∃ environment, Solves environment caller.bindings) :
    refine caller.bindings (Effects.handleValue handle) (.var (location caller destination handle payloadCode)) =
      some (ready caller destination handle payloadCode).bindings :=
  ClosedOnceQueryFrame.refine_fresh_closed _ _ _ (location_fresh caller destination handle payloadCode)
    consistent (LiteralQuerySource.read_handle handle)

set_option maxHeartbeats 1200000 in
theorem preparation {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom)
    (handle : NamedSpaces.Handle) (payloadCode : Atom)
    (consistent : ∃ environment, Solves environment caller.bindings) :
    (ScopedQuerySource.machine .relational program).run 3
      (placed allocator world scope parents (entry caller destination handle payloadCode) context origins pending) =
      ([], .exhausted (placed allocator world scope parents (ready caller destination handle payloadCode) context origins pending)) := by
  have refined := location_refined caller destination handle payloadCode consistent
  simp only [ready, location, entry, source] at refined
  cases handle <;>
    simp [Machine.run, ScopedQuerySource.machine, ScopedQuerySource.step, ScopedQuerySource.syntaxStep,
      ScopedQuerySource.constrainedCall, ScopedQuerySource.mutationCall, ScopedQuerySource.queryStep,
      placed, entry, source, scopeStep, enterCollapse?, enterSuperpose?, EagerDFS.Destination.machine,
      prepare, replace, installChild, retainChild, callable, StdLib.known, Eval.ioHead,
      callArguments, freshSlots, List.range_succ, Eval.argumentIsRaw, StdLib.rawArgument,
      ready, location, Effects.handleValue] at refined ⊢ <;> simp [refined]

/-- An ordinary ground removal payload supplies every value native removal demands. -/
private theorem payload_specified (payload : Atom) (ordinary : ScopedQuerySource.mutationPayload true payload = true) :
    Effects.removalNeedsValue payload = false := by
  unfold Effects.removalNeedsValue
  split
  · simp [ScopedQuerySource.mutationPayload, Mettapedia.Languages.ProcessCalculi.MORK.isGroundAtom] at ordinary
  · simp [ScopedQuerySource.mutationPayload] at ordinary
  · rfl

theorem source_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom)
    (handle : NamedSpaces.Handle) (payloadCode payload : Atom) (principal : Environment) (result : String)
    (rows : List Atom) (after : Effects.State) (resolved : resolve caller.bindings = some principal)
    (unbound : read principal destination = .var result) (reading : read principal payloadCode = payload)
    (closed : ∀ environment, read environment payload = payload)
    (ordinaryPayload : ScopedQuerySource.mutationPayload true payload = true)
    (snapshot : world.state.read handle = some rows) (complete : ClosedQueryAdmission.rowsReady payload rows = true)
    (erased : Effects.erase world.state handle payload = some after) :
    (ScopedQuerySource.machine .relational program).run 5
      (placed allocator world scope parents (entry caller destination handle payloadCode) context origins pending) =
      ([], .exhausted (placed allocator {world with state := after} scope parents
        (returned caller destination handle payloadCode (Effects.erasureChanged world.state after handle))
        context (origins ++ [0]) pending)) := by
  obtain ⟨environment, representative, prepared, stillUnbound⟩ := ScopedMutationSource.unbound_after_fresh_operand
    caller.bindings principal destination (Effects.handleValue handle) result (location caller destination handle payloadCode)
    resolved unbound (location_fresh caller destination handle payloadCode) (location_apart caller destination handle payloadCode)
    (by rw [LiteralQuerySource.handle_freeVars]; simp)
  have inherited : Solves environment caller.bindings := by
    intro pair member
    exact resolve_sound prepared pair (List.mem_append_left _ member)
  have payloadRead := CapturedQueryOperands.resolved_forces resolved payloadCode payload reading closed environment inherited
  have handleRead : read environment (.var (location caller destination handle payloadCode)) = Effects.handleValue handle := by
    have bound := resolve_sound prepared (Effects.handleValue handle, .var (location caller destination handle payloadCode))
      (List.mem_append_right _ (by simp))
    rw [LiteralQuerySource.read_handle] at bound
    exact bound.symm
  have applied := StdLib.remove_atom_applies_of_erased (payload_specified payload ordinaryPayload) erased
  have primitive := ScopedMutationSource.primitive_prefix .relational program allocator world
    {scope with frontier := (ready caller destination handle payloadCode, context, origins) :: pending} parents
    (ready caller destination handle payloadCode) context origins pending "remove-atom"
    [.var (location caller destination handle payloadCode), payloadCode] destination representative caller.goals
    environment after (Effects.boolean (Effects.erasureChanged world.state after handle)) rfl rfl prepared stillUnbound
    (PresenceGuardSource.read_boolean _)
    (by decide) (by decide) (by decide)
    (by intro _; simp [ScopedQuerySource.mutationReady, handleRead, payloadRead, snapshot, ordinaryPayload, complete])
    (by simpa [handleRead, payloadRead] using applied)
  have began := preparation program allocator world scope parents caller context origins pending destination handle payloadCode
    ⟨principal, resolve_sound resolved⟩
  have combined := (ScopedQuerySource.machine .relational program).established_and_pending 3 2 _ _ [] began
  change (ScopedQuerySource.machine .relational program).run 2
    (placed allocator world scope parents (ready caller destination handle payloadCode) context origins pending) = _ at primitive
  rw [primitive] at combined
  simpa [returned, ready, placed] using combined

/-- Readability constructs the primitive receipt, and source execution
derives the exact filtered target, the change reply and the unchanged
external frame. The reply is true exactly when a stored row matches. -/
theorem source_exists {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom)
    (handle : NamedSpaces.Handle) (payloadCode payload : Atom) (principal : Environment) (result : String)
    (rows : List Atom) (resolved : resolve caller.bindings = some principal)
    (unbound : read principal destination = .var result) (reading : read principal payloadCode = payload)
    (closed : ∀ environment, read environment payload = payload)
    (ordinaryPayload : ScopedQuerySource.mutationPayload true payload = true)
    (snapshot : world.state.read handle = some rows) (complete : ClosedQueryAdmission.rowsReady payload rows = true) :
    ∃ after, Effects.erase world.state handle payload = some after ∧
      (ScopedQuerySource.machine .relational program).run 5
        (placed allocator world scope parents (entry caller destination handle payloadCode) context origins pending) =
        ([], .exhausted (placed allocator {world with state := after} scope parents
          (returned caller destination handle payloadCode (Effects.erasureChanged world.state after handle))
          context (origins ++ [0]) pending)) ∧
      (Effects.erasureChanged world.state after handle = true ↔
        ∃ row ∈ rows, Effects.removalMatches payload row = true) ∧
      after.read handle = some (rows.filter fun row => !Effects.removalMatches payload row) ∧
      (∀ other, other ≠ handle → after.read other = world.state.read other) ∧ after.cells = world.state.cells := by
  obtain ⟨after, erased⟩ := Effects.erase_exists_of_read_some snapshot payload
  obtain ⟨actual, actualRead, afterRead⟩ := Effects.erase_reads_back erased
  have same : actual = rows := Option.some.inj (actualRead.symm.trans snapshot)
  subst actual
  exact ⟨after, erased, source_prefix program allocator world scope parents caller context origins pending destination
    handle payloadCode payload principal result rows after resolved unbound reading closed ordinaryPayload snapshot complete erased,
    Effects.erasureChanged_iff snapshot erased, afterRead, fun other apart => Effects.erase_read_other erased apart, Effects.erase_preserves_cells erased⟩

theorem returned_consistent (caller : Control) (destination : Atom) (handle : NamedSpaces.Handle)
    (payloadCode : Atom) (changed : Bool) (principal : Environment) (result : String)
    (resolved : resolve caller.bindings = some principal) (unbound : read principal destination = .var result) :
    ∃ environment, Solves environment (returned caller destination handle payloadCode changed).bindings := by
  obtain ⟨environment, representative, prepared, stillUnbound⟩ := ScopedMutationSource.unbound_after_fresh_operand
    caller.bindings principal destination (Effects.handleValue handle) result (location caller destination handle payloadCode)
    resolved unbound (location_fresh caller destination handle payloadCode) (location_apart caller destination handle payloadCode)
    (by rw [LiteralQuerySource.handle_freeVars]; simp)
  exact ClosedOnceQueryFrame.refined_consistent _ _ _
    (ScopedMutationSource.refine_unbound (ready caller destination handle payloadCode).bindings environment destination
      (Effects.boolean changed) representative prepared stillUnbound (PresenceGuardSource.read_boolean changed))

/-- A missing target retains the actual invocation after preparation, with
no removal and no fabricated Boolean or empty result. -/
theorem unavailable_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom)
    (handle : NamedSpaces.Handle) (payloadCode : Atom)
    (consistent : ∃ environment, Solves environment caller.bindings)
    (unavailable : world.state.read handle = none) :
    (ScopedQuerySource.machine .relational program).run 4
      (placed allocator world scope parents (entry caller destination handle payloadCode) context origins pending) =
      ([], .suspended (.branch (.invoke "remove-atom"
        [.var (location caller destination handle payloadCode), payloadCode] destination))
        (placed allocator world scope parents (ready caller destination handle payloadCode) context origins pending)) := by
  have refined := location_refined caller destination handle payloadCode consistent
  obtain ⟨environment, resolved⟩ := resolve_complete (ClosedOnceQueryFrame.refined_consistent _ _ _ refined)
  have handleRead : read environment (.var (location caller destination handle payloadCode)) = Effects.handleValue handle := by
    have bound := resolve_sound resolved (Effects.handleValue handle, .var (location caller destination handle payloadCode))
      (List.mem_append_right _ (by simp))
    rw [LiteralQuerySource.read_handle] at bound
    exact bound.symm
  have last : (ScopedQuerySource.machine .relational program).run 1
      (placed allocator world scope parents (ready caller destination handle payloadCode) context origins pending) =
      ([], .suspended (.branch (.invoke "remove-atom"
        [.var (location caller destination handle payloadCode), payloadCode] destination))
        (placed allocator world scope parents (ready caller destination handle payloadCode) context origins pending)) := by
    cases result : read environment destination <;>
      simp [Machine.run, ScopedQuerySource.machine, ScopedQuerySource.step, ScopedQuerySource.syntaxStep,
        ScopedQuerySource.constrainedCall, ScopedQuerySource.mutationCall, ScopedQuerySource.mutationReady,
        placed, ready, resolved, result, handleRead, unavailable]
  have began := preparation program allocator world scope parents caller context origins pending destination handle payloadCode consistent
  have combined := (ScopedQuerySource.machine .relational program).established_and_pending 3 1 _ _ [] began
  rw [last] at combined
  simpa using combined

namespace Controls

def fact : Atom := .expression [.symbol "fact"]

def caller : Control := ⟨[], [], .var "r", ∅, 0⟩

def world (rows : List Atom) : World := ⟨NamedSpaces.Store.new rows [], [], []⟩

/-- `(remove-atom &self (fact))` run as source over the `&self` rows `rows`. -/
private theorem run_on (program : SpaceSemantics.Program) (rows : List Atom)
    (complete : ClosedQueryAdmission.rowsReady fact rows = true) :
    ∃ after, (ScopedQuerySource.machine .relational program).run 5
        (placed (Allocator.empty 0 0) (world rows) ({frontier := []} : CollectionScope Unit) []
          (entry caller (.var "r") .self fact) () [] []) =
        ([], .exhausted (placed (Allocator.empty 0 0) {world rows with state := after} {frontier := []} []
          (returned caller (.var "r") .self fact (Effects.erasureChanged (world rows).state after .self))
          () [0] [])) ∧
      (Effects.erasureChanged (world rows).state after .self = true ↔
        ∃ row ∈ rows, Effects.removalMatches fact row = true) ∧
      after.read .self = some (rows.filter fun row => !Effects.removalMatches fact row) := by
  obtain ⟨principal, resolved⟩ := resolve_complete (source := caller.bindings)
    ⟨fun _ => .var "x", fun _ member => absurd member List.not_mem_nil⟩
  have unbound : read principal (.var "r") = .var "r" :=
    ClosedOnceQueryFrame.fresh_read [] "r" principal (fun _ member => absurd member List.not_mem_nil) resolved
  have closed := LiteralQuerySource.read_literal fact
    (SpaceSemantics.Literal.constructor "fact" [] (by decide) fun _ member => absurd member List.not_mem_nil)
  obtain ⟨after, _, run, changed, afterRead, _⟩ := source_exists program (Allocator.empty 0 0) (world rows)
    {frontier := []} [] caller () [] [] (.var "r") .self fact fact principal "r" rows
    resolved unbound (closed principal) closed rfl rfl complete
  exact ⟨after, run, changed, afterRead⟩

/-- Negative: an absent fact is not removed, and the reply is false. -/
theorem absent_answers_false (program : SpaceSemantics.Program) :
    ∃ after, (ScopedQuerySource.machine .relational program).run 5
        (placed (Allocator.empty 0 0) (world []) ({frontier := []} : CollectionScope Unit) []
          (entry caller (.var "r") .self fact) () [] []) =
        ([], .exhausted (placed (Allocator.empty 0 0) {world [] with state := after} {frontier := []} []
          (returned caller (.var "r") .self fact false) () [0] [])) ∧
      after.read .self = some [] := by
  obtain ⟨after, run, changed, afterRead⟩ := run_on program [] rfl
  have unchanged : Effects.erasureChanged (world []).state after .self = false :=
    Bool.eq_false_iff.mpr fun yes => by simpa using changed.mp yes
  exact ⟨after, unchanged ▸ run, afterRead⟩

/-- Positive: every stored copy is removed, and the reply is true. -/
theorem copies_removed_answers_true (program : SpaceSemantics.Program) :
    ∃ after, (ScopedQuerySource.machine .relational program).run 5
        (placed (Allocator.empty 0 0) (world [fact, fact]) ({frontier := []} : CollectionScope Unit) []
          (entry caller (.var "r") .self fact) () [] []) =
        ([], .exhausted (placed (Allocator.empty 0 0) {world [fact, fact] with state := after} {frontier := []} []
          (returned caller (.var "r") .self fact true) () [0] [])) ∧
      after.read .self = some [] := by
  have matched : Effects.removalMatches fact fact = true := Effects.removalMatches_self _ _
  obtain ⟨after, run, changed, afterRead⟩ := run_on program [fact, fact] (by decide)
  have removed : Effects.erasureChanged (world [fact, fact]).state after .self = true :=
    changed.mpr ⟨fact, by simp, matched⟩
  exact ⟨after, removed ▸ run, by simpa [matched] using afterRead⟩

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedRemovalSource

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedRemovalSource.source_exists
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedRemovalSource.unavailable_prefix
