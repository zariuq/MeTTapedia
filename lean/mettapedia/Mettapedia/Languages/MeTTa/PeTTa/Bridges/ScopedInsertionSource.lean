import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedMutationSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedQueryOperands

/-!
# Source insertion with captured payloads and retained callers

The canonical space operand is prepared by the ordinary evaluator. The
payload stays raw source data until the reached bindings read it. The
five-step prefix includes operand preparation, mutation and result refinement;
it neither replays an effect nor executes a captured payload as code.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedInsertionSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open ClosedOnceQueryFrame (FreshFor placed)

def source (handle : NamedSpaces.Handle) (payloadCode : Atom) : Atom :=
  .expression [.symbol "add-atom", Effects.handleValue handle, payloadCode]

def entry (caller : Control) (destination : Atom) (handle : NamedSpaces.Handle) (payloadCode : Atom) : Control :=
  {caller with goals := .evaluate (source handle payloadCode) destination :: caller.goals}

def location (caller : Control) (destination : Atom) (handle : NamedSpaces.Handle) (payloadCode : Atom) : String :=
  freshName (entry caller destination handle payloadCode) 0

def ready (caller : Control) (destination : Atom) (handle : NamedSpaces.Handle) (payloadCode : Atom) : Control :=
  {caller with
    bindings := caller.bindings ++ [(Effects.handleValue handle, .var (location caller destination handle payloadCode))]
    goals := .invoke "add-atom" [.var (location caller destination handle payloadCode), payloadCode] destination :: caller.goals}

def returned (caller : Control) (destination : Atom) (handle : NamedSpaces.Handle) (payloadCode : Atom) : Control :=
  {caller with bindings := (ready caller destination handle payloadCode).bindings ++ [(Effects.boolean true, destination)]}

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

theorem source_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom)
    (handle : NamedSpaces.Handle) (payloadCode payload : Atom) (principal : Environment) (result : String)
    (after : Effects.State) (resolved : resolve caller.bindings = some principal)
    (unbound : read principal destination = .var result) (reading : read principal payloadCode = payload)
    (closed : ∀ environment, read environment payload = payload)
    (ordinaryPayload : ScopedQuerySource.mutationPayload false payload = true)
    (inserted : Effects.insert world.state handle payload = some after) :
    (ScopedQuerySource.machine .relational program).run 5
      (placed allocator world scope parents (entry caller destination handle payloadCode) context origins pending) =
      ([], .exhausted (placed allocator {world with state := after} scope parents
        (returned caller destination handle payloadCode) context (origins ++ [0]) pending)) := by
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
  obtain ⟨rows, snapshot, _⟩ := Effects.insert_reads_back inserted
  have applied : StdLib.apply world.state "add-atom" [Effects.handleValue handle, payload] =
      .ok (after, [Effects.boolean true]) := by
    change (match Effects.readHandle (Effects.handleValue handle) >>= fun target => Effects.insert world.state target payload with
      | some state => Except.ok (state, [Effects.boolean true])
      | none => Except.error Effects.Fault.invalidSpace) = _
    simp [inserted]
  have primitive := ScopedMutationSource.primitive_prefix .relational program allocator world
    {scope with frontier := (ready caller destination handle payloadCode, context, origins) :: pending} parents
    (ready caller destination handle payloadCode) context origins pending "add-atom"
    [.var (location caller destination handle payloadCode), payloadCode] destination representative caller.goals
    environment after (Effects.boolean true) rfl rfl prepared stillUnbound (PresenceGuardSource.read_boolean true)
    (by decide) (by decide) (by decide)
    (by intro _; simp [ScopedQuerySource.mutationReady, handleRead, payloadRead, snapshot, ordinaryPayload])
    (by simpa [handleRead, payloadRead] using applied)
  have first := preparation program allocator world scope parents caller context origins pending destination handle payloadCode
    ⟨principal, resolve_sound resolved⟩
  have combined := (ScopedQuerySource.machine .relational program).established_and_pending 3 2 _ _ [] first
  change (ScopedQuerySource.machine .relational program).run 2
    (placed allocator world scope parents (ready caller destination handle payloadCode) context origins pending) = _ at primitive
  rw [primitive] at combined
  simpa [returned, ready, placed] using combined

theorem returned_consistent (caller : Control) (destination : Atom) (handle : NamedSpaces.Handle)
    (payloadCode : Atom) (principal : Environment) (result : String)
    (resolved : resolve caller.bindings = some principal) (unbound : read principal destination = .var result) :
    ∃ environment, Solves environment (returned caller destination handle payloadCode).bindings := by
  obtain ⟨environment, representative, prepared, stillUnbound⟩ := ScopedMutationSource.unbound_after_fresh_operand
    caller.bindings principal destination (Effects.handleValue handle) result (location caller destination handle payloadCode)
    resolved unbound (location_fresh caller destination handle payloadCode) (location_apart caller destination handle payloadCode)
    (by rw [LiteralQuerySource.handle_freeVars]; simp)
  exact ClosedOnceQueryFrame.refined_consistent _ _ _
    (ScopedMutationSource.refine_unbound (ready caller destination handle payloadCode).bindings environment destination
      (Effects.boolean true) representative prepared stillUnbound (PresenceGuardSource.read_boolean true))

/-- An unavailable canonical target retains the reached invocation after
operand preparation. It does not fabricate an insertion answer or reset the
world to an earlier caller checkpoint. A constrained result also declines at
this same boundary, so no unbound-result assumption is needed here. -/
theorem unavailable_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom)
    (handle : NamedSpaces.Handle) (payloadCode : Atom)
    (consistent : ∃ environment, Solves environment caller.bindings)
    (unavailable : world.state.read handle = none) :
    (ScopedQuerySource.machine .relational program).run 4
      (placed allocator world scope parents (entry caller destination handle payloadCode) context origins pending) =
      ([], .suspended (.branch (.invoke "add-atom"
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
      ([], .suspended (.branch (.invoke "add-atom"
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

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedInsertionSource
