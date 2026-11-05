import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedInsertionSource

/-!
# Authored match preparation in a retained frame

The canonical handle operand is evaluated once into a fresh slot. Pattern
and body remain raw syntax. The resulting equation is retained by every
captured child; it is not erased when later query frames are assembled.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedMatchPreparation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open ClosedOnceQueryFrame (FreshFor placed)

def source (handle : NamedSpaces.Handle) (pattern body : Atom) : Atom :=
  .expression [.symbol "match", Effects.handleValue handle, pattern, body]

def entry (caller : Control) (destination : Atom) (handle : NamedSpaces.Handle) (pattern body : Atom) : Control :=
  {caller with goals := .evaluate (source handle pattern body) destination :: caller.goals}

def location (caller : Control) (destination : Atom) (handle : NamedSpaces.Handle) (pattern body : Atom) : String :=
  freshName (entry caller destination handle pattern body) 0

def ready (caller : Control) (destination : Atom) (handle : NamedSpaces.Handle) (pattern body : Atom) : Control :=
  {caller with
    bindings := caller.bindings ++ [(Effects.handleValue handle, .var (location caller destination handle pattern body))]
    goals := .invoke "match" [.var (location caller destination handle pattern body), pattern, body] destination :: caller.goals}

theorem location_fresh (caller : Control) (destination : Atom) (handle : NamedSpaces.Handle) (pattern body : Atom) :
    FreshFor (location caller destination handle pattern body) caller.bindings :=
  ClosedOnceQueryFrame.fresh_for_bindings (entry caller destination handle pattern body) _ (freshName_not_mem _ _)

theorem location_refined (caller : Control) (destination : Atom) (handle : NamedSpaces.Handle) (pattern body : Atom)
    (consistent : ∃ environment, Solves environment caller.bindings) :
    refine caller.bindings (Effects.handleValue handle) (.var (location caller destination handle pattern body)) =
      some (ready caller destination handle pattern body).bindings :=
  ClosedOnceQueryFrame.refine_fresh_closed _ _ _ (location_fresh caller destination handle pattern body)
    consistent (LiteralQuerySource.read_handle handle)

theorem ready_consistent (caller : Control) (destination : Atom) (handle : NamedSpaces.Handle) (pattern body : Atom)
    (consistent : ∃ environment, Solves environment caller.bindings) :
    ∃ environment, Solves environment (ready caller destination handle pattern body).bindings :=
  ClosedOnceQueryFrame.refined_consistent _ _ _ (location_refined caller destination handle pattern body consistent)

theorem ready_inherited (caller : Control) (destination : Atom) (handle : NamedSpaces.Handle) (pattern body : Atom)
    (environment : Environment) (solved : Solves environment (ready caller destination handle pattern body).bindings) :
    Solves environment caller.bindings := by
  intro pair member
  exact solved pair (List.mem_append_left _ member)

theorem ready_location (caller : Control) (destination : Atom) (handle : NamedSpaces.Handle) (pattern body : Atom)
    (principal : Environment) (resolved : resolve (ready caller destination handle pattern body).bindings = some principal) :
    read principal (.var (location caller destination handle pattern body)) = Effects.handleValue handle := by
  have equation := resolve_sound resolved (Effects.handleValue handle, .var (location caller destination handle pattern body))
    (List.mem_append_right _ (by simp))
  rw [LiteralQuerySource.read_handle] at equation
  exact equation.symm

theorem retained_fresh (caller : Control) (destination : Atom) (handle : NamedSpaces.Handle) (pattern body : Atom)
    (name : String) (fresh : FreshFor name caller.bindings)
    (retained : name ∈ (entry caller destination handle pattern body).support) :
    FreshFor name (ready caller destination handle pattern body).bindings := by
  apply PresenceGuardSource.fresh_append_closed
  · exact fresh
  · intro same
    apply freshName_not_mem (entry caller destination handle pattern body) 0
    change location caller destination handle pattern body ∈ (entry caller destination handle pattern body).support
    rw [← same]
    exact retained
  · exact LiteralQuerySource.handle_freeVars handle

theorem closed_reading (caller : Control) (destination : Atom) (handle : NamedSpaces.Handle) (pattern body : Atom)
    (before after : Environment) (code value : Atom)
    (beforeResolved : resolve caller.bindings = some before)
    (afterResolved : resolve (ready caller destination handle pattern body).bindings = some after)
    (reading : read before code = value) (closed : ∀ environment, read environment value = value) :
    read after code = value :=
  CapturedQueryOperands.resolved_forces beforeResolved code value reading closed after
    (ready_inherited caller destination handle pattern body after (resolve_sound afterResolved))

set_option maxHeartbeats 1200000 in
theorem preparation {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (caller : Control) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (destination : Atom) (handle : NamedSpaces.Handle) (pattern body : Atom)
    (consistent : ∃ environment, Solves environment caller.bindings) :
    (ScopedQuerySource.machine .relational program).run 3
      (placed allocator world scope parents (entry caller destination handle pattern body) context origins pending) =
      ([], .exhausted (placed allocator world scope parents
        (ready caller destination handle pattern body) context origins pending)) := by
  have refined := location_refined caller destination handle pattern body consistent
  simp only [ready, location, entry, source] at refined
  cases handle <;>
    simp [Machine.run, ScopedQuerySource.machine, ScopedQuerySource.step, ScopedQuerySource.syntaxStep,
      ScopedQuerySource.constrainedCall, ScopedQuerySource.mutationCall, ScopedQuerySource.queryStep,
      placed, entry, source, scopeStep, enterCollapse?, enterSuperpose?, EagerDFS.Destination.machine,
      prepare, replace, installChild, retainChild, callable, StdLib.known, Eval.ioHead,
      callArguments, freshSlots, List.range_succ, Eval.argumentIsRaw, StdLib.rawArgument,
      ready, location, Effects.handleValue] at refined ⊢ <;> simp [refined]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedMatchPreparation
