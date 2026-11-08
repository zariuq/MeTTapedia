import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceBinding
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryReturn

/-!
# Source variable delivery into the typed occurrence return guard

The body executes its real variable read and two-way return equation before
the guard sees a value. That guard is consumed at the saved call's scope depth,
with the reached term record, world and older producer alternatives retained.
This is a local source/typed continuation join. Compound return recognition
and the native mixed-record representation are further obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSurfaceReturn

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open PettaOccurrenceOverlay
open Bridges.ClosedOnceQueryFrame (placed)

theorem typed_variable_body_two_steps {User : Type} (services : Services User)
    (policy : Policy) (program : SpaceSemantics.Program) (allocator : Allocator) (world : World)
    (scope : Scope User) (parents : List (Scope User)) (caller : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (name : String) (bindings : Equations)
    (calls : context.calls = frame :: outside) (phase : frame.phase = .body)
    (depth : frame.scopeDepth = (scope :: parents).length)
    (accepted : refine caller.bindings (.var name) frame.callDestination = some bindings) :
    (PettaOccurrenceOverlay.machine services policy program).run 2
      (placed allocator world scope parents
        {caller with goals := [.evaluate (.var name) frame.callDestination], destination := frame.callDestination}
        context origins pending) =
      ([], .exhausted (placed allocator world scope parents
        {caller with bindings, goals := [], destination := frame.callDestination} context origins pending)) := by
  simp [Machine.run, PettaOccurrenceOverlay.machine, PettaOccurrenceOverlay.step,
    delegate, calls, phase, depth, liftSource,
    Bridges.ScopedQuerySource.ownedStep, Bridges.ScopedQuerySource.ownershipStep,
    Bridges.ScopedCaseSource.entryStep, Bridges.ScopedCaseSource.readyStep,
    Bridges.ScopedQuerySource.step, Bridges.ScopedQuerySource.syntaxStep,
    Bridges.ScopedQuerySource.constrainedCall, Bridges.ScopedQuerySource.mutationCall,
    Bridges.ScopedQuerySource.queryStep, placed, scopeStep, enterCollapse?, enterSuperpose?,
    EagerDFS.Destination.machine, prepare, replace, installChild, retainChild, accepted]

/-- The protected value is derived from the actual source refinement. The
next step is exactly the existing result-guard operation: missing service
retains this point, refusal drops this occurrence, and each accepted store
resumes the caller once. Nothing restarts the source body. -/
theorem source_variable_then_guard {User : Type} (services : Services User)
    (policy : Policy) (program : SpaceSemantics.Program) (allocator : Allocator) (world : World)
    (scope : Scope User) (parents : List (Scope User)) (caller : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (name : String) (value : Atom) (bindings : Equations)
    (calls : context.calls = frame :: outside) (phase : frame.phase = .body)
    (depth : frame.scopeDepth = (scope :: parents).length)
    (fixed : ProtectedSlots.Fixed caller.bindings (.var name) value)
    (accepted : refine caller.bindings (.var name) frame.callDestination = some bindings) :
    let reachedControl := {caller with bindings, goals := [], destination := frame.callDestination}
    let reached := placed allocator world scope parents reachedControl context origins pending
    (PettaOccurrenceOverlay.machine services policy program).run 2
      (placed allocator world scope parents
        {caller with goals := [.evaluate (.var name) frame.callDestination], destination := frame.callDestination}
        context origins pending) = ([], .exhausted reached) ∧
    PettaOccurrenceOverlay.step services policy program reached =
      consumeBody services reached {scope with frontier := (reachedControl, context, origins) :: pending}
        parents reachedControl context origins pending frame outside value := by
  dsimp only
  refine ⟨typed_variable_body_two_steps services policy program allocator world scope parents caller context origins
    pending frame outside name bindings calls phase depth accepted, ?_⟩
  have sourceReturn := (refinement_iff _ _ _ _).mpr accepted
  have output := Bridges.ScopedQueryReturn.refinement_fixes_destination fixed sourceReturn
  have consistent : ∃ environment, EagerDFS.Destination.Solves environment bindings := by
    cases sourceReturn with
    | accepted environment old same => exact ⟨environment, (solves_append_equation _ _ _ _).mpr ⟨old, same⟩⟩
  obtain ⟨environment, resolved⟩ := resolve_complete consistent
  have actual := terminal_body_step services policy program
    (placed allocator world scope parents
      {caller with bindings, goals := [], destination := frame.callDestination} context origins pending)
    {scope with frontier :=
      ({caller with bindings, goals := [], destination := frame.callDestination}, context, origins) :: pending}
    parents {caller with bindings, goals := [], destination := frame.callDestination}
    context origins pending frame outside environment rfl rfl calls (by simpa [placed] using depth) phase rfl resolved
  simpa only [output environment (resolve_sound resolved)] using actual

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSurfaceReturn
