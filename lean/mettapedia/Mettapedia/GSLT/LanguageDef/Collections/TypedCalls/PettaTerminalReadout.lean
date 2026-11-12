import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceOverlay

/-!
# Typed terminals consume a checked readout, not a chosen solver presentation

The local read certificate refers to the actual reached equations and
destination. Resolution failure cannot supply such a certificate. Neither
the world, pending alternatives nor guard replies are replaced.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTerminalReadout

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open PettaOccurrenceOverlay

theorem argument {User : Type} (services : Services User) (policy : Policy)
    (program : SpaceSemantics.Program) (source : State User)
    (scope : Scope User) (parents : List (Scope User)) (branchControl : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (formal : Ty String) (slot value : Atom)
    (scopes : source.2.scopes = scope :: parents)
    (frontier : scope.frontier = (branchControl, context, origins) :: pending)
    (calls : context.calls = frame :: outside)
    (depth : frame.scopeDepth = source.2.scopes.length)
    (phase : frame.phase = .argument formal slot) (terminal : branchControl.goals = [])
    (observed : (resolve branchControl.bindings).map
      (fun environment => read environment branchControl.destination) = some value) :
    step services policy program source =
      consumeArgument services source scope parents branchControl context origins pending
        frame outside formal slot value := by
  obtain ⟨environment, resolved, readback⟩ := Option.map_eq_some_iff.mp observed
  have actualDepth : frame.scopeDepth = (scope :: parents).length := by simpa only [scopes] using depth
  simp only [step, scopes, frontier, calls, if_pos actualDepth, phase, terminal,
    List.isEmpty_nil, ↓reduceIte, resolved, readback]

theorem body {User : Type} (services : Services User) (policy : Policy)
    (program : SpaceSemantics.Program) (source : State User)
    (scope : Scope User) (parents : List (Scope User)) (branchControl : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (value : Atom)
    (scopes : source.2.scopes = scope :: parents)
    (frontier : scope.frontier = (branchControl, context, origins) :: pending)
    (calls : context.calls = frame :: outside)
    (depth : frame.scopeDepth = source.2.scopes.length)
    (phase : frame.phase = .body) (terminal : branchControl.goals = [])
    (observed : (resolve branchControl.bindings).map
      (fun environment => read environment branchControl.destination) = some value) :
    step services policy program source =
      consumeBody services source scope parents branchControl context origins pending frame outside value := by
  obtain ⟨environment, resolved, readback⟩ := Option.map_eq_some_iff.mp observed
  have delivered := terminal_body_step services policy program source scope parents branchControl context origins
    pending frame outside environment scopes frontier calls depth phase terminal resolved
  simpa only [readback] using delivered

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTerminalReadout
