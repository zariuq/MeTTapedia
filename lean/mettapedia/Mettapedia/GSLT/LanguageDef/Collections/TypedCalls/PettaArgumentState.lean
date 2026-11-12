import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaArgumentProgress
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaContextFacts

/-!
# Argument progress in active work and saved collection callers

The existing binding-contract transport carries the argument predicate on the
complete context. It is independent of logical bindings, so the actual source
owner preserves it through every source handler. Typed operations still have
to prove their own updates to that context.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaArgumentProgress

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay

def predicate (User : Type) : RefinementTransport.BindingPredicate (Context User) :=
  PettaContextFacts.predicate (@Calls User)

def Safe {User : Type} (source : State User) : Prop :=
  PettaContextFacts.Safe (@Calls User) source

def Keeps {User : Type} (reply : Step User) : Prop :=
  PettaContextFacts.Keeps (@Calls User) reply

theorem silent_keeps {User : Type} (source : State User) (good : Safe source) : Keeps (.silent source) := by
  exact PettaContextFacts.silent_keeps source good

theorem call_keeps {User : Type} (source : State User) (request : Request) (good : Safe source) :
    Keeps (.call request source) := by
  exact PettaContextFacts.call_keeps source request good

theorem source_keeps {User : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (source : State User) (good : Safe source) :
    Keeps (liftSource (Bridges.ScopedQuerySource.ownedStep policy program source)) := by
  exact PettaContextFacts.source_keeps (@Calls User) policy program source good

theorem active_calls {User : Type} (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (good : Safe source) (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending) : Calls context :=
  PettaContextFacts.active source current parents control context origins pending good scopes frontier

theorem active_frame {User : Type} (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (good : Safe source)
    (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = frame :: outside) : Aligned frame :=
  active_calls source current parents control context origins pending good scopes frontier frame
    (calls ▸ List.mem_cons_self)

theorem install_keeps {User : Type} (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending generated : List (Work User))
    (good : Safe source) (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (produced : Calls context → ∀ item ∈ generated, Calls item.2.1) :
    Safe (install source current parents generated pending) := by
  exact PettaContextFacts.install_keeps source current parents control context origins pending generated good scopes frontier produced

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaArgumentProgress
