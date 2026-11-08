import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceOverlay
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryBinding

/-!
# Source-owned publication under the typed occurrence overlay

The overlay never invents a body result. This module derives every published
packet from the actual Destination source terminal and its solved equations.
It does not identify this source profile with the native PeTTa evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceOverlay

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.GSLT.Distinction.ProductiveBlocks

theorem liftSource_published {User : Type}
    {original : Transition (State User) EagerDFS.Destination.CollectedAnswer (State User)
      EagerDFS.Destination.ScopeBoundary}
    {events : List EagerDFS.Destination.CollectedAnswer} {after : State User}
    (published : liftSource original = .publish events after) : original = .publish events after := by
  cases original <;> simp_all [liftSource]

theorem surface_published_is_source {User : Type}
    (policy : EagerDFS.Destination.Policy) (program : SpaceSemantics.Program)
    (source after : State User) (events : List EagerDFS.Destination.CollectedAnswer)
    (published : liftSource (Bridges.ScopedQuerySource.ownedStep policy program source) =
      .publish events after) :
    EagerDFS.Destination.scopeStep policy program source = .publish events after :=
  Bridges.ScopedQueryBinding.owned_publication_is_raw policy program source after events
    (liftSource_published published)

theorem enterRows_ne_publish {User : Type} (services : Services User) (source : State User)
    (scope : Scope User) (parents : List (Scope User)) (control : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (events : List EagerDFS.Destination.CollectedAnswer) (after : State User) :
    enterRows services source scope parents control context origins pending head arguments destination older ≠
      .publish events after := by
  unfold enterRows
  split <;> try simp
  split <;> simp

theorem nextArgument_ne_publish {User : Type} (services : Services User) (source : State User)
    (scope : Scope User) (parents : List (Scope User)) (control : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame)
    (events : List EagerDFS.Destination.CollectedAnswer) (after : State User) :
    nextArgument services source scope parents control context origins pending frame outside ≠
      .publish events after := by
  unfold nextArgument
  split <;> try simp
  split <;> simp

theorem consumeArgument_ne_publish {User : Type} (services : Services User) (source : State User)
    (scope : Scope User) (parents : List (Scope User)) (control : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (formal : Ty String) (slot value : Atom)
    (events : List EagerDFS.Destination.CollectedAnswer) (after : State User) :
    consumeArgument services source scope parents control context origins pending frame outside formal slot value ≠
      .publish events after := by
  unfold consumeArgument
  split <;> simp

theorem consumeBody_ne_publish {User : Type} (services : Services User) (source : State User)
    (scope : Scope User) (parents : List (Scope User)) (control : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (value : Atom)
    (events : List EagerDFS.Destination.CollectedAnswer) (after : State User) :
    consumeBody services source scope parents control context origins pending frame outside value ≠
      .publish events after := by
  unfold consumeBody
  split <;> simp

theorem delegate_published_is_source {User : Type} (services : Services User)
    (policy : EagerDFS.Destination.Policy) (program : SpaceSemantics.Program)
    (source : State User) (scope : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (events : List EagerDFS.Destination.CollectedAnswer) (after : State User)
    (published : delegate services policy program source scope parents control context origins pending =
      .publish events after) :
    EagerDFS.Destination.scopeStep policy program source = .publish events after := by
  unfold delegate at published
  split at published
  · split at published
    · split at published
      · exact surface_published_is_source _ _ _ _ _ published
      · exact False.elim (enterRows_ne_publish _ _ _ _ _ _ _ _ _ _ _ _ _ _ published)
    · exact surface_published_is_source _ _ _ _ _ published
  · exact surface_published_is_source _ _ _ _ _ published

theorem published_is_source {User : Type} (services : Services User)
    (policy : EagerDFS.Destination.Policy) (program : SpaceSemantics.Program)
    (source after : State User) (events : List EagerDFS.Destination.CollectedAnswer)
    (published : step services policy program source = .publish events after) :
    EagerDFS.Destination.scopeStep policy program source = .publish events after := by
  unfold step at published
  repeat' first
    | exact surface_published_is_source _ _ _ _ _ published
    | exact delegate_published_is_source _ _ _ _ _ _ _ _ _ _ _ _ published
    | exact False.elim (nextArgument_ne_publish _ _ _ _ _ _ _ _ _ _ _ _ published)
    | exact False.elim (consumeArgument_ne_publish _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ published)
    | exact False.elim (consumeBody_ne_publish _ _ _ _ _ _ _ _ _ _ _ _ _ published)
    | split at published
    | contradiction

/-- Every published packet has a real terminal source occurrence and a model
of that occurrence's actual equations. Guarding cannot manufacture a value or
replace a returned record with a captured caller record. -/
theorem published_source_model {User : Type} (services : Services User)
    (policy : EagerDFS.Destination.Policy) (program : SpaceSemantics.Program)
    (source after : State User) (events : List EagerDFS.Destination.CollectedAnswer)
    (published : step services policy program source = .publish events after) :
    ∃ value bindings origins environment,
      events = [⟨value, bindings, origins, []⟩] ∧
        EagerDFS.Destination.Solves environment bindings :=
  EagerDFS.Destination.scope_published_source_model policy program source after events
    (published_is_source services policy program source after events published)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceOverlay
