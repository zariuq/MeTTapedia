import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodySourceEmbedding

/-!
# Owned and inherited typed-call contexts in the same host state

The local context separates calls owned by a region from its inherited caller
context. Flattening concatenates those call lists. The complete host scope
stack, controls, alternatives, cut coordinates and collected packets remain
present throughout; only the opaque context representation changes.

Inherited frames contribute their operands to local protection. When such a
frame becomes active, the local region must hand off rather than publish an
answer or ignore the caller's typed protocol.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedContext

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay

abbrev LocalState (User : Type) := State (Context User)

def flatten {User : Type} (inside : Context (Context User)) : Context User :=
  ⟨inside.user.user, inside.calls ++ inside.user.calls⟩

def inherit {User : Type} (outside : Context User) : Context (Context User) :=
  ⟨outside, []⟩

def work {User : Type} := Bridges.DestinationContextMap.work (@flatten User)
def scope {User : Type} := Bridges.DestinationContextMap.scope (@flatten User)
def state {User : Type} := Bridges.DestinationContextMap.state (@flatten User)
def nest {User : Type} := Bridges.DestinationContextMap.state (@inherit User)

def services {User : Type} (original : Services User) : Services (Context User) where
  rows world inherited := original.rows world inherited.user
  declarations := original.declarations
  kind := original.kind
  userSupport := contextSupport original
  orderedGuard := original.orderedGuard
  guard_exact := original.guard_exact

def action {User Request : Type} :
    Transition (LocalState User) CollectedAnswer (LocalState User) Request →
    Transition (State User) CollectedAnswer (State User) Request
  | .silent next => .silent (state next)
  | .publish events next => .publish events (state next)
  | .finish final => .finish (state final)
  | .call request retained => .call request (state retained)
  | .fail events => .fail events

def outcome {User Request : Type} :
    Outcome (LocalState User) (LocalState User) Request →
    Outcome (State User) (State User) Request
  | .finished final => .finished (state final)
  | .suspended request retained => .suspended request (state retained)
  | .stuck retained => .stuck (state retained)
  | .exhausted retained => .exhausted (state retained)
  | .faulted => .faulted

theorem flatten_inherit {User : Type} (outside : Context User) :
    flatten (inherit outside) = outside := by cases outside; rfl

theorem empty_owned_is_original {User : Type} (inside : Context (Context User))
    (empty : inside.calls = []) : flatten inside = inside.user := by
  cases inside
  simp_all [flatten]

theorem state_world {User : Type} (source : LocalState User) :
    (state source).1 = source.1 ∧ (state source).2.world = source.2.world := ⟨rfl, rfl⟩

theorem state_depth {User : Type} (source : LocalState User) :
    (state source).2.scopes.length = source.2.scopes.length := by
  simp [state, Bridges.DestinationContextMap.state, Bridges.DestinationContextMap.configuration]

theorem state_support {User : Type} (source : LocalState User) :
    collectionSupport (state source).2 = collectionSupport source.2 :=
  Bridges.DestinationContextMap.configuration_support flatten source.2

theorem context_support {User : Type} (original : Services User) (inside : Context (Context User)) :
    contextSupport original (flatten inside) = contextSupport (services original) inside := by
  simp only [contextSupport, flatten, services, List.flatMap_append,
    PettaBodyFrameEmbedding.operand_support_append]
  ac_rfl

theorem protect_commutes {User : Type} (original : Services User) (source : LocalState User)
    (control : DControl) (inside : Context (Context User)) :
    protect original (state source) control (flatten inside) =
      protect (services original) source control inside := by
  simp only [protect, state_support, context_support]

theorem install_commutes {User : Type} (source : LocalState User) (current : Scope (Context User))
    (parents : List (Scope (Context User))) (generated pending : List (Work (Context User))) :
    install (state source) (scope current) (parents.map scope)
      (generated.map work) (pending.map work) = state (install source current parents generated pending) := by
  simp [install, state, scope, work, Bridges.DestinationContextMap.state,
    Bridges.DestinationContextMap.configuration, Bridges.DestinationContextMap.scope, List.map_append]

theorem source_action {User : Type}
    (reply : Bridges.ScopedQuerySource.Action (Context (Context User))) :
    liftSource (Bridges.DestinationContextMap.action flatten reply) = action (liftSource reply) := by
  cases reply <;> rfl

theorem source_owned {User : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (source : LocalState User) :
    liftSource (Bridges.ScopedQuerySource.ownedStep policy program (state source)) =
      action (liftSource (Bridges.ScopedQuerySource.ownedStep policy program source)) := by
  rw [state, Bridges.DestinationContextMap.owned_step, source_action]

theorem state_nest {User : Type} (source : State User) : state (nest source) = source := by
  rcases source with ⟨allocator, world, scopes⟩
  change ((allocator, ⟨world, _⟩) : State User) = ((allocator, ⟨world, scopes⟩) : State User)
  congr 2
  induction scopes with
  | nil => rfl
  | cons current parents ih =>
      simp only [nest, Bridges.DestinationContextMap.state,
        Bridges.DestinationContextMap.configuration, List.map_cons]
      congr 1
      cases current with
      | mk frontier collected caller =>
          simp only [Bridges.DestinationContextMap.scope, Bridges.DestinationContextMap.work,
            Bridges.DestinationContextMap.caller, List.map_map, Option.map_map, Function.comp_def,
            flatten_inherit, Prod.mk.eta, List.map_id_fun', Option.map_id_fun', id_eq]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedContext
