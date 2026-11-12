import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource

/-!
# Relabeling opaque Destination execution contexts

Contexts accompany executable controls and saved collection callers; they do
not replace logical environments or source terms. This map changes only that
opaque payload. Controls, output packets, world effects, allocation supplies
and occurrence coordinates retain their existing owners.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationContextMap

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination

variable {A B C : Type}

def work (map : A → B) (item : CollectionWork A) : CollectionWork B :=
  (item.1, map item.2.1, item.2.2)

def caller (map : A → B) (saved : CollectionCaller A) : CollectionCaller B :=
  (saved.1, saved.2.1, map saved.2.2.1, saved.2.2.2)

def scope (map : A → B) (original : CollectionScope A) : CollectionScope B :=
  ⟨original.frontier.map (work map), original.collected, original.caller.map (caller map)⟩

def configuration (map : A → B) (original : CollectionConfiguration A) : CollectionConfiguration B :=
  ⟨original.world, original.scopes.map (scope map)⟩

def state (map : A → B) (original : ScopedCursor A) : ScopedCursor B :=
  (original.1, configuration map original.2)

def cursor (map : A → B) (original : Cursor A) : Cursor B :=
  ⟨original.world, original.control, map original.context⟩

theorem configuration_world (map : A → B) (original : CollectionConfiguration A) :
    (configuration map original).world = original.world := rfl

def localAction (map : A → B) :
    Transition (Cursor A) Empty (Result × Cursor A) Boundary →
    Transition (Cursor B) Empty (Result × Cursor B) Boundary
  | .silent next => .silent (cursor map next)
  | .publish events next => .publish events (cursor map next)
  | .finish (result, final) => .finish (result, cursor map final)
  | .call request retained => .call request (cursor map retained)
  | .fail events => .fail events

def action (map : A → B) : ScopedQuerySource.Action A → ScopedQuerySource.Action B
  | .silent next => .silent (state map next)
  | .publish events next => .publish events (state map next)
  | .finish final => .finish (state map final)
  | .call request retained => .call request (state map retained)
  | .fail events => .fail events

theorem work_comp (first : A → B) (second : B → C) (item : CollectionWork A) :
    work second (work first item) = work (second ∘ first) item := rfl

theorem caller_comp (first : A → B) (second : B → C) (saved : CollectionCaller A) :
    caller second (caller first saved) = caller (second ∘ first) saved := rfl

theorem scope_comp (first : A → B) (second : B → C) (original : CollectionScope A) :
    scope second (scope first original) = scope (second ∘ first) original := by
  simp only [scope, List.map_map, Option.map_map, Function.comp_def, work_comp, caller_comp]

theorem scope_support (map : A → B) (original : CollectionScope A) :
    CollectionScope.support (scope map original) = CollectionScope.support original := by
  simp only [CollectionScope.support, scope, List.foldr_map]
  congr 1
  cases original.caller <;> rfl

theorem configuration_support (map : A → B) (original : CollectionConfiguration A) :
    collectionSupport (configuration map original) = collectionSupport original := by
  simp only [collectionSupport, configuration, List.foldr_map]
  congr 1
  funext original accumulated
  rw [scope_support]

theorem state_world (map : A → B) (original : ScopedCursor A) :
    (state map original).1 = original.1 ∧ (state map original).2.world = original.2.world := ⟨rfl, rfl⟩

theorem scope_record (map : A → B) (original : CollectionScope A)
    (pending : List (CollectionWork A)) (answer : CollectedAnswer) :
    scope map (EagerDFS.Scope.record original pending answer) =
      EagerDFS.Scope.record (scope map original) (pending.map (work map)) answer := rfl

theorem retain_child (map : A → B) (original : CollectionScope A)
    (pending : List (CollectionWork A)) (origins : List Nat) (reached : Cursor A) :
    scope map (retainChild original pending origins reached) =
      retainChild (scope map original) (pending.map (work map)) origins (cursor map reached) := rfl

theorem primitive_work (map : A → B) (control : Control) (context : A) (origins : List Nat)
    (destination : Atom) (older : List Goal) (values : List Atom) :
    primitiveWork control (map context) origins destination older values =
      (primitiveWork control context origins destination older values).map (work map) := by
  simp [primitiveWork, List.map_map, work]

theorem equation_work (map : A → B) (program : SpaceSemantics.Program) (control : Control)
    (boundary : Finset String) (context : A) (origins : List Nat) (head : String)
    (arguments : List Atom) (destination : Atom) (older : List Goal) (retained : Nat) :
    equationWork program control boundary (map context) origins head arguments destination older retained =
      (equationWork program control boundary context origins head arguments destination older retained).map (work map) := by
  simp [equationWork, List.map_map, work]

theorem allocated_work (map : A → B) (copies : List (MetavariableFrameStore.Shared.Token × (Atom × List Atom)))
    (saved : CollectionCaller A) :
    allocatedWork copies (caller map saved) = work map (allocatedWork copies saved) := rfl

/-- Every actual local branch operation commutes, including print effects,
failure, open requests and terminal binding records. -/
theorem local_step (map : A → B) (policy : Policy) (program : SpaceSemantics.Program) (source : Cursor A) :
    (EagerDFS.Destination.machine policy program).step (cursor map source) =
      ((EagerDFS.Destination.machine policy program).step source).map (localAction map) := by
  simp only [EagerDFS.Destination.machine, cursor]
  repeat' first
    | rfl
    | (split <;> try simp_all only [localAction, cursor, Option.map_some])

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationContextMap
