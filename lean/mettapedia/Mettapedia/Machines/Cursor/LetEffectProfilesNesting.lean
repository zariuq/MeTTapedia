import Mettapedia.Machines.Cursor.LetEffectProfiles

/-!
# Open child publication and a closed shared preparation

An open child publishes its own admitted step before the parent continues.
A refused parent has no parent receipt, but cannot undo that earlier child
publication. In the closed profile, child and parent share one private effect
buffer; refusal discards it and only the outer publication can be public.

These are different nesting disciplines. The closed composition propagates
child refusal/error; it does not introduce a recoverable savepoint semantics.
The open composition requests recording so that the two receipt scopes are
observable. Neither definition chooses the language's default discipline.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.LetEffectProfilesNesting

open LetEffectProfiles

variable {Key Value Event Child Parent Error : Type} [DecidableEq Key]

def bindSuccess (child : Code Key Value Event Child Error)
    (parent : Child → Code Key Value Event Parent Error) : Code Key Value Event Parent Error :=
  ReadOnlyQuery.bind child fun outcome =>
    match outcome with
    | .answer value => parent value
    | .refused => .pure .refused
    | .error reason => .pure (.error reason)

structure Nested (Key Value Event Child Parent Error : Type) where
  childResult : Result Child Error
  parentResult : Result Parent Error
  world : World Key Value Event
  childPublished : Bool
  parentPublished : Bool
  childReceipt : Option (Receipt Key Value Event Child)
  parentReceipt : Option (Receipt Key Value Event Parent)

def openNested (policy : ReadPolicy) (childAllowed parentAllowed : Bool)
    (child : Code Key Value Event Child Error) (parent : Child → Code Key Value Event Parent Error)
    (world : World Key Value Event) : Nested Key Value Event Child Parent Error :=
  let childPublished := publish true childAllowed world (prepared policy child world)
  match childPublished.result with
  | .answer value =>
      let parentPublished := publish true parentAllowed childPublished.world
        (prepared policy (parent value) childPublished.world)
      ⟨childPublished.result, parentPublished.result, parentPublished.world,
        childPublished.published, parentPublished.published, childPublished.receipt, parentPublished.receipt⟩
  | .refused =>
      ⟨.refused, .refused, childPublished.world, childPublished.published, false,
        childPublished.receipt, none⟩
  | .error reason =>
      ⟨.error reason, .error reason, childPublished.world, childPublished.published, false,
        childPublished.receipt, none⟩

/-- This is one shared preparation: no child base receipt is minted while
its effects remain speculative. Successful child output is passed directly
to the parent continuation, without re-evaluating the child. -/
def closedNested (policy : ReadPolicy) (allowed : Bool)
    (child : Code Key Value Event Child Error) (parent : Child → Code Key Value Event Parent Error)
    (world : World Key Value Event) : Publication Key Value Event Parent Error :=
  publish true allowed world (prepared policy (bindSuccess child parent) world)

theorem closed_refusal (policy : ReadPolicy) (allowed : Bool)
    (child : Code Key Value Event Child Error) (parent : Child → Code Key Value Event Parent Error)
    (world : World Key Value Event)
    (refused : (prepared policy (bindSuccess child parent) world).answer = .refused) :
    (closedNested policy allowed child parent world).world = world ∧
      (closedNested policy allowed child parent world).receipt = none ∧
      (closedNested policy allowed child parent world).published = false := by
  simp [closedNested, publish, refused]

/-- A parent admission refusal leaves the already admitted child's world and
receipt intact. No parent receipt is fabricated for that refused step. -/
theorem open_parent_refusal_keeps_child (policy : ReadPolicy)
    (child : Code Key Value Event Child Error) (parent : Child → Code Key Value Event Parent Error)
    (world : World Key Value Event) (value : Child)
    (answered : (prepared policy child world).answer = .answer value) :
    let preparedChild := prepared policy child world
    let childWorld := applyAll preparedChild.state.pendingRev.reverse world
    let result := openNested policy true false child parent world
    result.world = childWorld ∧ result.childPublished = true ∧ result.parentPublished = false ∧
      result.childReceipt = some ⟨value, preparedChild.state.pendingRev.reverse⟩ ∧
      result.parentReceipt = none := by
  simp only [openNested, publish, answered, ↓reduceIte]
  cases parentAnswer : (prepared policy (parent value)
      (applyAll (prepared policy child world).state.pendingRev.reverse world)).answer <;>
    simp

/-- Sharing the preparation is actual state threading through the existing
query bind. It is not a second evaluation on the original pre-state. -/
theorem closed_threads_child_payload (policy : ReadPolicy)
    (child : Code Key Value Event Child Error) (parent : Child → Code Key Value Event Parent Error)
    (world : World Key Value Event) (value : Child)
    (answered : (prepared policy child world).answer = .answer value) :
    prepared policy (bindSuccess child parent) world =
      let first := prepared policy child world
      let second := QueryState.run (preparedService policy) (parent value) first.state
      ⟨second.answer, second.state, first.reads ++ second.reads⟩ := by
  rw [prepared, bindSuccess, QueryState.run_bind]
  simp only [prepared] at answered ⊢
  rw [answered]

end Mettapedia.Machines.Cursor.LetEffectProfilesNesting
