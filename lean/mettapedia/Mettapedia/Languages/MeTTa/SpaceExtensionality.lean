import Mettapedia.Languages.MeTTa.EmptinessTaxonomy
import Mettapedia.GSLT.Core.NonFactorization

/-!
# Spaces: when equal content means interchangeable, and when it cannot

Two intuitions about spaces are both natural and jointly impossible:

* *"Two spaces holding the same atoms are interchangeable — only the name
  differs."*
* *"Modifying one must not modify the other."*

The second is what makes distinct references worth having.  The first is what
would make them extensional.  This module proves they cannot both hold, and
identifies exactly what forces the choice.

The result is stronger than "addressability breaks extensionality".  Two
independent features each break it on their own:

* **Locality of update** (`locality_forces_intensionality`) — if writing
  through one reference leaves the other alone, then a context that writes
  through one and reads the other separates them.  This needs no address
  comparison, no `@`, and no special primitive: it follows from update being
  local and effective, which is the whole point of having two references.
* **Address comparison** (`addressFiber`) — comparing references separates
  them with no update at all, so the distinction becomes visible even in a
  read-only fragment.

And the positive side is real and worth stating: in the fragment with
*neither* — read-only, address-blind — content does determine everything
(`readOnly_observations_agree`).  That fragment is where structure sharing,
hash-consing and deduplicating identical spaces are sound, and the theorem is
the licence for exactly those optimizations.  Adding either feature revokes
the licence, and copy-on-write is what restores it.

The forcing theorem is stated over abstract update laws, not over the
particular update defined here, so it applies to any store satisfying them.
-/

namespace Mettapedia.Languages.MeTTa.SpaceExtensionality

open Mettapedia.Languages.MeTTa.Emptiness
open Mettapedia.GSLT.Core.NonFactorization

/-! ## Spaces, references, and a store -/

/-- A reference names a space.  Its identity is not its content. -/
abbrev SpaceRef := Nat

/-- What a space holds.  The content model is deliberately crude; nothing
below depends on it. -/
abbrev Content := List Datum

/-- A store assigns content to every reference. -/
abbrev Store := SpaceRef → Content

/-- The empty store. -/
def emptyStore : Store := fun _ => []

/-- Adding an atom through a reference changes that reference only. -/
def addAtom (store : Store) (ref : SpaceRef) (atom : Datum) : Store :=
  fun other => if other = ref then atom :: store other else store other

/-! ## The read-only, address-blind fragment is extensional

Here content really does determine everything, because an observer in this
fragment has nothing else to look at. -/

/-- **Equal content is interchangeable when only content is observable.**
Every read-only, address-blind observation is by construction a function of
the content, so two references holding the same atoms cannot be told apart.
This is the licence for sharing structure between equal spaces. -/
theorem readOnly_observations_agree {View : Type} (observer : Content → View)
    {store : Store} {left right : SpaceRef} (sameContent : store left = store right) :
    observer (store left) = observer (store right) := by
  rw [sameContent]

/-! ## Update alone destroys it

No addressability is used here.  Only the two properties that make separate
references worth having: writing through one is *effective*, and it is
*local*. -/

/-- Writing through a reference changes what that reference holds. -/
def UpdateEffective (update : Store → SpaceRef → Datum → Store) : Prop :=
  ∀ store ref atom, update store ref atom ref ≠ store ref

/-- Writing through a reference leaves the others alone. -/
def UpdateLocal (update : Store → SpaceRef → Datum → Store) : Prop :=
  ∀ store ref other atom, other ≠ ref → update store ref atom other = store other

theorem addAtom_effective : UpdateEffective addAtom := by
  intro store ref atom
  simp [addAtom]

theorem addAtom_local : UpdateLocal addAtom := by
  intro store ref other atom different
  simp [addAtom, different]

/-- **Locality forces intensionality.**  Given any update that is effective
and local, two distinct references with identical content are separated by
the context "write through the hole, then read a fixed reference".

So the two intuitions really are incompatible: *if* modifying one space does
not modify the other, *then* equal content does not make them
interchangeable.  Only one of the two may be kept, and keeping locality is
the point of having references at all. -/
theorem locality_forces_intensionality
    {update : Store → SpaceRef → Datum → Store}
    (effective : UpdateEffective update) (local' : UpdateLocal update) :
    ∃ (store : Store) (left right : SpaceRef),
      store left = store right ∧
        update store left .unit left ≠ update store right .unit left := by
  refine ⟨emptyStore, 0, 1, rfl, ?_⟩
  rw [local' emptyStore 1 0 .unit (by decide)]
  exact effective emptyStore 0 .unit

/-- The same, as a fibre of the content projection: the write-then-read
behaviour is not a function of what the references hold. -/
def mutationFiber :
    NonTrivialFiber (fun ref : SpaceRef => emptyStore ref)
      (fun ref : SpaceRef => addAtom emptyStore ref .unit 0) where
  left := 0
  right := 1
  sameShadow := rfl
  differentValue := by decide

/-- **Content does not determine behaviour once updates exist.** -/
theorem content_not_determines_behavior_under_update :
    ¬ Factors (fun ref : SpaceRef => emptyStore ref)
      (fun ref : SpaceRef => addAtom emptyStore ref .unit 0) :=
  mutationFiber.not_factors

/-! ## Address comparison destroys it too, and without any update

The second, independent route.  Once references can be compared, the
distinction is visible in the read-only fragment as well. -/

/-- Comparing a reference against a fixed one. -/
def addressTest (ref : SpaceRef) : Bool := decide (ref = 0)

/-- Two references with the same content and different addresses. -/
def addressFiber :
    NonTrivialFiber (fun ref : SpaceRef => emptyStore ref) addressTest where
  left := 0
  right := 1
  sameShadow := rfl
  differentValue := by decide

/-- **Content does not determine behaviour once addresses are comparable** —
even with no update in the language at all. -/
theorem content_not_determines_behavior_under_address_comparison :
    ¬ Factors (fun ref : SpaceRef => emptyStore ref) addressTest :=
  addressFiber.not_factors

/-! ## The dichotomy

Collecting it.  Extensional spaces are available exactly in the fragment with
neither local update nor address comparison; each feature alone revokes it,
and no combination restores it. -/

/-- **The choice, stated once.**  Either the language keeps both features and
spaces are intensional, or it gives up both and spaces may be shared freely.
There is no arrangement in which references are separately updatable, or
comparable, *and* equal content makes them interchangeable. -/
theorem extensionality_dichotomy :
    (∀ (View : Type) (observer : Content → View) (store : Store)
        (left right : SpaceRef), store left = store right →
        observer (store left) = observer (store right)) ∧
      ¬ Factors (fun ref : SpaceRef => emptyStore ref)
          (fun ref : SpaceRef => addAtom emptyStore ref .unit 0) ∧
      ¬ Factors (fun ref : SpaceRef => emptyStore ref) addressTest :=
  ⟨fun _ observer _ _ _ sameContent =>
      readOnly_observations_agree observer sameContent,
    content_not_determines_behavior_under_update,
    content_not_determines_behavior_under_address_comparison⟩

end Mettapedia.Languages.MeTTa.SpaceExtensionality
