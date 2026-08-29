import Mettapedia.TypeTheory.ScopedIdentity

/-!
# Unity does not entail uniqueness of identity proofs

Two canaries separating three notions that are easily run together:

* `refl` gives a route from every object to itself;
* J-style structure (composition and inversion of routes) is available;
* K/UIP says every self-route equals `refl`.

A *connected* whole — one object, every route composable and invertible — can
still have a nontrivial self-route.  The one-object groupoid with the
two-element group as its routes is the smallest witness: it is as unified as a
layer can be, and K fails in it.  Conversely, the terminal layer (one object,
one route) satisfies K vacuously.  So "unity" fixes neither answer; only the
route structure does.
-/

namespace Mettapedia.TypeTheory.UnityIsNotUIP

open Mettapedia.TypeTheory.ScopedIdentity

/-- One object; routes are the two-element group `Bool` under xor. -/
def twoLoop : Layer Unit where
  Route := fun _ _ => Bool
  refl := fun _ => false
  Support := fun _ _ => True
  forget := fun _ => trivial

/-- Routes compose (xor) and invert (every element is its own inverse): the
J-style groupoid structure is present. -/
def twoLoop.comp : Bool → Bool → Bool := xor
theorem twoLoop.comp_refl (r : Bool) : twoLoop.comp r false = r := by
  cases r <;> rfl
theorem twoLoop.inverse (r : Bool) : twoLoop.comp r r = false := by
  cases r <;> rfl

/-- The whole is connected: there is a route between any two objects. -/
theorem twoLoop_connected (a b : Unit) : Nonempty (twoLoop.Route a b) :=
  ⟨false⟩

/-- Yet it has a nontrivial self-route, so uniqueness of identity proofs fails. -/
theorem twoLoop_hasDistinctRoutes : HasDistinctRoutes twoLoop :=
  ⟨(), (), (false : Bool), (true : Bool), Bool.false_ne_true⟩

theorem twoLoop_not_routeUIP : ¬ RouteUIP twoLoop :=
  fun uip => routeUIP_excludes_distinctRoutes uip twoLoop_hasDistinctRoutes

/-- The terminal layer: one object, exactly one route. -/
def terminal : Layer Unit where
  Route := fun _ _ => Unit
  refl := fun _ => ()
  Support := fun _ _ => True
  forget := fun _ => trivial

/-- Here uniqueness of identity proofs holds, vacuously. -/
theorem terminal_routeUIP : RouteUIP terminal :=
  fun _ _ => ⟨fun r s => by cases r; cases s; rfl⟩

/-- Both layers are connected on one object; they differ only in route
structure.  Unity is therefore not what decides K. -/
theorem connectedness_does_not_decide_uip :
    (∀ a b : Unit, Nonempty (twoLoop.Route a b)) ∧
      (∀ a b : Unit, Nonempty (terminal.Route a b)) ∧
      ¬ RouteUIP twoLoop ∧ RouteUIP terminal :=
  ⟨twoLoop_connected, fun _ _ => ⟨()⟩, twoLoop_not_routeUIP, terminal_routeUIP⟩

#print axioms twoLoop_not_routeUIP
#print axioms terminal_routeUIP
#print axioms connectedness_does_not_decide_uip

end Mettapedia.TypeTheory.UnityIsNotUIP
