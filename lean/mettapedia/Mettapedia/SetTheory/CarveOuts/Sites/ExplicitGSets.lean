import Mettapedia.SetTheory.CarveOuts.Sites.GSets
import Mettapedia.GSLT.Core.NonFactorization

/-!
# A choice-free witness that forgetting the action loses the isomorphism

Two actions of the two-element group on `Bool` have the same carrier. One flips the value and
one fixes it. An equivalence of actions is a bijection written out here, required to commute
with the action; the identity equivalence is the identity function. The flipping action is
equivalent to itself, and the fixing action is not equivalent to it.

The same separation, stated with the identity isomorphism of the category of actions, uses
`Classical.choice`. That isomorphism is the identity arrow together with the left and right
unit laws of the category, and those laws are not written out for the category of actions.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.CarveOuts.Sites

open Mettapedia.GSLT.Core.NonFactorization

/-- A monoid action on a carrier. -/
structure ExplicitGSet (G : Type) [Monoid G] where
  /-- The underlying carrier. -/
  carrier : Type
  /-- The action. -/
  act : G → carrier → carrier
  /-- The unit acts as the identity. -/
  one_act : ∀ x, act 1 x = x
  /-- The action respects multiplication. -/
  mul_act : ∀ a b x, act (a * b) x = act a (act b x)

/-- A bijection of carriers that commutes with the two actions. -/
structure ExplicitIso {G : Type} [Monoid G] (X Y : ExplicitGSet G) where
  /-- The forward map. -/
  toFun : X.carrier → Y.carrier
  /-- The inverse map. -/
  invFun : Y.carrier → X.carrier
  /-- The inverse is a left inverse. -/
  left_inv : ∀ x, invFun (toFun x) = x
  /-- The inverse is a right inverse. -/
  right_inv : ∀ y, toFun (invFun y) = y
  /-- The bijection commutes with the action. -/
  comm : ∀ g x, toFun (X.act g x) = Y.act g (toFun x)

/-- The identity equivalence. -/
def ExplicitIso.refl {G : Type} [Monoid G] (X : ExplicitGSet G) : ExplicitIso X X where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  comm _ _ := rfl

/-- The two-element group acting on `Bool` by negation. -/
def swapAction : ExplicitGSet Flip where
  carrier := Bool
  act g b := match g with
    | .keep => b
    | .flip => !b
  one_act _ := rfl
  mul_act a b x := by cases a <;> cases b <;> cases x <;> rfl

/-- The two-element group acting trivially on `Bool`. -/
def trivialAction : ExplicitGSet Flip where
  carrier := Bool
  act _ b := b
  one_act _ := rfl
  mul_act _ _ _ := rfl

/-- **The two actions have the same carrier.** -/
theorem explicit_carriers_eq : swapAction.carrier = trivialAction.carrier :=
  rfl

/-- **The trivial action is not equivalent to the swapping action.** An equivalence would fix
a value that the swap moves. -/
theorem no_explicitIso_trivial_swap (e : ExplicitIso trivialAction swapAction) : False := by
  have moved := e.comm Flip.flip true
  change e.toFun true = !(e.toFun true) at moved
  cases h : e.toFun true with
  | false =>
      rw [h] at moved
      exact Bool.false_ne_true moved
  | true =>
      rw [h] at moved
      exact Bool.false_ne_true moved.symm

/-- **Forgetting the carrier's action loses the isomorphism.** The two actions read as the
same carrier; only the swapping action is equivalent to itself through the identity
equivalence. -/
def explicitFiber :
    NonTrivialFiber (fun X : ExplicitGSet Flip => X.carrier)
      (fun X => Nonempty (ExplicitIso X swapAction)) :=
  NonTrivialFiber.ofProp explicit_carriers_eq
    ⟨ExplicitIso.refl swapAction⟩
    (fun ⟨e⟩ => no_explicitIso_trivial_swap e)

end Mettapedia.SetTheory.CarveOuts.Sites
