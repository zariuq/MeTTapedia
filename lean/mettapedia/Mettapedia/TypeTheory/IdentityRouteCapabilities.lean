import Mettapedia.TypeTheory.ScopedIdentity

/-!
# Independent capabilities of proof-relevant identity routes

A reflexive route family, groupoid operations, uniqueness of routes, and
reflection of routes into endpoint equality are distinct structures.  This
module separates them and gives a constructive four-cell matrix for the two
most easily conflated properties:

* route UIP: at most one retained route between fixed endpoints;
* endpoint reflection: a retained route forces its endpoints to be equal.

Every cell also admits groupoid composition and inversion.  Consequently,
J-shaped route algebra alone chooses neither UIP nor equality reflection.
The final theorem identifies the exact price of forgetting routes into a
proposition: that erasure is injective precisely when route UIP holds.

These are criteria and countermodels, not a selection of an identity type,
K, univalence, or equality reflection for any object calculus.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IdentityRouteCapabilities

open Mettapedia.TypeTheory.ScopedIdentity

universe uObject uRoute

/-! ## Capability definitions -/

/-- Composition, inversion, and the groupoid equations for a route layer. -/
structure RouteGroupoid {Object : Type uObject}
    (layer : Layer.{uObject, uRoute} Object) where
  comp : ∀ {source middle target},
    layer.Route source middle -> layer.Route middle target ->
      layer.Route source target
  inv : ∀ {source target},
    layer.Route source target -> layer.Route target source
  refl_comp : ∀ {source target} (route : layer.Route source target),
    comp (layer.refl source) route = route
  comp_refl : ∀ {source target} (route : layer.Route source target),
    comp route (layer.refl target) = route
  assoc : ∀ {first second third last}
    (earlier : layer.Route first second)
    (middle : layer.Route second third)
    (later : layer.Route third last),
    comp (comp earlier middle) later = comp earlier (comp middle later)
  inv_comp : ∀ {source target} (route : layer.Route source target),
    comp (inv route) route = layer.refl target
  comp_inv : ∀ {source target} (route : layer.Route source target),
    comp route (inv route) = layer.refl source

/-- Reflection of route existence into equality of endpoints.  This is
strictly about endpoints and does not assert uniqueness of route evidence. -/
def EndpointReflection {Object : Type uObject}
    (layer : Layer.{uObject, uRoute} Object) : Prop :=
  ∀ {source target}, layer.Route source target -> source = target

/-- The proof-irrelevant support readout retains exact route identity only
when every route fibre is a subsingleton. -/
def SupportFaithful {Object : Type uObject}
    (layer : Layer.{uObject, uRoute} Object) : Prop :=
  ∀ {source target},
    Function.Injective
      (layer.forget : layer.Route source target ->
        layer.Support source target)

/-- Proposition-valued support is faithful exactly under route UIP. -/
theorem supportFaithful_iff_routeUIP {Object : Type uObject}
    (layer : Layer.{uObject, uRoute} Object) :
    SupportFaithful layer ↔ RouteUIP layer := by
  constructor
  · intro faithful source target
    refine ⟨?_⟩
    intro first second
    apply faithful
    exact Subsingleton.elim _ _
  · intro uip source target first second _sameSupport
    exact (uip source target).allEq first second

/-! ## Reusable Boolean groupoid -/

/-- Boolean xor supplies a one-object-style group law on every route fibre. -/
def boolComp (first second : Bool) : Bool := xor first second

theorem bool_refl_comp (route : Bool) : boolComp false route = route := by
  cases route <;> rfl

theorem bool_comp_refl (route : Bool) : boolComp route false = route := by
  cases route <;> rfl

theorem bool_comp_assoc (first second third : Bool) :
    boolComp (boolComp first second) third =
      boolComp first (boolComp second third) := by
  cases first <;> cases second <;> cases third <;> rfl

theorem bool_self_inverse (route : Bool) :
    boolComp route route = false := by
  cases route <;> rfl

/-! ## Four constructive cells -/

namespace Canary

/-! ### Reflection without UIP -/

/-- One object with two self-routes. -/
def reflectedPlural : Layer Unit where
  Route := fun _ _ => Bool
  refl := fun _ => false
  Support := fun _ _ => True
  forget := fun _ => trivial

def reflectedPluralGroupoid : RouteGroupoid reflectedPlural where
  comp := boolComp
  inv := id
  refl_comp := bool_refl_comp
  comp_refl := bool_comp_refl
  assoc := bool_comp_assoc
  inv_comp := bool_self_inverse
  comp_inv := bool_self_inverse

theorem reflectedPlural_reflects : EndpointReflection reflectedPlural := by
  intro source target _route
  cases source
  cases target
  rfl

theorem reflectedPlural_not_uip : ¬ RouteUIP reflectedPlural := by
  intro uip
  have equalRoutes := (uip () ()).allEq false true
  exact Bool.false_ne_true equalRoutes

/-! ### UIP without reflection -/

/-- Exactly one route between every pair of Boolean endpoints. -/
def indiscreteSubsingleton : Layer Bool where
  Route := fun _ _ => PUnit
  refl := fun _ => PUnit.unit
  Support := fun _ _ => True
  forget := fun _ => trivial

def indiscreteSubsingletonGroupoid : RouteGroupoid indiscreteSubsingleton where
  comp := fun _ _ => PUnit.unit
  inv := fun _ => PUnit.unit
  refl_comp := by
    intro source target route
    change PUnit.unit = route
    exact Subsingleton.elim _ _
  comp_refl := by
    intro source target route
    change PUnit.unit = route
    exact Subsingleton.elim _ _
  assoc := by
    intro first second third last earlier middle later
    change PUnit.unit = PUnit.unit
    rfl
  inv_comp := by
    intro source target route
    change PUnit.unit = PUnit.unit
    rfl
  comp_inv := by
    intro source target route
    change PUnit.unit = PUnit.unit
    rfl

theorem indiscreteSubsingleton_uip : RouteUIP indiscreteSubsingleton :=
  fun _ _ => show Subsingleton PUnit from inferInstance

theorem indiscreteSubsingleton_not_reflects :
    ¬ EndpointReflection indiscreteSubsingleton := by
  intro reflects
  have impossible : false = true := reflects PUnit.unit
  exact Bool.false_ne_true impossible

/-! ### Both reflection and UIP -/

/-- Equality witnesses lifted into `Type`, retaining only routes between
equal endpoints. -/
def liftedEquality : Layer Bool where
  Route := fun source target => PLift (source = target)
  refl := fun _ => ⟨rfl⟩
  Support := fun source target => source = target
  forget := fun route => route.down

def liftedEqualityGroupoid : RouteGroupoid liftedEquality where
  comp := fun first second => ⟨first.down.trans second.down⟩
  inv := fun route => ⟨route.down.symm⟩
  refl_comp := by
    intro source target route
    change (⟨rfl.trans route.down⟩ : PLift (source = target)) = route
    exact Subsingleton.elim _ _
  comp_refl := by
    intro source target route
    change (⟨route.down.trans rfl⟩ : PLift (source = target)) = route
    exact Subsingleton.elim _ _
  assoc := by
    intro first second third last earlier middle later
    change
      (⟨(earlier.down.trans middle.down).trans later.down⟩ :
        PLift (first = last)) =
      ⟨earlier.down.trans (middle.down.trans later.down)⟩
    exact Subsingleton.elim _ _
  inv_comp := by
    intro source target route
    change (⟨route.down.symm.trans route.down⟩ : PLift (target = target)) =
      ⟨rfl⟩
    exact Subsingleton.elim _ _
  comp_inv := by
    intro source target route
    change (⟨route.down.trans route.down.symm⟩ : PLift (source = source)) =
      ⟨rfl⟩
    exact Subsingleton.elim _ _

theorem liftedEquality_reflects : EndpointReflection liftedEquality :=
  fun route => route.down

theorem liftedEquality_uip : RouteUIP liftedEquality :=
  fun source target =>
    show Subsingleton (PLift (source = target)) from inferInstance

/-! ### Neither reflection nor UIP -/

/-- Two routes between every pair of Boolean endpoints. -/
def indiscretePlural : Layer Bool where
  Route := fun _ _ => Bool
  refl := fun _ => false
  Support := fun _ _ => True
  forget := fun _ => trivial

def indiscretePluralGroupoid : RouteGroupoid indiscretePlural where
  comp := boolComp
  inv := id
  refl_comp := bool_refl_comp
  comp_refl := bool_comp_refl
  assoc := bool_comp_assoc
  inv_comp := bool_self_inverse
  comp_inv := bool_self_inverse

theorem indiscretePlural_not_reflects :
    ¬ EndpointReflection indiscretePlural := by
  intro reflects
  have impossible : false = true := reflects false
  exact Bool.false_ne_true impossible

theorem indiscretePlural_not_uip : ¬ RouteUIP indiscretePlural := by
  intro uip
  have equalRoutes := (uip false false).allEq false true
  exact Bool.false_ne_true equalRoutes

/-- Groupoid/J-shaped route algebra leaves both endpoint reflection and UIP
undecided: all four combinations are constructively inhabited. -/
theorem groupoid_reflection_uip_independent :
    (Nonempty (RouteGroupoid reflectedPlural) ∧
      EndpointReflection reflectedPlural ∧ ¬ RouteUIP reflectedPlural) ∧
    (Nonempty (RouteGroupoid indiscreteSubsingleton) ∧
      ¬ EndpointReflection indiscreteSubsingleton ∧
        RouteUIP indiscreteSubsingleton) ∧
    (Nonempty (RouteGroupoid liftedEquality) ∧
      EndpointReflection liftedEquality ∧ RouteUIP liftedEquality) ∧
    (Nonempty (RouteGroupoid indiscretePlural) ∧
      ¬ EndpointReflection indiscretePlural ∧ ¬ RouteUIP indiscretePlural) :=
  ⟨⟨⟨reflectedPluralGroupoid⟩, reflectedPlural_reflects,
      reflectedPlural_not_uip⟩,
    ⟨⟨indiscreteSubsingletonGroupoid⟩,
      indiscreteSubsingleton_not_reflects, indiscreteSubsingleton_uip⟩,
    ⟨⟨liftedEqualityGroupoid⟩, liftedEquality_reflects,
      liftedEquality_uip⟩,
    ⟨⟨indiscretePluralGroupoid⟩, indiscretePlural_not_reflects,
      indiscretePlural_not_uip⟩⟩

/-- The support readout is faithful in the UIP cells and necessarily
nonfaithful in the route-plural cells. -/
theorem support_faithfulness_matrix :
    SupportFaithful indiscreteSubsingleton ∧
      SupportFaithful liftedEquality ∧
      ¬ SupportFaithful reflectedPlural ∧
      ¬ SupportFaithful indiscretePlural := by
  rw [supportFaithful_iff_routeUIP,
    supportFaithful_iff_routeUIP,
    supportFaithful_iff_routeUIP,
    supportFaithful_iff_routeUIP]
  exact ⟨indiscreteSubsingleton_uip, liftedEquality_uip,
    reflectedPlural_not_uip, indiscretePlural_not_uip⟩

end Canary

#print axioms supportFaithful_iff_routeUIP
#print axioms Canary.groupoid_reflection_uip_independent
#print axioms Canary.support_faithfulness_matrix

end Mettapedia.TypeTheory.IdentityRouteCapabilities
