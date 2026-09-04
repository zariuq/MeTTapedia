import Mettapedia.TypeTheory.CategoryIndexedFamilyTwoCellAction
import Mettapedia.TypeTheory.DecidableIdentityRouteStructure

/-!
# Route transport as an exact proof-relevance discriminator

A proof-relevant route is computationally relevant precisely when some lawful
dependent transport can distinguish it from a parallel route.  This module
makes that criterion exact without selecting an identity theory.

For a route layer with groupoid operations, a transport family consists of
fibres over objects and functorial transport along routes.  The covariant
representable family based at the source object distinguishes any two distinct
parallel routes.  Consequently:

* two routes have the same action on every transport family exactly when they
  are equal;
* route UIP is exactly the absence of transport discriminators; and
* a transport discriminator rules out the decidable identity-route structure
  whose Hedberg argument entails UIP.

The same criterion is stated for natural transformations between context
substitutions.  There, covariant indexed families jointly distinguish 2-cells.
This gives a common mathematical gate for identity transport and directed
mode-cell action while keeping the two notions separate.

The Boolean canary realizes identity and negation as two automorphism routes.
Their actions on `false` differ.  It is only a transport/groupoid specimen:
no univalence principle or object-language identity eliminator is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.RouteTransportDiscriminator

open CategoryTheory
open Mettapedia.TypeTheory.ScopedIdentity
open Mettapedia.TypeTheory.IdentityRouteCapabilities
open Mettapedia.TypeTheory.DecidableIdentityRouteStructure
open Mettapedia.TypeTheory.CategoryIndexedFamilyCwf
open Mettapedia.TypeTheory.CategoryIndexedFamilyTwoCellAction

universe uObject uRoute uFiber u
universe uSource vSource uTarget vTarget

/-! ## Lawful transport over a route groupoid -/

/-- A dependent family with functorial transport along a selected route
groupoid.  No identity eliminator, universe, or equality reflection is part of
this structure. -/
structure TransportFamily
    {Object : Type uObject} (layer : Layer.{uObject, uRoute} Object)
    (groupoid : RouteGroupoid layer) where
  Fibre : Object → Type uFiber
  transport : ∀ {source target},
    layer.Route source target → Fibre source → Fibre target
  transport_refl : ∀ (object : Object) (value : Fibre object),
    transport (layer.refl object) value = value
  transport_comp : ∀ {source middle target}
    (earlier : layer.Route source middle)
    (later : layer.Route middle target) (value : Fibre source),
    transport (groupoid.comp earlier later) value =
      transport later (transport earlier value)

namespace TransportFamily

variable {Object : Type uObject}
variable {layer : Layer.{uObject, uRoute} Object}
variable {groupoid : RouteGroupoid layer}

/-- One family distinguishes two parallel routes when they transport some
source value to different target values. -/
def Distinguishes (family : TransportFamily.{uObject, uRoute, uFiber}
    layer groupoid) {source target : Object}
    (first second : layer.Route source target) : Prop :=
  ∃ value : family.Fibre source,
    family.transport first value ≠ family.transport second value

/-- Equality of routes makes their action equal in every transport family. -/
theorem not_distinguishes_of_eq
    (family : TransportFamily.{uObject, uRoute, uFiber} layer groupoid)
    {source target : Object} {first second : layer.Route source target}
    (same : first = second) : ¬ family.Distinguishes first second := by
  subst second
  rintro ⟨value, different⟩
  exact different rfl

end TransportFamily

/-! ## The representable discriminator -/

/-- The covariant representable family based at `base`.  Its fibre at
`target` is the type of routes from `base` to `target`; transport is route
composition. -/
def covariantRepresentable
    {Object : Type uObject} {layer : Layer.{uObject, uRoute} Object}
    (groupoid : RouteGroupoid layer) (base : Object) :
    TransportFamily.{uObject, uRoute, uRoute} layer groupoid where
  Fibre target := layer.Route base target
  transport route prior := groupoid.comp prior route
  transport_refl _ prior := groupoid.comp_refl prior
  transport_comp earlier later prior :=
    (groupoid.assoc prior earlier later).symm

@[simp] theorem covariantRepresentable_transport_reflSource
    {Object : Type uObject} {layer : Layer.{uObject, uRoute} Object}
    (groupoid : RouteGroupoid layer) {source target : Object}
    (route : layer.Route source target) :
    (covariantRepresentable groupoid source).transport route
        (layer.refl source) = route :=
  groupoid.refl_comp route

/-- Some lawful route-valued dependent family distinguishes the two routes. -/
def HasTransportDiscriminator
    {Object : Type uObject} {layer : Layer.{uObject, uRoute} Object}
    (groupoid : RouteGroupoid layer) {source target : Object}
    (first second : layer.Route source target) : Prop :=
  ∃ family : TransportFamily.{uObject, uRoute, uRoute} layer groupoid,
    family.Distinguishes first second

/-- Yoneda-style exactness: distinct parallel routes are exactly those which
some lawful transport family distinguishes.  The reverse direction uses the
representable family, so it is constructive and needs no choice principle. -/
theorem hasTransportDiscriminator_iff_ne
    {Object : Type uObject} {layer : Layer.{uObject, uRoute} Object}
    (groupoid : RouteGroupoid layer) {source target : Object}
    (first second : layer.Route source target) :
    HasTransportDiscriminator groupoid first second ↔ first ≠ second := by
  constructor
  · rintro ⟨family, value, different⟩ same
    subst second
    exact different rfl
  · intro different
    refine ⟨covariantRepresentable groupoid source,
      ⟨layer.refl source, ?_⟩⟩
    change
      groupoid.comp (layer.refl source) first ≠
        groupoid.comp (layer.refl source) second
    intro equalComposites
    apply different
    simpa only [groupoid.refl_comp] using equalComposites

/-- Route UIP forbids every lawful transport discriminator. -/
theorem no_transportDiscriminator_of_routeUIP
    {Object : Type uObject} {layer : Layer.{uObject, uRoute} Object}
    (groupoid : RouteGroupoid layer) (uip : RouteUIP layer)
    {source target : Object} (first second : layer.Route source target) :
    ¬ HasTransportDiscriminator groupoid first second := by
  rw [hasTransportDiscriminator_iff_ne]
  exact fun different => different ((uip source target).allEq first second)

/-- Conversely, the absence of transport discriminators in every parallel
fibre forces route UIP. -/
theorem routeUIP_of_no_transportDiscriminator
    {Object : Type uObject} {layer : Layer.{uObject, uRoute} Object}
    (groupoid : RouteGroupoid layer)
    (none : ∀ {source target : Object}
      (first second : layer.Route source target),
      ¬ HasTransportDiscriminator groupoid first second) :
    RouteUIP layer := by
  intro source target
  refine ⟨?_⟩
  intro first second
  by_contra different
  exact none first second
    ((hasTransportDiscriminator_iff_ne groupoid first second).2 different)

/-- Exact global criterion: a groupoid route layer is UIP precisely when no
lawful dependent transport can distinguish parallel routes. -/
theorem routeUIP_iff_no_transportDiscriminator
    {Object : Type uObject} {layer : Layer.{uObject, uRoute} Object}
    (groupoid : RouteGroupoid layer) :
    RouteUIP layer ↔
      ∀ {source target : Object} (first second : layer.Route source target),
        ¬ HasTransportDiscriminator groupoid first second := by
  constructor
  · intro uip source target first second
    exact no_transportDiscriminator_of_routeUIP groupoid uip first second
  · exact routeUIP_of_no_transportDiscriminator groupoid

/-! ## Boundary with decidable identity admission -/

/-- A route layer admitted by the full decidable identity-route criterion has
transport-invariant parallel routes.  This conclusion is scoped to that exact
criterion; decidable object syntax alone is not used. -/
theorem identityStructure_transport_invariant
    {Object : Type uObject} {layer : Layer.{uObject, uRoute} Object}
    (identity : Structure layer)
    (family : TransportFamily.{uObject, uRoute, uFiber}
      layer identity.groupoid)
    {source target : Object} (first second : layer.Route source target)
    (value : family.Fibre source) :
    family.transport first value = family.transport second value := by
  exact congrArg (fun route => family.transport route value)
    ((identity.routeUIP source target).allEq first second)

/-- A single transport-sensitive pair is an exact obstruction to the full
decidable identity-route structure. -/
theorem transportDiscriminator_excludes_identityStructure
    {Object : Type uObject} {layer : Layer.{uObject, uRoute} Object}
    (groupoid : RouteGroupoid layer) {source target : Object}
    {first second : layer.Route source target}
    (observable : HasTransportDiscriminator groupoid first second) :
    ¬ Nonempty (Structure layer) := by
  intro admitted
  have different :=
    (hasTransportDiscriminator_iff_ne groupoid first second).1 observable
  exact pluralRouteFibre_excludes_structure
    ⟨source, target, first, second, different⟩ admitted

/-! ## The corresponding category and context 2-cell gates -/

/-- A covariant family which distinguishes two parallel natural
transformations, allowing the object and morphism universes of the categories
to differ. -/
def HasWhiskeredFamilyDiscriminator
    {Source : Type uSource} [Category.{vSource} Source]
    {Target : Type uTarget} [Category.{vTarget} Target]
    {left right : Functor Source Target}
    (first second : left ⟶ right) : Prop :=
  ∃ family : Functor Target (Type vTarget),
    whiskeredFamilyAction first family ≠
      whiskeredFamilyAction second family

/-- A whiskered-family discriminator proves that the natural transformations
are distinct. -/
theorem naturalTransformations_ne_of_whiskeredFamilyDiscriminator
    {Source : Type uSource} [Category.{vSource} Source]
    {Target : Type uTarget} [Category.{vTarget} Target]
    {left right : Functor Source Target}
    {first second : left ⟶ right}
    (observable : HasWhiskeredFamilyDiscriminator first second) :
    first ≠ second := by
  rintro same
  subst second
  rcases observable with ⟨family, different⟩
  exact different rfl

/-- Classically, covariant representables turn joint faithfulness into the
single-consumer gate: distinct parallel natural transformations are
distinguished by at least one covariant family. -/
theorem hasWhiskeredFamilyDiscriminator_iff_ne
    {Source : Type uSource} [Category.{vSource} Source]
    {Target : Type uTarget} [Category.{vTarget} Target]
    {left right : Functor Source Target}
    (first second : left ⟶ right) :
    HasWhiskeredFamilyDiscriminator first second ↔ first ≠ second := by
  classical
  constructor
  · exact naturalTransformations_ne_of_whiskeredFamilyDiscriminator
  · intro different
    by_contra noDiscriminator
    have allEqual : ∀ family : Functor Target (Type vTarget),
        whiskeredFamilyAction first family =
          whiskeredFamilyAction second family := by
      intro family
      by_contra unequal
      exact noDiscriminator ⟨family, unequal⟩
    apply different
    apply whiskeredDependentAction_injective
    funext family
    exact allEqual family

/-- A required dependent consumer for two parallel context cells is one
indexed family on which their induced natural transformations differ. -/
def HasDependentFamilyDiscriminator
    {source target : Context.{u}}
    {left right : ContextHom source target}
    (first second : left ⟶ right) : Prop :=
  ∃ family : IndexedFamily target,
    familyAction first family ≠ familyAction second family

/-- Any dependent family discriminator proves that the context cells are
distinct. -/
theorem contextCells_ne_of_dependentFamilyDiscriminator
    {source target : Context.{u}}
    {left right : ContextHom source target}
    {first second : left ⟶ right}
    (observable : HasDependentFamilyDiscriminator first second) :
    first ≠ second := by
  rintro same
  subst second
  rcases observable with ⟨family, different⟩
  exact different rfl

/-- Classically, the joint faithfulness theorem sharpens to the operational
gate used in design decisions: distinct context 2-cells provide one concrete
dependent family which distinguishes their actions. -/
theorem hasDependentFamilyDiscriminator_iff_ne
    {source target : Context.{u}}
    {left right : ContextHom source target}
    (first second : left ⟶ right) :
    HasDependentFamilyDiscriminator first second ↔ first ≠ second := by
  classical
  constructor
  · exact contextCells_ne_of_dependentFamilyDiscriminator
  · intro different
    by_contra noDiscriminator
    have allEqual : ∀ family : IndexedFamily target,
        familyAction first family = familyAction second family := by
      intro family
      by_contra unequal
      exact noDiscriminator ⟨family, unequal⟩
    apply different
    apply (dependentAction_eq_iff first second).1
    funext family
    exact allEqual family

/-! ## Boolean identity/negation transport canary -/

namespace Canary

open Mettapedia.TypeTheory.IdentityRouteCapabilities.Canary

/-- The two Boolean route codes act as the identity and Boolean negation.
This is the smallest computational transport specimen behind the familiar
`id`/`not` discriminator. -/
def booleanAutomorphismTransport :
    TransportFamily reflectedPlural reflectedPluralGroupoid where
  Fibre _ := Bool
  transport route value := xor value route
  transport_refl _ value := by cases value <;> rfl
  transport_comp earlier later value := by
    cases value <;> cases earlier <;> cases later <;> rfl

@[simp] theorem identityRoute_transports_false :
    booleanAutomorphismTransport.transport
      (source := ()) (target := ()) false false = false :=
  rfl

@[simp] theorem negationRoute_transports_false :
    booleanAutomorphismTransport.transport
      (source := ()) (target := ()) true false = true :=
  rfl

/-- The identity and negation routes are separated by their transport of one
Boolean value. -/
theorem booleanAutomorphisms_have_transportDiscriminator :
    HasTransportDiscriminator reflectedPluralGroupoid
      (source := ()) (target := ()) false true := by
  refine ⟨booleanAutomorphismTransport, false, ?_⟩
  exact Bool.false_ne_true

/-- Therefore this route/transport specimen is not UIP. -/
theorem booleanAutomorphismTransport_forces_nonUIP :
    ¬ RouteUIP reflectedPlural := by
  intro uip
  exact
    (no_transportDiscriminator_of_routeUIP reflectedPluralGroupoid uip
      false true)
      booleanAutomorphisms_have_transportDiscriminator

/-- And it cannot be reclassified as the complete decidable identity-route
structure.  This does not refute univalence: that theory does not identify
the automorphism groupoid on one chosen code with ordinary identity on the
one-point carrier. -/
theorem booleanAutomorphismTransport_excludes_identityStructure :
    ¬ Nonempty (Structure reflectedPlural) :=
  transportDiscriminator_excludes_identityStructure
    reflectedPluralGroupoid
    booleanAutomorphisms_have_transportDiscriminator

/-- Positive thin control: lifted ordinary Boolean equality admits the
decidable identity structure, so no lawful family can distinguish parallel
equality routes. -/
theorem liftedEquality_has_no_transportDiscriminator
    {source target : Bool}
    (first second : liftedEquality.Route source target) :
    ¬ HasTransportDiscriminator liftedEqualityGroupoid first second :=
  no_transportDiscriminator_of_routeUIP liftedEqualityGroupoid
    liftedEquality_uip first second

/-- The complete choice boundary keeps both outcomes explicit: thin ordinary
equality supports decidable identity admission, while proof-relevant
automorphism transport has a concrete consumer and excludes that admission. -/
theorem thin_identity_and_transport_relevant_routes_boundary :
    (∀ {source target : Bool}
      (first second : liftedEquality.Route source target),
        ¬ HasTransportDiscriminator liftedEqualityGroupoid first second) ∧
      HasTransportDiscriminator reflectedPluralGroupoid
        (source := ()) (target := ()) false true ∧
      ¬ Nonempty (Structure reflectedPlural) :=
  ⟨liftedEquality_has_no_transportDiscriminator,
    booleanAutomorphisms_have_transportDiscriminator,
    booleanAutomorphismTransport_excludes_identityStructure⟩

end Canary

/-! ## Axiom audit -/

#print axioms hasTransportDiscriminator_iff_ne
#print axioms routeUIP_iff_no_transportDiscriminator
#print axioms identityStructure_transport_invariant
#print axioms transportDiscriminator_excludes_identityStructure
#print axioms hasWhiskeredFamilyDiscriminator_iff_ne
#print axioms hasDependentFamilyDiscriminator_iff_ne
#print axioms Canary.booleanAutomorphisms_have_transportDiscriminator
#print axioms Canary.thin_identity_and_transport_relevant_routes_boundary

end Mettapedia.TypeTheory.RouteTransportDiscriminator
