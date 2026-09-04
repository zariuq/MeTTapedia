import Mettapedia.TypeTheory.ContextualIdentityTypes
import Mettapedia.TypeTheory.EqualityFamilyObserverFactorization

/-!
# Identity routes compared with observed equality

An extensional equality can be a sound readout of an intensional route family
without being complete or faithful.  This module separates the relevant
properties for an arbitrary observation `Source -> Target`:

* soundness: every retained route gives equality of observed endpoints;
* completeness: every observed equality is represented by a retained route;
* faithfulness: equality of observations does not identify distinct routes;
* endpoint reflection: a retained route identifies the original endpoints.

Faithfulness of the route-to-equality map is exactly route UIP.  In the
presence of endpoint reflection, completeness is exactly injectivity of the
endpoint observation.  Thus an exact comparison between intensional routes
and extensional equality requires two independent facts: a faithful endpoint
readout and thin route fibres.

The results are criteria for relating identity disciplines.  They do not
select an object-language identity type, an extensional simple type theory,
equality reflection, UIP, or univalence.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IdentityObservationComparison

open Mettapedia.TypeTheory.ScopedIdentity
open Mettapedia.TypeTheory.IdentityRouteCapabilities
open Mettapedia.TypeTheory.ContextualIdentityTypes
open Mettapedia.TypeTheory.ExtensionalReadout
open Mettapedia.GSLT.Core.ContextualLadder

universe uSource uRoute uTarget u v w w'

/-! ## Generic comparison -/

/-- A sound comparison from retained routes to equality after an observation.
No completeness, proof irrelevance, or reflection to source equality is
assumed. -/
structure Comparison
    {Source : Type uSource} (layer : Layer.{uSource, uRoute} Source)
    {Target : Type uTarget} (observe : Source -> Target) where
  toObservedEquality : forall {source target},
    layer.Route source target -> observe source = observe target

namespace Comparison

variable {Source : Type uSource} {Target : Type uTarget}
variable {layer : Layer.{uSource, uRoute} Source}
variable {observe : Source -> Target}
variable (comparison : Comparison layer observe)

/-- Every equality of observed endpoints is represented by a route. -/
def Complete : Prop :=
  forall source target,
    Function.Surjective
      (fun route : layer.Route source target =>
        comparison.toObservedEquality route)

/-- The equality readout retains the identity of route witnesses. -/
def Faithful : Prop :=
  forall source target,
    Function.Injective
      (fun route : layer.Route source target =>
        comparison.toObservedEquality route)

/-- The route-to-observed-equality map is bijective in every endpoint fibre. -/
def Exact : Prop :=
  forall source target,
    Function.Bijective
      (fun route : layer.Route source target =>
        comparison.toObservedEquality route)

/-- Any exact comparison is complete. -/
theorem complete_of_exact (exact : comparison.Exact) : comparison.Complete :=
  fun source target => (exact source target).2

/-- Any exact comparison is faithful. -/
theorem faithful_of_exact (exact : comparison.Exact) : comparison.Faithful :=
  fun source target => (exact source target).1

/-- Equality proofs are propositionally thin, so faithfulness of the
route-to-equality map is exactly route UIP. -/
theorem faithful_iff_routeUIP :
    comparison.Faithful <-> RouteUIP layer := by
  constructor
  · intro faithful source target
    refine ⟨?_⟩
    intro first second
    apply faithful source target
    exact Subsingleton.elim _ _
  · intro uip source target first second _sameEquality
    exact (uip source target).allEq first second

/-- Exactness decomposes into completeness of observed equality and thinness
of the retained route fibres. -/
theorem exact_iff_complete_and_routeUIP :
    comparison.Exact <-> comparison.Complete ∧ RouteUIP layer := by
  constructor
  · intro exact
    exact ⟨comparison.complete_of_exact exact,
      comparison.faithful_iff_routeUIP.mp
        (comparison.faithful_of_exact exact)⟩
  · rintro ⟨complete, uip⟩ source target
    exact ⟨fun first second _ =>
      (uip source target).allEq first second,
      complete source target⟩

/-- An injective endpoint observation makes every observed equality lift to a
route, using only reflexivity of the route layer. -/
theorem complete_of_observe_injective
    (injective : Function.Injective observe) : comparison.Complete := by
  intro source target sameObservation
  have sameEndpoint : source = target := injective sameObservation
  subst target
  refine ⟨layer.refl source, ?_⟩
  exact Subsingleton.elim _ _

/-- If routes reflect source endpoints, completeness of the comparison forces
the endpoint observation to be injective. -/
theorem observe_injective_of_complete
    (reflects : EndpointReflection layer)
    (complete : comparison.Complete) : Function.Injective observe := by
  intro source target sameObservation
  obtain ⟨route, _routeReadsAsEquality⟩ :=
    complete source target sameObservation
  exact reflects route

/-- Under endpoint reflection, comparison completeness is precisely
faithfulness of the endpoint observation. -/
theorem complete_iff_observe_injective
    (reflects : EndpointReflection layer) :
    comparison.Complete <-> Function.Injective observe := by
  constructor
  · exact comparison.observe_injective_of_complete reflects
  · exact comparison.complete_of_observe_injective

/-- An injective observation turns soundness after observation into endpoint
reflection before observation. -/
theorem endpointReflection_of_observe_injective
    (sound : Comparison layer observe)
    (injective : Function.Injective observe) : EndpointReflection layer := by
  intro source target route
  exact injective
    (@Comparison.toObservedEquality Source layer Target observe sound
      source target route)

/-- With endpoint reflection available, exact comparison has exactly two
independent prices: injective observation of endpoints and route UIP. -/
theorem exact_iff_observe_injective_and_routeUIP
    (reflects : EndpointReflection layer) :
    comparison.Exact <->
      Function.Injective observe ∧ RouteUIP layer := by
  rw [comparison.exact_iff_complete_and_routeUIP,
    comparison.complete_iff_observe_injective reflects]

end Comparison

/-! ## Canonical comparisons and contextual identity -/

/-- Endpoint reflection supplies a canonical sound comparison along every
endpoint observation. -/
def ofEndpointReflection
    {Source : Type uSource} {Target : Type uTarget}
    {layer : Layer.{uSource, uRoute} Source}
    (reflects : EndpointReflection layer) (observe : Source -> Target) :
    Comparison layer observe where
  toObservedEquality route := congrArg observe (reflects route)

/-- For a split extensional readout, exact identity transport is equivalent
to exactness of the endpoint readout together with route UIP.  Completeness of
visible values alone is insufficient. -/
theorem splitReadout_exactComparison_iff
    {Source : Type uSource} {Target : Type uTarget}
    {layer : Layer.{uSource, uRoute} Source}
    (reflects : EndpointReflection layer)
    (readout : SplitReadout Source Target) :
    (ofEndpointReflection reflects readout.observe).Exact <->
      readout.Exact ∧ RouteUIP layer := by
  constructor
  · intro exact
    have boundary :=
      (Comparison.exact_iff_observe_injective_and_routeUIP
        (ofEndpointReflection reflects readout.observe) reflects).mp exact
    exact ⟨readout.exact_iff_faithful.mpr boundary.1, boundary.2⟩
  · rintro ⟨readoutExact, uip⟩
    exact
      (Comparison.exact_iff_observe_injective_and_routeUIP
        (ofEndpointReflection reflects readout.observe) reflects).mpr
          ⟨readout.exact_iff_faithful.mp readoutExact, uip⟩

/-- Intrinsic contextual identity gives a route layer at each term fibre.  An
endpoint-reflecting identity discipline therefore induces a sound comparison
to equality after any selected term observation. -/
def ofIntrinsicEndpointReflection
    (C : Cwf.{u, v, w, w'})
    (identity : IdentityFormation C)
    (introduction : IdentityReflexivity C identity)
    (reflects : IdentityEndpointReflection C identity)
    {context : C.Ctx} (type : C.Ty context)
    {Target : Type uTarget} (observe : C.Tm context type -> Target) :
    Comparison (termIdentityLayer C identity introduction type) observe :=
  ofEndpointReflection (fun route => reflects route) observe

/-- Pointwise exactness of an intrinsic-identity readout requires both an
injective observation of terms and proof irrelevance of that identity fibre.
The statement deliberately does not assume these properties globally. -/
theorem intrinsic_exact_iff_injective_and_thin
    (C : Cwf.{u, v, w, w'})
    (identity : IdentityFormation C)
    (introduction : IdentityReflexivity C identity)
    (reflects : IdentityEndpointReflection C identity)
    {context : C.Ctx} (type : C.Ty context)
    {Target : Type uTarget} (observe : C.Tm context type -> Target) :
    (ofIntrinsicEndpointReflection C identity introduction reflects type
      observe).Exact <->
      Function.Injective observe ∧
        (forall left right,
          Subsingleton
            (C.Tm context (identity.idTy type left right))) := by
  simpa [RouteUIP, termIdentityLayer] using
    (ofIntrinsicEndpointReflection C identity introduction reflects type
      observe).exact_iff_observe_injective_and_routeUIP
        (fun route => reflects route)

/-! ## Positive and adversarial controls -/

namespace Canary

open Mettapedia.TypeTheory.IdentityRouteCapabilities.Canary
open Mettapedia.TypeTheory.DependencyExtensionalityOrthogonality
open Mettapedia.TypeTheory.ExtensionalReadout.Canary

/-- Ordinary lifted equality, defined for an arbitrary carrier. -/
def equalityLayer (Carrier : Type uSource) : Layer Carrier where
  Route source target := PLift (source = target)
  refl _ := ⟨rfl⟩
  Support source target := source = target
  forget route := route.down

theorem equalityLayer_reflects (Carrier : Type uSource) :
    EndpointReflection (equalityLayer Carrier) :=
  fun route => route.down

theorem equalityLayer_uip (Carrier : Type uSource) :
    RouteUIP (equalityLayer Carrier) :=
  fun source target =>
    show Subsingleton (PLift (source = target)) from inferInstance

/-- Ordinary equality observed without quotienting is exact. -/
def exactEquality : Comparison (equalityLayer Bool) (id : Bool -> Bool) :=
  ofEndpointReflection (equalityLayer_reflects Bool) id

theorem exactEquality_is_exact : exactEquality.Exact := by
  rw [exactEquality.exact_iff_observe_injective_and_routeUIP
    (equalityLayer_reflects Bool)]
  exact ⟨Function.injective_id, equalityLayer_uip Bool⟩

/-- A plural self-route layer can be complete on extensional equality while
remaining nonfaithful to route identity. -/
def pluralEquality :
    Comparison reflectedPlural (id : Unit -> Unit) :=
  ofEndpointReflection reflectedPlural_reflects id

theorem pluralEquality_complete : pluralEquality.Complete :=
  pluralEquality.complete_of_observe_injective Function.injective_id

theorem pluralEquality_not_faithful : ¬ pluralEquality.Faithful := by
  rw [pluralEquality.faithful_iff_routeUIP]
  exact reflectedPlural_not_uip

theorem pluralEquality_not_exact : ¬ pluralEquality.Exact := by
  rw [pluralEquality.exact_iff_complete_and_routeUIP]
  exact fun exact => reflectedPlural_not_uip exact.2

/-- The coarsest Boolean endpoint observation. -/
def coarseBool : Bool -> PUnit := fun _ => PUnit.unit

/-- Coarse equality is sound for ordinary source equality. -/
def coarseEquality : Comparison (equalityLayer Bool) coarseBool :=
  ofEndpointReflection (equalityLayer_reflects Bool) coarseBool

/-- But it invents an observed equality between distinct source endpoints, so
it is not complete with respect to ordinary identity routes. -/
theorem coarseEquality_not_complete : ¬ coarseEquality.Complete := by
  rw [coarseEquality.complete_iff_observe_injective
    (equalityLayer_reflects Bool)]
  intro injective
  exact Bool.false_ne_true (injective rfl)

/-- A thin indiscrete route relation is exactly represented by equality in a
coarse one-point observation, despite failing source endpoint reflection. -/
def indiscreteCoarse :
    Comparison indiscreteSubsingleton coarseBool where
  toObservedEquality _route := rfl

theorem indiscreteCoarse_exact : indiscreteCoarse.Exact := by
  intro source target
  constructor
  · intro first second _sameEquality
    exact (indiscreteSubsingleton_uip source target).allEq first second
  · intro sameObservation
    exact ⟨PUnit.unit, Subsingleton.elim _ sameObservation⟩

theorem indiscreteCoarse_not_endpointReflection :
    ¬ EndpointReflection indiscreteSubsingleton :=
  indiscreteSubsingleton_not_reflects

/-- Equality of route-bearing function values cannot be transported exactly
through application behavior when the extensional readout forgets a route
tag. -/
def functionBehaviorEquality :
    Comparison (equalityLayer simpleRouteSensitive.Function)
      routeReadout.observe :=
  ofEndpointReflection
    (equalityLayer_reflects simpleRouteSensitive.Function)
    routeReadout.observe

theorem functionBehaviorEquality_not_complete :
    ¬ functionBehaviorEquality.Complete := by
  rw [functionBehaviorEquality.complete_iff_observe_injective
    (equalityLayer_reflects simpleRouteSensitive.Function)]
  exact routeReadout_not_faithful

/-- The four controls distinguish all relevant failure modes: exact ordinary
identity, complete-but-route-losing equality, sound-but-incomplete coarse
equality, and exact equality over a relation which is not source identity. -/
theorem identityObservation_boundary :
    exactEquality.Exact ∧
      (pluralEquality.Complete ∧ ¬ pluralEquality.Faithful) ∧
      ¬ coarseEquality.Complete ∧
      (indiscreteCoarse.Exact ∧
        ¬ EndpointReflection indiscreteSubsingleton) ∧
      ¬ functionBehaviorEquality.Complete :=
  ⟨exactEquality_is_exact,
    ⟨pluralEquality_complete, pluralEquality_not_faithful⟩,
    coarseEquality_not_complete,
    ⟨indiscreteCoarse_exact, indiscreteCoarse_not_endpointReflection⟩,
    functionBehaviorEquality_not_complete⟩

end Canary

#print axioms Comparison.faithful_iff_routeUIP
#print axioms Comparison.exact_iff_complete_and_routeUIP
#print axioms Comparison.complete_iff_observe_injective
#print axioms Comparison.exact_iff_observe_injective_and_routeUIP
#print axioms splitReadout_exactComparison_iff
#print axioms intrinsic_exact_iff_injective_and_thin
#print axioms Canary.identityObservation_boundary

end Mettapedia.TypeTheory.IdentityObservationComparison
