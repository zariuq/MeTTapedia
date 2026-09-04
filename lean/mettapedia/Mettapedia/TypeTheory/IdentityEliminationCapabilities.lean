import Mettapedia.TypeTheory.IdentityRouteCapabilities

/-!
# Identity elimination, decidable route support, and scoped UIP

This module states a route-family form of the Hedberg argument without
selecting an identity theory for any object language.

Four ingredients remain explicit:

* a reflexive route family;
* groupoid composition and inversion;
* propositional identity elimination from reflexivity; and
* a proof-relevant decision procedure for whether a route fibre is inhabited.

Identity elimination alone reflects routes into equality of endpoints.
Together with decidable route support and the groupoid laws, it also makes
every route fibre a subsingleton.  The proof normalizes the constant selector
provided by decidability so that it fixes reflexivity, then applies identity
elimination.

The counterexamples show why decidable object syntax, decidable route support,
or groupoid operations alone are not a UIP certificate.  This is a generic
criterion, not an admission of K, equality reflection, or proof irrelevance
for a particular language.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IdentityEliminationCapabilities

open Mettapedia.TypeTheory.ScopedIdentity
open Mettapedia.TypeTheory.IdentityRouteCapabilities

universe uObject uRoute

/-! ## Identity-elimination and decidability capabilities -/

/-- Propositional identity elimination for a route family.  This is the
dependent elimination principle into `Prop`; no judgmental computation rule
or elimination into data is assumed.  The `External` qualifier is essential:
motives are Lean propositions over semantic routes.  An internal
object-language J rule reaches this structure only through a separate
adequacy or model theorem. -/
structure ExternalPropositionalIdentityElimination {Object : Type uObject}
    (layer : Layer.{uObject, uRoute} Object) where
  eliminate :
    ∀ {source : Object}
      (motive : ∀ target, layer.Route source target → Prop),
      motive source (layer.refl source) →
      ∀ {target} (route : layer.Route source target), motive target route

/-- A proof-relevant decision of route-fibre inhabitation.  The positive
branch carries an actual route.  This is stronger than
`Decidable (Nonempty Route)`, whose witness is propositionally truncated and
cannot be extracted into route-valued data without choice. -/
inductive RouteDecision (Route : Type uRoute) where
  | present (selected : Route)
  | absent (refute : Route → False)

/-- Constructive, proof-relevant decisions for every route fibre. -/
abbrev RouteInhabitationDecision {Object : Type uObject}
    (layer : Layer.{uObject, uRoute} Object) :=
  ∀ source target, RouteDecision (layer.Route source target)

/-- A decision of inhabitation supplies a constant endomap on every inhabited
fibre.  The impossible branch is eliminated by the input route itself. -/
def constantSelector {Route : Type uRoute}
    (decision : RouteDecision Route) : Route → Route :=
  match decision with
  | .present selected => fun _ => selected
  | .absent refute => fun route => (refute route).elim

theorem constantSelector_weaklyConstant {Route : Type uRoute}
    (decision : RouteDecision Route)
    (first second : Route) :
    constantSelector decision first = constantSelector decision second := by
  cases decision with
  | present selected => rfl
  | absent refute => exact (refute first).elim

/-- Select the canonical route chosen by the inhabitation decision for the
given endpoints. -/
def selectRoute {Object : Type uObject}
    {layer : Layer.{uObject, uRoute} Object}
    (decision : RouteInhabitationDecision layer)
    {source target : Object} :
    layer.Route source target → layer.Route source target :=
  constantSelector (decision source target)

theorem selectRoute_weaklyConstant {Object : Type uObject}
    {layer : Layer.{uObject, uRoute} Object}
    (decision : RouteInhabitationDecision layer)
    {source target : Object}
    (first second : layer.Route source target) :
    selectRoute decision first = selectRoute decision second :=
  constantSelector_weaklyConstant (decision source target) first second

/-! ## What identity elimination already forces -/

/-- A genuine identity-elimination principle reflects every route into an
equality of its endpoints.  Arbitrary graph paths and operational traces do
not generally admit this eliminator. -/
theorem identityElimination_implies_endpointReflection
    {Object : Type uObject}
    {layer : Layer.{uObject, uRoute} Object}
    (identityElimination : ExternalPropositionalIdentityElimination layer) :
    EndpointReflection layer := by
  intro source target route
  exact identityElimination.eliminate
    (source := source) (fun endpoint _ => source = endpoint) rfl route

/-! ## The route-family Hedberg argument -/

/-- Normalize a decision-selected route so that the selected reflexive loop is
cancelled.  This repair is what makes the selector fix reflexivity. -/
def normalizedSelector {Object : Type uObject}
    {layer : Layer.{uObject, uRoute} Object}
    (groupoid : RouteGroupoid layer)
    (decision : RouteInhabitationDecision layer)
    {source target : Object} (route : layer.Route source target) :
    layer.Route source target :=
  groupoid.comp
    (groupoid.inv (selectRoute decision (layer.refl source)))
    (selectRoute decision route)

theorem normalizedSelector_refl {Object : Type uObject}
    {layer : Layer.{uObject, uRoute} Object}
    (groupoid : RouteGroupoid layer)
    (decision : RouteInhabitationDecision layer)
    (source : Object) :
    normalizedSelector groupoid decision (layer.refl source) =
      layer.refl source := by
  exact groupoid.inv_comp (selectRoute decision (layer.refl source))

theorem normalizedSelector_weaklyConstant {Object : Type uObject}
    {layer : Layer.{uObject, uRoute} Object}
    (groupoid : RouteGroupoid layer)
    (decision : RouteInhabitationDecision layer)
    {source target : Object}
    (first second : layer.Route source target) :
    normalizedSelector groupoid decision first =
      normalizedSelector groupoid decision second := by
  apply congrArg (fun selected =>
    groupoid.comp
      (groupoid.inv (selectRoute decision (layer.refl source))) selected)
  exact selectRoute_weaklyConstant decision first second

/-- Identity elimination proves that the normalized constant selector is the
identity on every route. -/
theorem normalizedSelector_eq_self {Object : Type uObject}
    {layer : Layer.{uObject, uRoute} Object}
    (groupoid : RouteGroupoid layer)
    (identityElimination : ExternalPropositionalIdentityElimination layer)
    (decision : RouteInhabitationDecision layer)
    {source target : Object} (route : layer.Route source target) :
    normalizedSelector groupoid decision route = route := by
  exact identityElimination.eliminate
    (source := source)
    (fun endpoint candidate =>
      normalizedSelector groupoid decision candidate = candidate)
    (normalizedSelector_refl groupoid decision source)
    route

/-- Route-family Hedberg theorem: identity elimination, groupoid laws, and
decidable route support imply uniqueness of identity routes. -/
theorem hedbergRouteUIP {Object : Type uObject}
    {layer : Layer.{uObject, uRoute} Object}
    (groupoid : RouteGroupoid layer)
    (identityElimination : ExternalPropositionalIdentityElimination layer)
    (decision : RouteInhabitationDecision layer) :
    RouteUIP layer := by
  intro source target
  refine ⟨?_⟩
  intro first second
  calc
    first = normalizedSelector groupoid decision first :=
      (normalizedSelector_eq_self groupoid identityElimination decision first).symm
    _ = normalizedSelector groupoid decision second :=
      normalizedSelector_weaklyConstant groupoid decision first second
    _ = second :=
      normalizedSelector_eq_self groupoid identityElimination decision second

/-! ## Positive and negative controls -/

namespace Canary

open Mettapedia.TypeTheory.IdentityRouteCapabilities.Canary

/-- Lifted ordinary equality has the expected propositional identity
eliminator. -/
def liftedEqualityElimination :
    ExternalPropositionalIdentityElimination liftedEquality where
  eliminate := by
    intro source motive base target route
    rcases route with ⟨equality⟩
    cases equality
    exact base

/-- Route support for lifted Boolean equality is constructively decidable. -/
def liftedEqualityDecision : RouteInhabitationDecision liftedEquality := by
  intro source target
  by_cases equal : source = target
  · exact .present ⟨equal⟩
  · exact .absent (fun route => equal route.down)

/-- Positive control: the generic route-family proof derives UIP for lifted
ordinary equality. -/
theorem liftedEquality_uip_via_hedberg : RouteUIP liftedEquality :=
  hedbergRouteUIP liftedEqualityGroupoid liftedEqualityElimination
    liftedEqualityDecision

/-- The one-object plural route layer has decidable route support. -/
def reflectedPluralDecision : RouteInhabitationDecision reflectedPlural :=
  fun _ _ => .present false

/-- Decidable route support and groupoid operations alone do not imply UIP. -/
theorem decidable_routes_and_groupoid_do_not_imply_uip :
    Nonempty (RouteInhabitationDecision reflectedPlural) ∧
      Nonempty (RouteGroupoid reflectedPlural) ∧
      ¬ RouteUIP reflectedPlural :=
  ⟨⟨reflectedPluralDecision⟩, ⟨reflectedPluralGroupoid⟩,
    reflectedPlural_not_uip⟩

/-- Consequently the plural one-object route family cannot carry the stated
identity eliminator.  Decidable object syntax would not repair this gap. -/
theorem reflectedPlural_has_no_identityElimination :
    ¬ Nonempty
      (ExternalPropositionalIdentityElimination reflectedPlural) := by
  rintro ⟨identityElimination⟩
  exact reflectedPlural_not_uip
    (hedbergRouteUIP reflectedPluralGroupoid identityElimination
      reflectedPluralDecision)

/-- A thin route family between unequal endpoints cannot carry identity
elimination either: thinness is not equality reflection. -/
theorem indiscreteSubsingleton_has_no_identityElimination :
    ¬ Nonempty
      (ExternalPropositionalIdentityElimination indiscreteSubsingleton) := by
  rintro ⟨identityElimination⟩
  exact indiscreteSubsingleton_not_reflects
    (identityElimination_implies_endpointReflection identityElimination)

/-- The four identity-related capabilities therefore remain disciplined:
ordinary equality supplies all three relevant properties, while each
countermodel lacks exactly the evidence needed to treat arbitrary routes as
identity proofs. -/
theorem identity_elimination_admission_matrix :
    Nonempty (ExternalPropositionalIdentityElimination liftedEquality) ∧
      Nonempty (RouteInhabitationDecision liftedEquality) ∧
      EndpointReflection liftedEquality ∧
      RouteUIP liftedEquality ∧
      ¬ Nonempty
        (ExternalPropositionalIdentityElimination reflectedPlural) ∧
      ¬ Nonempty
        (ExternalPropositionalIdentityElimination indiscreteSubsingleton) :=
  ⟨⟨liftedEqualityElimination⟩, ⟨liftedEqualityDecision⟩,
    identityElimination_implies_endpointReflection liftedEqualityElimination,
    liftedEquality_uip_via_hedberg,
    reflectedPlural_has_no_identityElimination,
    indiscreteSubsingleton_has_no_identityElimination⟩

end Canary

/-! ## Axiom audit -/

#print axioms constantSelector_weaklyConstant
#print axioms identityElimination_implies_endpointReflection
#print axioms normalizedSelector_refl
#print axioms normalizedSelector_weaklyConstant
#print axioms normalizedSelector_eq_self
#print axioms hedbergRouteUIP
#print axioms Canary.liftedEquality_uip_via_hedberg
#print axioms Canary.decidable_routes_and_groupoid_do_not_imply_uip
#print axioms Canary.reflectedPlural_has_no_identityElimination
#print axioms Canary.indiscreteSubsingleton_has_no_identityElimination
#print axioms Canary.identity_elimination_admission_matrix

end Mettapedia.TypeTheory.IdentityEliminationCapabilities
