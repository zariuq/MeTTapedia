import Mettapedia.TypeTheory.IdentityEliminationCapabilities

/-!
# Decidable identity-route structures and operational obstructions

A proof-relevant route family can serve as ordinary identity evidence only
after it earns the relevant identity laws.  This module packages three
standard ingredients:

* groupoid composition and inversion;
* propositional identity elimination from reflexivity; and
* constructive decisions of route-fibre inhabitation.

The existing route-family Hedberg theorem then forces endpoint reflection and
route UIP.  Consequently either of two operational phenomena is an exact
obstruction:

* a route between distinct endpoints; or
* two distinct retained routes in one endpoint fibre.

The result does not choose an identity theory for a language.  It instead
states the admission criterion that any proposed identification of execution
paths, occurrence histories, or revision traces with identity proofs must
satisfy.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DecidableIdentityRouteStructure

open Mettapedia.TypeTheory.ScopedIdentity
open Mettapedia.TypeTheory.IdentityRouteCapabilities
open Mettapedia.TypeTheory.IdentityEliminationCapabilities

universe uObject uRoute

/-- Groupoid laws, identity elimination, and constructive decidability of
route support.  Each component is explicit because dropping any one changes
the resulting criterion. -/
structure Structure {Object : Type uObject}
    (layer : Layer.{uObject, uRoute} Object) where
  groupoid : RouteGroupoid layer
  elimination : ExternalPropositionalIdentityElimination layer
  decision : RouteInhabitationDecision layer

namespace Structure

variable {Object : Type uObject}
variable {layer : Layer.{uObject, uRoute} Object}

/-- Identity elimination alone reflects a route into equality of its
endpoints. -/
theorem endpointReflection (bundle : Structure layer) :
    EndpointReflection layer :=
  identityElimination_implies_endpointReflection bundle.elimination

/-- The complete structure makes every route fibre a subsingleton. -/
theorem routeUIP (bundle : Structure layer) : RouteUIP layer :=
  hedbergRouteUIP bundle.groupoid bundle.elimination bundle.decision

/-- Proposition-valued support retains exact route identity once the route
family satisfies the decidable identity criterion. -/
theorem supportFaithful (bundle : Structure layer) :
    SupportFaithful layer :=
  fun {_source _target} first second _sameSupport =>
    (bundle.routeUIP _source _target).allEq first second

end Structure

/-! ## Exact obstruction properties -/

/-- A retained route connects unequal endpoints. -/
def HasEndpointChangingRoute {Object : Type uObject}
    (layer : Layer.{uObject, uRoute} Object) : Prop :=
  ∃ source target, source ≠ target ∧ Nonempty (layer.Route source target)

/-- One endpoint fibre retains two distinct route witnesses. -/
def HasPluralRouteFibre {Object : Type uObject}
    (layer : Layer.{uObject, uRoute} Object) : Prop :=
  ∃ source target, ∃ first second : layer.Route source target, first ≠ second

/-- The two route phenomena needed by ordinary operational and provenance
semantics: state change or retained history multiplicity. -/
def OperationallyNontrivial {Object : Type uObject}
    (layer : Layer.{uObject, uRoute} Object) : Prop :=
  HasEndpointChangingRoute layer ∨ HasPluralRouteFibre layer

/-- Endpoint-changing routes are incompatible with identity elimination and
hence with the complete decidable identity-route structure. -/
theorem endpointChangingRoute_excludes_structure
    {Object : Type uObject} {layer : Layer.{uObject, uRoute} Object}
    (changes : HasEndpointChangingRoute layer) :
    ¬ Nonempty (Structure layer) := by
  rintro ⟨bundle⟩
  rcases changes with ⟨source, target, different, ⟨route⟩⟩
  exact different (bundle.endpointReflection route)

/-- Retained multiplicity in one route fibre is incompatible with the route
UIP forced by the complete structure. -/
theorem pluralRouteFibre_excludes_structure
    {Object : Type uObject} {layer : Layer.{uObject, uRoute} Object}
    (plural : HasPluralRouteFibre layer) :
    ¬ Nonempty (Structure layer) := by
  rintro ⟨bundle⟩
  rcases plural with ⟨source, target, first, second, different⟩
  exact different ((bundle.routeUIP source target).allEq first second)

/-- Any genuinely state-changing or history-retaining route family fails the
decidable identity-route criterion. -/
theorem operationallyNontrivial_excludes_structure
    {Object : Type uObject} {layer : Layer.{uObject, uRoute} Object}
    (nontrivial : OperationallyNontrivial layer) :
    ¬ Nonempty (Structure layer) := by
  rcases nontrivial with changes | plural
  · exact endpointChangingRoute_excludes_structure changes
  · exact pluralRouteFibre_excludes_structure plural

/-! ## Positive and negative controls -/

namespace Canary

open Mettapedia.TypeTheory.IdentityRouteCapabilities.Canary
open Mettapedia.TypeTheory.IdentityEliminationCapabilities.Canary

/-- Lifted ordinary equality carries the complete decidable identity-route
structure. -/
def liftedEqualityStructure : Structure liftedEquality where
  groupoid := liftedEqualityGroupoid
  elimination := liftedEqualityElimination
  decision := liftedEqualityDecision

theorem liftedEquality_supportFaithful : SupportFaithful liftedEquality :=
  fun {_source _target} first second _sameSupport =>
    (liftedEqualityStructure.routeUIP _source _target).allEq first second

/-- The reflected plural canary retains two distinct self-routes. -/
theorem reflectedPlural_operationallyNontrivial :
    OperationallyNontrivial reflectedPlural := by
  right
  exact ⟨(), (), false, true, Bool.false_ne_true⟩

/-- Therefore its retained histories cannot be ordinary decidable identity
proofs. -/
theorem reflectedPlural_has_no_structure :
    ¬ Nonempty (Structure reflectedPlural) :=
  operationallyNontrivial_excludes_structure
    reflectedPlural_operationallyNontrivial

/-- The indiscrete thin canary has only one route per fibre but connects
distinct Boolean endpoints. -/
theorem indiscreteSubsingleton_operationallyNontrivial :
    OperationallyNontrivial indiscreteSubsingleton := by
  left
  exact ⟨false, true, Bool.false_ne_true, ⟨PUnit.unit⟩⟩

/-- Thinness alone does not turn state-changing paths into identity proofs. -/
theorem indiscreteSubsingleton_has_no_structure :
    ¬ Nonempty (Structure indiscreteSubsingleton) :=
  operationallyNontrivial_excludes_structure
    indiscreteSubsingleton_operationallyNontrivial

/-- The admission matrix contains one positive ordinary-equality instance and
both independent operational obstructions. -/
theorem identityRoute_admission_matrix :
    Nonempty (Structure liftedEquality) ∧
      SupportFaithful liftedEquality ∧
      ¬ Nonempty (Structure reflectedPlural) ∧
      ¬ Nonempty (Structure indiscreteSubsingleton) :=
  ⟨⟨liftedEqualityStructure⟩,
    (fun {_source _target} first second _sameSupport =>
      (liftedEqualityStructure.routeUIP _source _target).allEq first second),
    reflectedPlural_has_no_structure,
    indiscreteSubsingleton_has_no_structure⟩

end Canary

#print axioms Structure.endpointReflection
#print axioms Structure.routeUIP
#print axioms Structure.supportFaithful
#print axioms endpointChangingRoute_excludes_structure
#print axioms pluralRouteFibre_excludes_structure
#print axioms operationallyNontrivial_excludes_structure
#print axioms Canary.identityRoute_admission_matrix

end Mettapedia.TypeTheory.DecidableIdentityRouteStructure
