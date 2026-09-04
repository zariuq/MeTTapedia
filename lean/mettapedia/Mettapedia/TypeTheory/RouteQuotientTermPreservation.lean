import Mettapedia.TypeTheory.RouteQuotientComprehension

/-!
# Term preservation for the route-quotient dependent right adjoint

The comprehension comparison preserves type formation for dependent sums,
the admissible dependent products, and extensional fibrewise identity.  This
module carries the corresponding term constructors through the same
comparison.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.RouteQuotientTermPreservation

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualProductComparison
open Mettapedia.TypeTheory.OperationalIntensionalExtensionalModes
open Mettapedia.TypeTheory.RouteFamilyCwf
open Mettapedia.TypeTheory.RouteFamilyTypeFormers
open Mettapedia.TypeTheory.RouteQuotientDependentRightAdjoint
open Mettapedia.TypeTheory.RouteQuotientComprehension

universe u

/-- Transport a route-natural section across equality of its route families. -/
def castRouteSection {context : RouteType.{u}}
    {left right : RouteFamily context} (equality : left = right) :
    RouteSection left -> RouteSection right := by
  cases equality
  exact id

/-- Casting a section across family equality does not change its values,
heterogeneously. -/
theorem castRouteSection_value {context : RouteType.{u}}
    {left right : RouteFamily context} (equality : left = right)
    (term : RouteSection left) :
    HEq (castRouteSection equality term).value term.value := by
  cases equality
  rfl

/-- Two sections agree after a family cast when their value functions agree
heterogeneously. -/
theorem castRouteSection_eq_of_value {context : RouteType.{u}}
    {left right : RouteFamily context} (equality : left = right)
    (leftTerm : RouteSection left) (rightTerm : RouteSection right)
    (sameValue : HEq leftTerm.value rightTerm.value) :
    castRouteSection equality leftTerm = rightTerm := by
  cases equality
  apply RouteSection.ext
  exact eq_of_heq sameValue

/-- Extensional dependent-pair introduction. -/
def extSigmaPair {context : ExtType.{u}}
    {domain : context.carrier -> Type u}
    {codomain : Sigma domain -> Type u}
    (first : forall point, domain point)
    (second : forall point, codomain ⟨point, first point⟩) :
    forall point, extSigmaFamily domain codomain point :=
  fun point => ⟨first point, second point⟩

/-- Pull the second component of an extensional dependent pair into the
substituted codomain expected by route-family pair introduction. -/
def pullbackSigmaSecond (context : RouteType.{u})
    (domain : (routeQuotient.obj context).carrier -> Type u)
    (codomain : Sigma domain -> Type u)
    (first : forall point, domain point)
    (second : forall point, codomain ⟨point, first point⟩) :
    RouteSection
      (routeCwf.tySub
        (pullbackExtendedReadoutFamily context domain codomain)
        (selfExtend routeCwf (pullbackSection context domain first))) where
  value point := second (Quot.mk context.Route point)
  natural {source target} route := by
    let equality : Quot.mk context.Route source =
        Quot.mk context.Route target := Quot.sound route
    change
      cast
          (congrArg
            (fun quotient => codomain ⟨quotient, first quotient⟩)
            equality)
          (second (Quot.mk context.Route source)) =
        second (Quot.mk context.Route target)
    exact dependentSection_transport second equality

/-- Pair introduction commutes with the dependent right action, including the
transport equality between the two sum families. -/
theorem sigmaPair_rightAction (context : RouteType.{u})
    (domain : (routeQuotient.obj context).carrier -> Type u)
    (codomain : Sigma domain -> Type u)
    (first : forall point, domain point)
    (second : forall point, codomain ⟨point, first point⟩) :
    castRouteSection (sigma_rightAction context domain codomain)
        (sigmaPair (pullbackSection context domain first)
          (pullbackSigmaSecond context domain codomain first second)) =
      pullbackSection context (extSigmaFamily domain codomain)
        (extSigmaPair first second) := by
  apply castRouteSection_eq_of_value
  rfl

/-- Regard the pullback of an extensional sum term as a term of the
route-family sum by using the inverse formation comparison. -/
def pullbackSigmaTerm (context : RouteType.{u})
    (domain : (routeQuotient.obj context).carrier -> Type u)
    (codomain : Sigma domain -> Type u)
    (term : forall point, extSigmaFamily domain codomain point) :
    RouteSection
      (sigmaFamily (pullbackReadoutFamily context domain)
        (pullbackExtendedReadoutFamily context domain codomain)) :=
  castRouteSection (sigma_rightAction context domain codomain).symm
    (pullbackSection context (extSigmaFamily domain codomain) term)

/-- The inverse formation comparison leaves the pointwise value of a pulled
sum term unchanged. -/
theorem pullbackSigmaTerm_value (context : RouteType.{u})
    (domain : (routeQuotient.obj context).carrier -> Type u)
    (codomain : Sigma domain -> Type u)
    (term : forall point, extSigmaFamily domain codomain point)
    (point : context.carrier) :
    (pullbackSigmaTerm context domain codomain term).value point =
      term (Quot.mk context.Route point) := by
  have sameValues :
      (pullbackSigmaTerm context domain codomain term).value =
        (pullbackSection context (extSigmaFamily domain codomain) term).value :=
    eq_of_heq
      (castRouteSection_value
        (sigma_rightAction context domain codomain).symm
        (pullbackSection context (extSigmaFamily domain codomain) term))
  exact congrFun sameValues point

/-- First projection commutes with the dependent right action. -/
theorem sigmaFst_rightAction (context : RouteType.{u})
    (domain : (routeQuotient.obj context).carrier -> Type u)
    (codomain : Sigma domain -> Type u)
    (term : forall point, extSigmaFamily domain codomain point) :
    sigmaFst (pullbackSigmaTerm context domain codomain term) =
      pullbackSection context domain (fun point => (term point).1) := by
  apply RouteSection.ext
  funext point
  exact congrArg Sigma.fst
    (pullbackSigmaTerm_value context domain codomain term point)

/-- The first-projection comparison induces equality of the two substituted
codomain families in which the second projections live. -/
def sigmaSndFamilyEquality (context : RouteType.{u})
    (domain : (routeQuotient.obj context).carrier -> Type u)
    (codomain : Sigma domain -> Type u)
    (term : forall point, extSigmaFamily domain codomain point) :
    routeCwf.tySub
        (pullbackExtendedReadoutFamily context domain codomain)
        (selfExtend routeCwf
          (sigmaFst (pullbackSigmaTerm context domain codomain term))) =
      routeCwf.tySub
        (pullbackExtendedReadoutFamily context domain codomain)
        (selfExtend routeCwf
          (pullbackSection context domain (fun point => (term point).1))) :=
  congrArg
    (fun first : RouteSection (pullbackReadoutFamily context domain) =>
      routeCwf.tySub
        (pullbackExtendedReadoutFamily context domain codomain)
        (selfExtend routeCwf first))
    (sigmaFst_rightAction context domain codomain term)

/-- Second projection commutes with the dependent right action after the
substituted codomain is transported along first-projection preservation. -/
theorem sigmaSnd_rightAction (context : RouteType.{u})
    (domain : (routeQuotient.obj context).carrier -> Type u)
    (codomain : Sigma domain -> Type u)
    (term : forall point, extSigmaFamily domain codomain point) :
    castRouteSection (sigmaSndFamilyEquality context domain codomain term)
        (sigmaSnd (pullbackSigmaTerm context domain codomain term)) =
      pullbackSigmaSecond context domain codomain
        (fun point => (term point).1) (fun point => (term point).2) := by
  apply castRouteSection_eq_of_value
  apply Function.hfunext rfl
  intro point otherPoint pointEquality
  cases pointEquality
  exact
    (Sigma.mk.inj_iff.mp
      (pullbackSigmaTerm_value context domain codomain term point)).2

/-! ## Dependent functions -/

/-- Pull an extensional section over a dependent total space back through the
comprehension comparison. -/
def pullbackExtendedSection (context : RouteType.{u})
    (domain : (routeQuotient.obj context).carrier -> Type u)
    (codomain : Sigma domain -> Type u)
    (term : forall point, codomain point) :
    RouteSection (pullbackExtendedReadoutFamily context domain codomain) :=
  pullbackSection (PulledExtension context domain)
    (extCwf.tySub codomain (extensionReadoutHom context domain))
    (fun quotient => term ((extensionReadoutHom context domain).toFun quotient))

/-- Extensional lambda abstraction. -/
def extPiLam {context : ExtType.{u}}
    {domain : context.carrier -> Type u}
    {codomain : Sigma domain -> Type u}
    (body : forall point, codomain point) :
    forall point, extPiFamily domain codomain point :=
  fun point argument => body ⟨point, argument⟩

/-- Lambda abstraction commutes with the dependent right action. -/
theorem piLam_rightAction (context : RouteType.{u})
    (domain : (routeQuotient.obj context).carrier -> Type u)
    (codomain : Sigma domain -> Type u)
    (body : forall point, codomain point) :
    castRouteSection (pi_rightAction context domain codomain)
        (piLam (pullbackReadoutEquivalenceTransport context domain)
          (pullbackExtendedSection context domain codomain body)) =
      pullbackSection context (extPiFamily domain codomain)
        (extPiLam body) := by
  apply castRouteSection_eq_of_value
  rfl

/-- Regard the pullback of an extensional dependent function as a term of the
route-family product by using the inverse formation comparison. -/
def pullbackPiTerm (context : RouteType.{u})
    (domain : (routeQuotient.obj context).carrier -> Type u)
    (codomain : Sigma domain -> Type u)
    (term : forall point, extPiFamily domain codomain point) :
    RouteSection
      (piFamily (pullbackReadoutFamily context domain)
        (pullbackReadoutEquivalenceTransport context domain)
        (pullbackExtendedReadoutFamily context domain codomain)) :=
  castRouteSection (pi_rightAction context domain codomain).symm
    (pullbackSection context (extPiFamily domain codomain) term)

/-- The inverse formation comparison leaves the pointwise value of a pulled
dependent function unchanged. -/
theorem pullbackPiTerm_value (context : RouteType.{u})
    (domain : (routeQuotient.obj context).carrier -> Type u)
    (codomain : Sigma domain -> Type u)
    (term : forall point, extPiFamily domain codomain point)
    (point : context.carrier) :
    (pullbackPiTerm context domain codomain term).value point =
      term (Quot.mk context.Route point) := by
  have sameValues :
      (pullbackPiTerm context domain codomain term).value =
        (pullbackSection context (extPiFamily domain codomain) term).value :=
    eq_of_heq
      (castRouteSection_value
        (pi_rightAction context domain codomain).symm
        (pullbackSection context (extPiFamily domain codomain) term))
  exact congrFun sameValues point

/-- Extensional dependent application. -/
def extPiApp {context : ExtType.{u}}
    {domain : context.carrier -> Type u}
    {codomain : Sigma domain -> Type u}
    (function : forall point, extPiFamily domain codomain point)
    (argument : forall point, domain point) :
    forall point, codomain ⟨point, argument point⟩ :=
  fun point => function point (argument point)

/-- Application commutes with the dependent right action. -/
theorem piApp_rightAction (context : RouteType.{u})
    (domain : (routeQuotient.obj context).carrier -> Type u)
    (codomain : Sigma domain -> Type u)
    (function : forall point, extPiFamily domain codomain point)
    (argument : forall point, domain point) :
    piApp (pullbackReadoutEquivalenceTransport context domain)
        (pullbackPiTerm context domain codomain function)
        (pullbackSection context domain argument) =
      pullbackSigmaSecond context domain codomain argument
        (extPiApp function argument) := by
  apply RouteSection.ext
  funext point
  exact congrFun
    (pullbackPiTerm_value context domain codomain function point)
    (argument (Quot.mk context.Route point))

/-! ## Extensional identity -/

/-- Extensional fibrewise reflexivity. -/
def extIdentityRefl {context : ExtType.{u}}
    {family : context.carrier -> Type u}
    (term : forall point, family point) :
    forall point, extIdentityFamily family term term point :=
  fun _ => ⟨⟨rfl⟩⟩

/-- Reflexivity commutes with the dependent right action. -/
theorem identityRefl_rightAction (context : RouteType.{u})
    (family : (routeQuotient.obj context).carrier -> Type u)
    (term : forall point, family point) :
    castRouteSection (identity_rightAction context family term term)
        (routeIdentityReflexivity.refl
          (pullbackSection context family term)) =
      pullbackSection context (extIdentityFamily family term term)
        (extIdentityRefl term) := by
  apply castRouteSection_eq_of_value
  rfl

#print axioms castRouteSection
#print axioms castRouteSection_value
#print axioms castRouteSection_eq_of_value
#print axioms pullbackSigmaSecond
#print axioms sigmaPair_rightAction
#print axioms pullbackSigmaTerm
#print axioms pullbackSigmaTerm_value
#print axioms sigmaFst_rightAction
#print axioms sigmaSndFamilyEquality
#print axioms sigmaSnd_rightAction
#print axioms pullbackExtendedSection
#print axioms piLam_rightAction
#print axioms pullbackPiTerm
#print axioms pullbackPiTerm_value
#print axioms piApp_rightAction
#print axioms identityRefl_rightAction

end Mettapedia.TypeTheory.RouteQuotientTermPreservation
