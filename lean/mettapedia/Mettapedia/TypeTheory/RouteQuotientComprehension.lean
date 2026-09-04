import Mettapedia.TypeTheory.RouteFamilyTypeFormers

/-!
# Comprehension for the route-quotient dependent right adjoint

For an extensional family `family` over the route quotient of `context`, the
quotient of the intensional comprehension by the pulled-back family is
equivalent to the extensional dependent total space.  This is the missing
context comparison needed to study preservation of dependent type formers by
the quotient dependent right adjoint.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.RouteQuotientComprehension

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.OperationalIntensionalExtensionalModes
open Mettapedia.TypeTheory.RouteFamilyCwf
open Mettapedia.TypeTheory.RouteFamilyTypeFormers
open Mettapedia.TypeTheory.RouteQuotientDependentRightAdjoint

universe u

/-- The intensional comprehension used below. -/
abbrev PulledExtension (context : RouteType.{u})
    (family : (routeQuotient.obj context).carrier -> Type u) :
    RouteType.{u} :=
  extend context (pullbackReadoutFamily context family)

/-- Send a point of the intensional comprehension to its quotient base point
and unchanged dependent value. -/
def extensionPointReadout (context : RouteType.{u})
    (family : (routeQuotient.obj context).carrier -> Type u)
    (point : (PulledExtension context family).carrier) : Sigma family :=
  ⟨Quot.mk context.Route point.1, point.2⟩

/-- The point readout identifies every declared route of the pulled
comprehension. -/
theorem extensionPointReadout_respects (context : RouteType.{u})
    (family : (routeQuotient.obj context).carrier -> Type u)
    {source target : (PulledExtension context family).carrier}
    (route : (PulledExtension context family).Route source target) :
    extensionPointReadout context family source =
      extensionPointReadout context family target := by
  rcases route with ⟨baseRoute, transported⟩
  let baseEquality : Quot.mk context.Route source.1 =
      Quot.mk context.Route target.1 := Quot.sound baseRoute
  apply Sigma.ext baseEquality
  exact
    (cast_heq (congrArg family baseEquality) source.2).symm.trans
      (heq_of_eq transported)

/-- Quotient the point readout to obtain the canonical comparison from the
quotient comprehension to the extensional dependent total space. -/
def extensionReadout (context : RouteType.{u})
    (family : (routeQuotient.obj context).carrier -> Type u) :
    (routeQuotient.obj (PulledExtension context family)).carrier ->
      Sigma family :=
  Quot.lift (extensionPointReadout context family)
    (fun _ _ route => extensionPointReadout_respects context family route)

/-- Representatives related in the base quotient induce heterogeneously equal
maps from their dependent fibres into the quotient comprehension. -/
theorem extensionRepresentative_coherent (context : RouteType.{u})
    (family : (routeQuotient.obj context).carrier -> Type u)
    {source target : context.carrier} (route : context.Route source target) :
    HEq
      (fun value : family (Quot.mk context.Route source) =>
        Quot.mk (PulledExtension context family).Route
          (⟨source, value⟩ : (PulledExtension context family).carrier))
      (fun value : family (Quot.mk context.Route target) =>
        Quot.mk (PulledExtension context family).Route
          (⟨target, value⟩ : (PulledExtension context family).carrier)) := by
  apply Function.hfunext (congrArg family (Quot.sound route))
  intro sourceValue targetValue valueEquality
  apply heq_of_eq
  apply Quot.sound
  refine ⟨route, ?_⟩
  exact eq_of_heq
    ((cast_heq_iff_heq
      (congrArg family (Quot.sound route)) sourceValue targetValue).2
        valueEquality)

/-- Reconstruct a quotient-comprehension point from an extensional base class
and a value over that class.  Heterogeneous quotient recursion makes the
construction independent of the representative. -/
def extensionReadoutInverse (context : RouteType.{u})
    (family : (routeQuotient.obj context).carrier -> Type u) :
    Sigma family ->
      (routeQuotient.obj (PulledExtension context family)).carrier :=
  fun point =>
    (Quot.hrecOn
      (motive := fun quotient => family quotient ->
        (routeQuotient.obj (PulledExtension context family)).carrier)
      point.1
      (fun representative => fun value =>
        Quot.mk (PulledExtension context family).Route
          (⟨representative, value⟩ :
            (PulledExtension context family).carrier))
      (fun _ _ route =>
        extensionRepresentative_coherent context family route)) point.2

/-- Reading out after reconstruction is the identity on the extensional
dependent total space. -/
theorem extensionReadout_rightInverse (context : RouteType.{u})
    (family : (routeQuotient.obj context).carrier -> Type u) :
    Function.RightInverse (extensionReadoutInverse context family)
      (extensionReadout context family) := by
  rintro ⟨quotient, value⟩
  induction quotient using Quot.ind with
  | _ representative => rfl

/-- Reconstruction after reading out is the identity on the quotient
comprehension. -/
theorem extensionReadout_leftInverse (context : RouteType.{u})
    (family : (routeQuotient.obj context).carrier -> Type u) :
    Function.LeftInverse (extensionReadoutInverse context family)
      (extensionReadout context family) := by
  intro quotient
  induction quotient using Quot.ind with
  | _ point =>
      rcases point with ⟨base, value⟩
      rfl

/-- The quotient of a pulled comprehension is equivalent to the extensional
dependent total space. -/
def extensionReadoutEquiv (context : RouteType.{u})
    (family : (routeQuotient.obj context).carrier -> Type u) :
    (routeQuotient.obj (PulledExtension context family)).carrier ≃
      Sigma family where
  toFun := extensionReadout context family
  invFun := extensionReadoutInverse context family
  left_inv := extensionReadout_leftInverse context family
  right_inv := extensionReadout_rightInverse context family

/-- The forward comparison as an extensional substitution. -/
def extensionReadoutHom (context : RouteType.{u})
    (family : (routeQuotient.obj context).carrier -> Type u) :
    ExtHom (routeQuotient.obj (PulledExtension context family))
      (extCwf.ext (routeQuotient.obj context) family) where
  toFun := extensionReadout context family

/-- The inverse comparison as an extensional substitution. -/
def extensionReadoutInverseHom (context : RouteType.{u})
    (family : (routeQuotient.obj context).carrier -> Type u) :
    ExtHom (extCwf.ext (routeQuotient.obj context) family)
      (routeQuotient.obj (PulledExtension context family)) where
  toFun := extensionReadoutInverse context family

/-- The two comprehension substitutions compose to the identity in the
quotient-comprehension direction. -/
theorem extensionReadoutHom_leftInverse (context : RouteType.{u})
    (family : (routeQuotient.obj context).carrier -> Type u) :
    extCompose (extensionReadoutHom context family)
        (extensionReadoutInverseHom context family) =
      extIdentity (routeQuotient.obj (PulledExtension context family)) := by
  apply ExtHom.ext
  exact extensionReadout_leftInverse context family

/-- The two comprehension substitutions compose to the identity in the
extensional-total-space direction. -/
theorem extensionReadoutHom_rightInverse (context : RouteType.{u})
    (family : (routeQuotient.obj context).carrier -> Type u) :
    extCompose (extensionReadoutInverseHom context family)
        (extensionReadoutHom context family) =
      extIdentity (extCwf.ext (routeQuotient.obj context) family) := by
  apply ExtHom.ext
  exact extensionReadout_rightInverse context family

/-! ## The right action over comprehension -/

/-- Pull an extensional codomain over the dependent total space back along the
comprehension comparison and then through the route quotient. -/
def pullbackExtendedReadoutFamily (context : RouteType.{u})
    (domain : (routeQuotient.obj context).carrier -> Type u)
    (codomain : Sigma domain -> Type u) :
    RouteFamily (PulledExtension context domain) :=
  pullbackReadoutFamily (PulledExtension context domain)
    (extCwf.tySub codomain (extensionReadoutHom context domain))

/-- Extensional dependent summation. -/
def extSigmaFamily {context : ExtType.{u}}
    (domain : context.carrier -> Type u)
    (codomain : Sigma domain -> Type u) : context.carrier -> Type u :=
  fun point => Sigma fun argument : domain point => codomain ⟨point, argument⟩

/-- Extensional dependent functions. -/
def extPiFamily {context : ExtType.{u}}
    (domain : context.carrier -> Type u)
    (codomain : Sigma domain -> Type u) : context.carrier -> Type u :=
  fun point => forall argument : domain point, codomain ⟨point, argument⟩

/-- The canonical dependent-total equality induced by moving a base point
forward and casting its argument. -/
def sigmaTransportIndex {Index : Type u} (domain : Index -> Type u)
    {source target : Index} (equality : source = target)
    (argument : domain source) :
    (⟨source, argument⟩ : Sigma domain) =
      ⟨target, cast (congrArg domain equality) argument⟩ := by
  cases equality
  rfl

/-- Casting a dependent pair along a base equality is the same as casting its
two components in sequence. -/
theorem cast_extSigma {Index : Type u} (domain : Index -> Type u)
    (codomain : Sigma domain -> Type u)
    {source target : Index} (equality : source = target)
    (value : extSigmaFamily domain codomain source) :
    cast (congrArg (extSigmaFamily domain codomain) equality) value =
      ⟨cast (congrArg domain equality) value.1,
        cast (congrArg codomain
          (sigmaTransportIndex domain equality value.1)) value.2⟩ := by
  cases equality
  rcases value with ⟨argument, result⟩
  rfl

/-- The fibres of a pulled extensional codomain are definitionally the
expected codomain fibres at the read-out base and unchanged argument. -/
theorem pullbackExtendedReadoutFamily_fibre (context : RouteType.{u})
    (domain : (routeQuotient.obj context).carrier -> Type u)
    (codomain : Sigma domain -> Type u)
    (point : (PulledExtension context domain).carrier) :
    (pullbackExtendedReadoutFamily context domain codomain).fibre point =
      codomain ⟨Quot.mk context.Route point.1, point.2⟩ :=
  rfl

/-- Fibre formation for dependent sums commutes definitionally with the right
action. -/
theorem sigma_rightAction_fibre (context : RouteType.{u})
    (domain : (routeQuotient.obj context).carrier -> Type u)
    (codomain : Sigma domain -> Type u) (point : context.carrier) :
    (sigmaFamily (pullbackReadoutFamily context domain)
        (pullbackExtendedReadoutFamily context domain codomain)).fibre point =
      (pullbackReadoutFamily context
        (extSigmaFamily domain codomain)).fibre point :=
  rfl

/-- Fibre formation for dependent products commutes definitionally with the
right action. -/
theorem pi_rightAction_fibre (context : RouteType.{u})
    (domain : (routeQuotient.obj context).carrier -> Type u)
    (codomain : Sigma domain -> Type u) (point : context.carrier) :
    (piFamily (pullbackReadoutFamily context domain)
        (pullbackReadoutEquivalenceTransport context domain)
        (pullbackExtendedReadoutFamily context domain codomain)).fibre point =
      (pullbackReadoutFamily context
        (extPiFamily domain codomain)).fibre point :=
  rfl

/-- Dependent-sum transport as well as fibre formation commutes with the right
action. -/
theorem sigma_rightAction (context : RouteType.{u})
    (domain : (routeQuotient.obj context).carrier -> Type u)
    (codomain : Sigma domain -> Type u) :
    sigmaFamily (pullbackReadoutFamily context domain)
        (pullbackExtendedReadoutFamily context domain codomain) =
      pullbackReadoutFamily context (extSigmaFamily domain codomain) := by
  refine RouteFamily.ext (left := sigmaFamily
      (pullbackReadoutFamily context domain)
      (pullbackExtendedReadoutFamily context domain codomain))
    (right := pullbackReadoutFamily context
      (extSigmaFamily domain codomain)) rfl ?_
  apply heq_of_eq
  funext source target route value
  rcases value with ⟨argument, result⟩
  let baseEquality : Quot.mk context.Route source =
      Quot.mk context.Route target := Quot.sound route
  let canonicalIndexEquality :=
    sigmaTransportIndex domain baseEquality argument
  let liftedRoute :
      (PulledExtension context domain).Route
        ⟨source, argument⟩
        ⟨target, cast (congrArg domain baseEquality) argument⟩ :=
    ⟨route, rfl⟩
  have codomainEquality :
      congrArg
          (fun quotient => codomain
            ((extensionReadoutHom context domain).toFun quotient))
          (Quot.sound liftedRoute) =
        congrArg codomain canonicalIndexEquality :=
    Subsingleton.elim _ _
  change
    ⟨cast (congrArg domain baseEquality) argument,
      cast
        (congrArg
          (fun quotient => codomain
            ((extensionReadoutHom context domain).toFun quotient))
          (Quot.sound liftedRoute)) result⟩ =
      cast (congrArg (extSigmaFamily domain codomain) baseEquality)
        ⟨argument, result⟩
  have sigmaCast :
      cast (congrArg (extSigmaFamily domain codomain) baseEquality)
          (⟨argument, result⟩ :
            extSigmaFamily domain codomain
              (Quot.mk context.Route source)) =
        ⟨cast (congrArg domain baseEquality) argument,
          cast (congrArg codomain canonicalIndexEquality) result⟩ :=
    cast_extSigma
      (Index := (routeQuotient.obj context).carrier)
      domain codomain baseEquality ⟨argument, result⟩
  calc
    ⟨cast (congrArg domain baseEquality) argument,
        cast
          (congrArg
            (fun quotient => codomain
              ((extensionReadoutHom context domain).toFun quotient))
            (Quot.sound liftedRoute)) result⟩ =
        ⟨cast (congrArg domain baseEquality) argument,
          cast (congrArg codomain canonicalIndexEquality) result⟩ := by
            rw [codomainEquality]
            rfl
    _ = cast (congrArg (extSigmaFamily domain codomain) baseEquality)
          ⟨argument, result⟩ := sigmaCast.symm

/-- Dependent-product transport as well as fibre formation commutes with the
right action. -/
theorem pi_rightAction (context : RouteType.{u})
    (domain : (routeQuotient.obj context).carrier -> Type u)
    (codomain : Sigma domain -> Type u) :
    piFamily (pullbackReadoutFamily context domain)
        (pullbackReadoutEquivalenceTransport context domain)
        (pullbackExtendedReadoutFamily context domain codomain) =
      pullbackReadoutFamily context (extPiFamily domain codomain) := by
  refine RouteFamily.ext (left := piFamily
      (pullbackReadoutFamily context domain)
      (pullbackReadoutEquivalenceTransport context domain)
      (pullbackExtendedReadoutFamily context domain codomain))
    (right := pullbackReadoutFamily context
      (extPiFamily domain codomain)) rfl ?_
  apply heq_of_eq
  funext source target route value
  apply eq_of_heq
  have leftToSource :
      HEq
        ((piFamily (pullbackReadoutFamily context domain)
          (pullbackReadoutEquivalenceTransport context domain)
          (pullbackExtendedReadoutFamily context domain codomain)).transport
            route value)
        value := by
    apply Function.hfunext
      (congrArg domain (Quot.sound route).symm)
    intro targetArgument sourceArgument argumentEquality
    let inverseArgument :=
      (pullbackReadoutEquivalenceTransport context domain).inverse
        route targetArgument
    let liftedRoute :
        (PulledExtension context domain).Route
          ⟨source, inverseArgument⟩ ⟨target, targetArgument⟩ :=
      ⟨route,
        (pullbackReadoutEquivalenceTransport context domain).transport_inverse
          route targetArgument⟩
    change HEq
      ((pullbackExtendedReadoutFamily context domain codomain).transport
        liftedRoute (value inverseArgument))
      (value sourceArgument)
    have inverseArgumentEquality : inverseArgument = sourceArgument := by
      exact eq_of_heq
        ((cast_heq _ targetArgument).trans argumentEquality)
    exact
      (cast_heq _ (value inverseArgument)).trans
        (congr_arg_heq value inverseArgumentEquality)
  have rightToSource :
      HEq
        ((pullbackReadoutFamily context
          (extPiFamily domain codomain)).transport route value)
        value := by
    apply cast_heq
  exact leftToSource.trans rightToSource.symm

/-! ## Extensional identity under the right action -/

/-- Extensional fibrewise equality over an extensional context. -/
def extIdentityFamily {context : ExtType.{u}}
    (family : context.carrier -> Type u)
    (left right : forall point, family point) :
    context.carrier -> Type u :=
  fun point => ULift (PLift (left point = right point))

/-- Fibre formation for extensional identity commutes definitionally with the
right action. -/
theorem identity_rightAction_fibre (context : RouteType.{u})
    (family : (routeQuotient.obj context).carrier -> Type u)
    (left right : forall point, family point) (point : context.carrier) :
    (identityFamily (pullbackReadoutFamily context family)
        (pullbackSection context family left)
        (pullbackSection context family right)).fibre point =
      (pullbackReadoutFamily context
        (extIdentityFamily family left right)).fibre point :=
  rfl

/-- Extensional-identity transport as well as fibre formation commutes with
the right action. -/
theorem identity_rightAction (context : RouteType.{u})
    (family : (routeQuotient.obj context).carrier -> Type u)
    (left right : forall point, family point) :
    identityFamily (pullbackReadoutFamily context family)
        (pullbackSection context family left)
        (pullbackSection context family right) =
      pullbackReadoutFamily context
        (extIdentityFamily family left right) := by
  refine RouteFamily.ext (left := identityFamily
      (pullbackReadoutFamily context family)
      (pullbackSection context family left)
      (pullbackSection context family right))
    (right := pullbackReadoutFamily context
      (extIdentityFamily family left right)) rfl ?_
  apply heq_of_eq
  funext source target route witness
  exact (liftedEqualitySubsingleton _ _).allEq _ _

#print axioms extensionPointReadout_respects
#print axioms extensionRepresentative_coherent
#print axioms extensionReadoutInverse
#print axioms extensionReadout_rightInverse
#print axioms extensionReadout_leftInverse
#print axioms extensionReadoutEquiv
#print axioms extensionReadoutHom_leftInverse
#print axioms extensionReadoutHom_rightInverse
#print axioms pullbackExtendedReadoutFamily
#print axioms sigma_rightAction_fibre
#print axioms pi_rightAction_fibre
#print axioms sigma_rightAction
#print axioms pi_rightAction
#print axioms identity_rightAction_fibre
#print axioms identity_rightAction

end Mettapedia.TypeTheory.RouteQuotientComprehension
