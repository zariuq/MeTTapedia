import Mettapedia.GSLT.Core.ContextualTypeReindexing
import Mettapedia.TypeTheory.ContextualIdentityTypes
import Mettapedia.TypeTheory.ContextualSumComparison
import Mettapedia.TypeTheory.RouteQuotientDependentRightAdjoint

/-!
# Dependent type formers for route families

The CwF of route-indexed families supports dependent sums and fibrewise
identity types using only forward route transport.  Dependent products have a
different variance requirement: moving a function forward along a route
requires pulling its target argument back.  They therefore exist when the
domain family has fibrewise invertible transport, including every family
pulled back from the extensional route quotient.

This module keeps that boundary explicit.  It does not install a dependent
product on arbitrary covariant route families.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.RouteFamilyTypeFormers

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.GSLT.Core.ContextualLadder.TypeOver
open Mettapedia.TypeTheory.ContextualIdentityTypes
open Mettapedia.TypeTheory.ContextualProductComparison
open Mettapedia.TypeTheory.ContextualSumComparison
open Mettapedia.TypeTheory.OperationalIntensionalExtensionalModes
open Mettapedia.TypeTheory.RouteFamilyCwf
open Mettapedia.TypeTheory.RouteQuotientDependentRightAdjoint

universe u

/-! ## Canonical lifting of a route substitution -/

/-- The display-map pullback leg for route families, written concretely. -/
def liftRouteSubstitution {source target : RouteType.{u}}
    (substitution : RouteHom source target) (family : RouteFamily target) :
    RouteHom (extend source (family.reindex substitution))
      (extend target family) where
  toFun point := ⟨substitution.toFun point.1, point.2⟩
  map_route route := by
    rcases route with ⟨baseRoute, transported⟩
    exact ⟨substitution.map_route baseRoute, transported⟩

/-- The concrete route-family lifting is the generic CwF extension
substitution. -/
theorem liftRouteSubstitution_eq_extensionSubstitution
    {source target : RouteType.{u}}
    (substitution : RouteHom source target) (family : RouteFamily target) :
    liftRouteSubstitution substitution family =
      extensionSubstitution (C := routeCwf) substitution family := by
  apply RouteHom.ext
  intro point
  rfl

/-! ## Dependent sums -/

/-- Fibrewise dependent summation, transported covariantly along routes. -/
def sigmaFamily {context : RouteType.{u}} (domain : RouteFamily context)
    (codomain : RouteFamily (extend context domain)) : RouteFamily context where
  fibre point := Sigma fun argument : domain.fibre point =>
    codomain.fibre ⟨point, argument⟩
  transport {source target} route value :=
    ⟨domain.transport route value.1,
      codomain.transport ⟨route, rfl⟩ value.2⟩
  transport_refl point value := by
    rcases value with ⟨argument, result⟩
    let forwardRoute :
        (extend context domain).Route ⟨point, argument⟩
          ⟨point, domain.transport (context.route_refl point) argument⟩ :=
      ⟨context.route_refl point, rfl⟩
    apply Sigma.ext (domain.transport_refl point argument)
    change HEq (codomain.transport forwardRoute result) result
    have transportCongruence :
        HEq
          (codomain.transport forwardRoute result)
          (codomain.transport
            ((extend context domain).route_refl ⟨point, argument⟩)
            result) := by
      congr
      · exact domain.transport_refl point argument
      · apply proof_irrel_heq
    exact transportCongruence.trans
      (heq_of_eq (codomain.transport_refl ⟨point, argument⟩ result))

/-- Introduction for route-family dependent sums. -/
def sigmaPair {context : RouteType.{u}} {domain : RouteFamily context}
    {codomain : RouteFamily (extend context domain)}
    (first : RouteSection domain)
    (second : routeCwf.Tm context
      (routeCwf.tySub codomain (selfExtend routeCwf first))) :
    RouteSection (sigmaFamily domain codomain) where
  value point := ⟨first.value point, second.value point⟩
  natural {source target} route := by
    let forwardRoute :
        (extend context domain).Route
          ⟨source, first.value source⟩
          ⟨target, domain.transport route (first.value source)⟩ :=
      ⟨route, rfl⟩
    apply Sigma.ext (first.natural route)
    change HEq
      (codomain.transport forwardRoute (second.value source))
      (second.value target)
    have transportCongruence :
        HEq
          (codomain.transport forwardRoute (second.value source))
          (codomain.transport
            ((selfExtend routeCwf first).map_route route)
            (second.value source)) := by
      congr
      · simpa using first.natural route
      · apply proof_irrel_heq
    exact transportCongruence.trans (heq_of_eq (second.natural route))

/-- First projection of a route-family dependent sum. -/
def sigmaFst {context : RouteType.{u}} {domain : RouteFamily context}
    {codomain : RouteFamily (extend context domain)}
    (value : RouteSection (sigmaFamily domain codomain)) :
    RouteSection domain where
  value point := (value.value point).1
  natural route := congrArg Sigma.fst (value.natural route)

/-- Second projection of a route-family dependent sum. -/
def sigmaSnd {context : RouteType.{u}} {domain : RouteFamily context}
    {codomain : RouteFamily (extend context domain)}
    (value : RouteSection (sigmaFamily domain codomain)) :
    routeCwf.Tm context
      (routeCwf.tySub codomain
        (selfExtend routeCwf (sigmaFst value))) where
  value point := (value.value point).2
  natural {source target} route := by
    let forwardRoute :
        (extend context domain).Route
          ⟨source, (value.value source).1⟩
          ⟨target, domain.transport route (value.value source).1⟩ :=
      ⟨route, rfl⟩
    have wholeNatural := value.natural route
    have secondNatural := (Sigma.mk.inj_iff.mp wholeNatural).2
    change
      codomain.transport
          ((selfExtend routeCwf (sigmaFst value)).map_route route)
          (value.value source).2 =
        (value.value target).2
    have transportCongruence :
        HEq
          (codomain.transport
            ((selfExtend routeCwf (sigmaFst value)).map_route route)
            (value.value source).2)
          (codomain.transport forwardRoute (value.value source).2) := by
      congr
      · exact Sigma.ext rfl
          (heq_of_eq (congrArg Sigma.fst wholeNatural).symm)
      · apply proof_irrel_heq
    apply eq_of_heq
    exact transportCongruence.trans secondNatural

/-- Route families carry the full beta fragment of dependent sums. -/
def routeDependentSums : DependentSumBeta routeCwf where
  sigma := sigmaFamily
  pair := sigmaPair
  fst := sigmaFst
  snd := sigmaSnd
  fst_pair first second := by
    apply RouteSection.ext
    rfl
  snd_pair first second := by
    exact HEq.rfl

/-- Dependent-sum formation commutes with route substitution. -/
theorem sigmaFamily_reindex {source target : RouteType.{u}}
    (domain : RouteFamily target)
    (codomain : RouteFamily (extend target domain))
    (substitution : RouteHom source target) :
    (sigmaFamily domain codomain).reindex substitution =
      sigmaFamily (domain.reindex substitution)
        (codomain.reindex (liftRouteSubstitution substitution domain)) := by
  rfl

/-! ## Fibrewise extensional identity -/

/-- Lifted equality proofs form a subsingleton without adding proof
irrelevance as an object-language rule. -/
@[reducible] def liftedEqualitySubsingleton {Value : Type u}
    (left right : Value) :
    Subsingleton (ULift (PLift (left = right))) where
  allEq first second := by
    rcases first with ⟨⟨firstProof⟩⟩
    rcases second with ⟨⟨secondProof⟩⟩
    have sameProof : firstProof = secondProof := Subsingleton.elim _ _
    cases sameProof
    rfl

/-- Equality in each fibre, transported using naturality of its endpoints. -/
def identityFamily {context : RouteType.{u}} (family : RouteFamily context)
    (left right : RouteSection family) : RouteFamily context where
  fibre point := ULift (PLift (left.value point = right.value point))
  transport route witness :=
    ⟨⟨(left.natural route).symm.trans
      ((congrArg (family.transport route) witness.down.down).trans
        (right.natural route))⟩⟩
  transport_refl _ _ := Subsingleton.elim _ _

/-- Fibrewise equality is substitution-stable identity formation on the
route-family CwF. -/
def routeIdentityFormation : IdentityFormation routeCwf where
  idTy := identityFamily
  idTy_sub _ _ _ _ := rfl

/-- Reflexivity is a route-natural term of fibrewise equality. -/
def routeIdentityReflexivity :
    IdentityReflexivity routeCwf routeIdentityFormation where
  refl _term :=
    { value := fun _ => ⟨⟨rfl⟩⟩
      natural := fun _ =>
        (liftedEqualitySubsingleton _ _).allEq _ _ }
  refl_sub := by
    intro source target substitution family term
    exact HEq.rfl

/-- Fibrewise equality proofs are propositionally irrelevant in this
particular semantic identity structure. -/
theorem routeIdentityProofIrrelevance :
    IdentityProofIrrelevance routeCwf routeIdentityFormation := by
  intro context family left right
  constructor
  intro first second
  apply RouteSection.ext
  funext point
  exact (liftedEqualitySubsingleton _ _).allEq _ _

/-- An inhabited fibrewise identity type reflects equality of route-natural
sections. -/
theorem routeIdentityEndpointReflection :
    IdentityEndpointReflection routeCwf routeIdentityFormation := by
  intro context family left right witness
  apply RouteSection.ext
  funext point
  exact (witness.value point).down.down

/-! ## Dependent products with invertible domain transport -/

/-- A route family has fibrewise equivalence transport when every selected
forward transport map is the forward function of an equivalence. -/
structure FibrewiseEquivalenceTransport {context : RouteType.{u}}
    (family : RouteFamily context) : Type (u + 1) where
  equivalence : {source target : context.carrier} ->
    (route : context.Route source target) ->
      family.fibre source ≃ family.fibre target
  apply_eq_transport : forall {source target : context.carrier}
    (route : context.Route source target) (value : family.fibre source),
    equivalence route value = family.transport route value

namespace FibrewiseEquivalenceTransport

/-- Pullback preserves fibrewise equivalence transport. -/
def reindex {source target : RouteType.{u}} {family : RouteFamily target}
    (transportStructure : FibrewiseEquivalenceTransport family)
    (substitution : RouteHom source target) :
    FibrewiseEquivalenceTransport (family.reindex substitution) where
  equivalence route := transportStructure.equivalence
    (substitution.map_route route)
  apply_eq_transport _ _ := transportStructure.apply_eq_transport _ _

/-- Transport a target value backward using the inverse equivalence. -/
def inverse {context : RouteType.{u}} {family : RouteFamily context}
    (transportStructure : FibrewiseEquivalenceTransport family)
    {source target : context.carrier} (route : context.Route source target)
    (value : family.fibre target) : family.fibre source :=
  (transportStructure.equivalence route).symm value

/-- Forward transport after inverse transport returns the target value. -/
theorem transport_inverse {context : RouteType.{u}}
    {family : RouteFamily context}
    (transportStructure : FibrewiseEquivalenceTransport family)
    {source target : context.carrier} (route : context.Route source target)
    (value : family.fibre target) :
    family.transport route (transportStructure.inverse route value) = value := by
  rw [← transportStructure.apply_eq_transport]
  exact (transportStructure.equivalence route).apply_symm_apply value

/-- Inverse transport after forward transport returns the source value. -/
theorem inverse_transport {context : RouteType.{u}}
    {family : RouteFamily context}
    (transportStructure : FibrewiseEquivalenceTransport family)
    {source target : context.carrier} (route : context.Route source target)
    (value : family.fibre source) :
    transportStructure.inverse route (family.transport route value) = value := by
  rw [← transportStructure.apply_eq_transport]
  exact (transportStructure.equivalence route).symm_apply_apply value

/-- Constant route families have identity equivalence transport. -/
def constant (context : RouteType.{u}) (valueType : Type u) :
    FibrewiseEquivalenceTransport (RouteFamily.constant context valueType) where
  equivalence _ := Equiv.refl valueType
  apply_eq_transport _ _ := rfl

end FibrewiseEquivalenceTransport

/-- A quotient-pulled family transports by equality casts, hence by
equivalences. -/
def pullbackReadoutEquivalenceTransport (context : RouteType.{u})
    (family : (routeQuotient.obj context).carrier -> Type u) :
    FibrewiseEquivalenceTransport (pullbackReadoutFamily context family) where
  equivalence route := Equiv.cast (congrArg family (Quot.sound route))
  apply_eq_transport _ _ := rfl

/-- Pointwise dependent functions form a route family whenever domain
transport is fibrewise invertible. -/
def piFamily {context : RouteType.{u}} (domain : RouteFamily context)
    (domainTransport : FibrewiseEquivalenceTransport domain)
    (codomain : RouteFamily (extend context domain)) : RouteFamily context where
  fibre point := forall argument : domain.fibre point,
    codomain.fibre ⟨point, argument⟩
  transport {source target} route function targetArgument :=
    codomain.transport
      ⟨route, domainTransport.transport_inverse route targetArgument⟩
      (function (domainTransport.inverse route targetArgument))
  transport_refl point function := by
    funext argument
    let route := context.route_refl point
    let inverseArgument := domainTransport.inverse route argument
    have inverseRefl : inverseArgument = argument := by
      calc
        inverseArgument =
            domainTransport.inverse route
              (domain.transport route argument) :=
          congrArg (domainTransport.inverse route)
            (domain.transport_refl point argument).symm
        _ = argument := domainTransport.inverse_transport route argument
    let forwardRoute :
        (extend context domain).Route ⟨point, inverseArgument⟩
          ⟨point, argument⟩ :=
      ⟨route, domainTransport.transport_inverse route argument⟩
    have transportCongruence :
        HEq
          (codomain.transport forwardRoute (function inverseArgument))
          (codomain.transport
            ((extend context domain).route_refl ⟨point, argument⟩)
            (function argument)) := by
      congr
      · apply proof_irrel_heq
    exact eq_of_heq
      (transportCongruence.trans
        (heq_of_eq
          (codomain.transport_refl ⟨point, argument⟩
            (function argument))))

/-- Lambda abstraction for products with invertible domain transport. -/
def piLam {context : RouteType.{u}} {domain : RouteFamily context}
    (domainTransport : FibrewiseEquivalenceTransport domain)
    {codomain : RouteFamily (extend context domain)}
    (body : RouteSection codomain) :
    RouteSection (piFamily domain domainTransport codomain) where
  value point argument := body.value ⟨point, argument⟩
  natural {source target} route := by
    funext targetArgument
    exact body.natural
      ⟨route, domainTransport.transport_inverse route targetArgument⟩

/-- Application for products with invertible domain transport. -/
def piApp {context : RouteType.{u}} {domain : RouteFamily context}
    (domainTransport : FibrewiseEquivalenceTransport domain)
    {codomain : RouteFamily (extend context domain)}
    (function : RouteSection (piFamily domain domainTransport codomain))
    (argument : RouteSection domain) :
    routeCwf.Tm context
      (routeCwf.tySub codomain (selfExtend routeCwf argument)) where
  value point := function.value point (argument.value point)
  natural {source target} route := by
    let inverseArgument :=
      domainTransport.inverse route (argument.value target)
    have inverseNatural : inverseArgument = argument.value source := by
      calc
        inverseArgument = domainTransport.inverse route
            (domain.transport route (argument.value source)) :=
          congrArg (domainTransport.inverse route)
            (argument.natural route).symm
        _ = argument.value source :=
          domainTransport.inverse_transport route (argument.value source)
    let backwardRoute :
        (extend context domain).Route ⟨source, inverseArgument⟩
          ⟨target, argument.value target⟩ :=
      ⟨route,
        domainTransport.transport_inverse route (argument.value target)⟩
    have functionNatural :=
      congrFun (function.natural route) (argument.value target)
    change
      codomain.transport ((selfExtend routeCwf argument).map_route route)
          (function.value source (argument.value source)) =
        function.value target (argument.value target)
    have transportCongruence :
        HEq
          (codomain.transport
            ((selfExtend routeCwf argument).map_route route)
            (function.value source (argument.value source)))
          (codomain.transport backwardRoute
            (function.value source inverseArgument)) := by
      congr
      · exact congrArg
          (fun value => (⟨source, value⟩ : Sigma domain.fibre))
          inverseNatural.symm
      · apply proof_irrel_heq
      · exact congr_arg_heq (function.value source) inverseNatural.symm
    exact eq_of_heq
      (transportCongruence.trans (heq_of_eq functionNatural))

/-- Beta computation for the restricted dependent product is judgmental in
the semantic model. -/
theorem pi_beta {context : RouteType.{u}} {domain : RouteFamily context}
    (domainTransport : FibrewiseEquivalenceTransport domain)
    {codomain : RouteFamily (extend context domain)}
    (body : RouteSection codomain) (argument : RouteSection domain) :
    piApp domainTransport (piLam domainTransport body) argument =
      routeCwf.tmSub body (selfExtend routeCwf argument) := by
  apply RouteSection.ext
  rfl

/-- Restricted dependent-product formation commutes with substitution. -/
theorem piFamily_reindex {source target : RouteType.{u}}
    (domain : RouteFamily target)
    (domainTransport : FibrewiseEquivalenceTransport domain)
    (codomain : RouteFamily (extend target domain))
    (substitution : RouteHom source target) :
    (piFamily domain domainTransport codomain).reindex substitution =
      piFamily (domain.reindex substitution)
        (domainTransport.reindex substitution)
        (codomain.reindex (liftRouteSubstitution substitution domain)) := by
  rfl

/-! ## Positive and negative product controls -/

namespace Canary

/-- The earlier codiscrete varying family does not have equivalence
transport: its route from `false` to `true` would require an equivalence from
`PUnit` to `Bool`. -/
theorem codiscreteVaryingFamily_not_equivalenceTransport :
    ¬ Nonempty
      (FibrewiseEquivalenceTransport
        RouteFamilyCwf.Canary.codiscreteVaryingFamily) := by
  rintro ⟨transportStructure⟩
  exact RouteFamilyCwf.Canary.codiscreteVaryingFamily_fibres_not_equiv
    ⟨transportStructure.equivalence (show codiscretePair.Route false true from
      trivial)⟩

/-- A two-point base with one directed nonidentity route. -/
inductive DirectedRoute : Bool -> Bool -> Prop
  | refl (point : Bool) : DirectedRoute point point
  | forward : DirectedRoute false true

/-- The directed two-point route context. -/
def directedPair : RouteType where
  carrier := Bool
  Route := DirectedRoute
  route_refl := DirectedRoute.refl

/-- A covariant domain whose forward route includes `PUnit` into `Bool` at
`false`; the target value `true` has no preimage. -/
def directedVaryingDomain : RouteFamily directedPair where
  fibre
    | false => PUnit
    | true => Bool
  transport {source target} _ := by
    cases source <;> cases target
    · exact id
    · exact fun _ => false
    · exact fun _ => PUnit.unit
    · exact id
  transport_refl point value := by
    cases point <;> rfl

/-- The missing target argument is not connected to the source point in the
dependent total route context. -/
theorem noRoute_source_to_missing :
    ¬ (extend directedPair directedVaryingDomain).Route
      ⟨false, PUnit.unit⟩ ⟨true, true⟩ := by
  rintro ⟨baseRoute, transported⟩
  cases baseRoute with
  | forward => exact Bool.false_ne_true transported

/-- Nor can the transported target argument reach the missing one by a
reflexive base route. -/
theorem noRoute_transported_to_missing :
    ¬ (extend directedPair directedVaryingDomain).Route
      ⟨true, false⟩ ⟨true, true⟩ := by
  rintro ⟨baseRoute, transported⟩
  cases baseRoute with
  | refl point => exact Bool.false_ne_true transported

/-- A dependent codomain inhabited at the source and at the transported
target argument, but empty at the target argument outside the transport
image. -/
def missingPreimageCodomain :
    RouteFamily (extend directedPair directedVaryingDomain) where
  fibre point :=
    match point with
    | ⟨false, PUnit.unit⟩ => PUnit
    | ⟨true, false⟩ => PUnit
    | ⟨true, true⟩ => Empty
  transport {source target} route := by
    rcases source with ⟨sourceBase, sourceArgument⟩
    rcases target with ⟨targetBase, targetArgument⟩
    cases sourceBase
    · cases sourceArgument
      cases targetBase
      · exact id
      · cases targetArgument
        · exact id
        · exact fun _ => (noRoute_source_to_missing route).elim
    · cases sourceArgument
      · cases targetBase
        · exact fun _ => PUnit.unit
        · cases targetArgument
          · exact id
          · exact fun _ => (noRoute_transported_to_missing route).elim
      · exact Empty.elim
  transport_refl point value := by
    rcases point with ⟨base, argument⟩
    cases base
    · cases argument
      rfl
    · cases argument
      · rfl
      · exact value.elim

/-- The raw pointwise carrier expected of a dependent product. -/
def PointwisePiFibre {context : RouteType.{u}} (domain : RouteFamily context)
    (codomain : RouteFamily (extend context domain))
    (point : context.carrier) : Type u :=
  forall argument : domain.fibre point, codomain.fibre ⟨point, argument⟩

/-- There is an inhabitant of the source pointwise product. -/
def sourcePointwiseFunction :
    PointwisePiFibre directedVaryingDomain missingPreimageCodomain false :=
  fun _ => PUnit.unit

/-- The target pointwise product is empty because it must return a value at
the missing Boolean argument. -/
theorem targetPointwiseFunction_empty :
    IsEmpty
      (PointwisePiFibre directedVaryingDomain missingPreimageCodomain true) :=
  ⟨fun function => by
    have impossible : Empty := function true
    exact impossible.elim⟩

/-- No route family can have these pointwise dependent-function fibres.  A
forward transport would map the inhabited source product into the empty
target product. -/
theorem no_arbitrary_pointwisePi_routeFamily :
    ¬ Exists fun product : RouteFamily directedPair =>
      product.fibre =
        PointwisePiFibre directedVaryingDomain missingPreimageCodomain := by
  rintro ⟨product, fibreEquality⟩
  have sourceEquality := congrFun fibreEquality false
  have targetEquality := congrFun fibreEquality true
  let sourceValue : product.fibre false :=
    cast sourceEquality.symm sourcePointwiseFunction
  let targetValue : product.fibre true :=
    product.transport DirectedRoute.forward sourceValue
  let impossible :
      PointwisePiFibre directedVaryingDomain missingPreimageCodomain true :=
    cast targetEquality targetValue
  exact targetPointwiseFunction_empty.false impossible

/-- The obstruction is invariant under fibrewise equivalence: changing the
encoding of the pointwise function fibres cannot create the missing forward
transport. -/
theorem no_equivalent_pointwisePi_routeFamily :
    ¬ Exists fun product : RouteFamily directedPair =>
      forall point : directedPair.carrier,
        Nonempty
          (product.fibre point ≃
            PointwisePiFibre directedVaryingDomain
              missingPreimageCodomain point) := by
  rintro ⟨product, fibreEquivalence⟩
  rcases fibreEquivalence false with ⟨sourceEquivalence⟩
  rcases fibreEquivalence true with ⟨targetEquivalence⟩
  let sourceValue : product.fibre false :=
    sourceEquivalence.symm sourcePointwiseFunction
  let targetValue : product.fibre true :=
    product.transport DirectedRoute.forward sourceValue
  let impossible :
      PointwisePiFibre directedVaryingDomain missingPreimageCodomain true :=
    targetEquivalence targetValue
  exact targetPointwiseFunction_empty.false impossible

/-- Pulled-back extensional families inhabit the product-supporting
fragment, while a valid covariant family and codomain refute unrestricted
pointwise products. -/
theorem dependent_product_variance_boundary :
    (forall (context : RouteType.{0})
      (family : (routeQuotient.obj context).carrier -> Type),
      Nonempty
        (FibrewiseEquivalenceTransport
          (pullbackReadoutFamily context family))) /\
    ¬ Exists fun product : RouteFamily directedPair =>
      forall point : directedPair.carrier,
        Nonempty
          (product.fibre point ≃
            PointwisePiFibre directedVaryingDomain
              missingPreimageCodomain point) :=
  ⟨fun context family =>
      ⟨pullbackReadoutEquivalenceTransport context family⟩,
    no_equivalent_pointwisePi_routeFamily⟩

end Canary

#print axioms liftRouteSubstitution_eq_extensionSubstitution
#print axioms sigmaFamily
#print axioms routeDependentSums
#print axioms sigmaFamily_reindex
#print axioms liftedEqualitySubsingleton
#print axioms identityFamily
#print axioms routeIdentityFormation
#print axioms routeIdentityReflexivity
#print axioms routeIdentityProofIrrelevance
#print axioms routeIdentityEndpointReflection
#print axioms FibrewiseEquivalenceTransport.reindex
#print axioms FibrewiseEquivalenceTransport.transport_inverse
#print axioms FibrewiseEquivalenceTransport.inverse_transport
#print axioms pullbackReadoutEquivalenceTransport
#print axioms piFamily
#print axioms piLam
#print axioms piApp
#print axioms pi_beta
#print axioms piFamily_reindex
#print axioms Canary.codiscreteVaryingFamily_not_equivalenceTransport
#print axioms Canary.missingPreimageCodomain
#print axioms Canary.targetPointwiseFunction_empty
#print axioms Canary.no_arbitrary_pointwisePi_routeFamily
#print axioms Canary.no_equivalent_pointwisePi_routeFamily
#print axioms Canary.dependent_product_variance_boundary

end Mettapedia.TypeTheory.RouteFamilyTypeFormers
