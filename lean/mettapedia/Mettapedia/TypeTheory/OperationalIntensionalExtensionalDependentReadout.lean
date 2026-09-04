import Mettapedia.TypeTheory.DependentFamilyDescentNaturality
import Mettapedia.TypeTheory.OperationalIntensionalExtensionalModes
import Mettapedia.TypeTheory.QuotientDependentFamilyDescent

/-!
# Dependent families at the intensional/extensional readout

The object-level readout from a route type to its quotient is always lawful.
Its action on arbitrary dependent families is more selective.  A family can
descend, up to fibrewise equivalence, only when quotient-related source points
carry equivalent fibres.  Hence the route quotient supports every dependent
family exactly when its quotient map is injective.

Discrete route types form the positive control: their relation is equality,
so every family descends.  The codiscrete two-point route type is the negative
control.  Its quotient identifies `false` and `true`, while the family with a
singleton fibre over `false` and a Boolean fibre over `true` cannot descend.

This boundary does not rule out a dependent modal structure on a restricted
class of route-invariant families, nor a separately justified pushforward.
It rules out treating the identifying quotient as lossless descent for all
dependent families.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.OperationalIntensionalExtensionalDependentReadout

open Mettapedia.TypeTheory.DependentFamilyObserverFactorization
open Mettapedia.TypeTheory.DependentFamilyDescentNaturality
open Mettapedia.TypeTheory.ExtensionalReadout
open Mettapedia.TypeTheory.OperationalIntensionalExtensionalModes
open Mettapedia.TypeTheory.QuotientDependentFamilyDescent
open Mettapedia.TypeTheory.UniversalDependentFamilyDescent
open CategoryTheory

universe u uFibre

/-- The underlying split readout of the intensional-to-extensional route
quotient.  A representative is selected classically for each quotient class.
-/
noncomputable def routeQuotientReadout (X : RouteType.{u}) :
    SplitReadout X.carrier (routeQuotient.obj X).carrier :=
  quotientReadout X.Route

/-- The route quotient transports every dependent family exactly when the
underlying quotient map is injective. -/
theorem allFamiliesDescend_iff_routeQuotient_injective
    (X : RouteType.{u}) :
    AllFamiliesDescend.{u, u, uFibre} (routeQuotientReadout X) <->
      Function.Injective (Quot.mk X.Route) :=
  allFamiliesDescend_iff_quotMk_injective X.Route

/-- Explicit descent data is stable under substitution along a route-preserving
map.  This is the first required contextual law for the restricted-family
alternative; it is not yet a comprehension theorem. -/
noncomputable def reindexRouteQuotientDescent
    {X Y : RouteType.{u}} (map : X ⟶ Y)
    {family : Y.carrier -> Type uFibre}
    (factorization :
      FamilyFactorization (routeQuotientReadout Y).observe family) :
    FamilyFactorization (routeQuotientReadout X).observe
      (fun source => family (map.toFun source)) :=
  Descent.reindexAlongSquare factorization map.toFun
    (routeQuotientReadout X).observe (routeQuotient.map map).toFun
    (fun _ => rfl)

/-- The property of admitting route-quotient descent is therefore stable under
reindexing. -/
theorem routeQuotientDescent_reindex
    {X Y : RouteType.{u}} (map : X ⟶ Y)
    {family : Y.carrier -> Type uFibre}
    (descends :
      Nonempty
        (FamilyFactorization (routeQuotientReadout Y).observe family)) :
    Nonempty
      (FamilyFactorization (routeQuotientReadout X).observe
        (fun source => family (map.toFun source))) := by
  obtain ⟨factorization⟩ := descends
  exact ⟨reindexRouteQuotientDescent map factorization⟩

/-! ## Discrete positive control -/

/-- Every dependent family descends through the quotient of a discrete route
type, because its route relation identifies only equal points. -/
theorem discrete_allFamiliesDescend (B : ExtType.{u}) :
    AllFamiliesDescend.{u, u, uFibre}
      (routeQuotientReadout (discreteOn.obj B)) :=
  equalityQuotient_allFamiliesDescend B.carrier

/-! ## Identifying-quotient negative control -/

/-- The concrete varying family used to test the codiscrete route quotient. -/
def codiscreteVaryingFamily : codiscretePair.carrier -> Type
  | false => PUnit
  | true => Bool

/-- The two points of the codiscrete pair have the same extensional readout. -/
theorem codiscretePair_sameReadout :
    (routeQuotientReadout codiscretePair).observe false =
      (routeQuotientReadout codiscretePair).observe true :=
  Quot.sound trivial

/-- The codiscrete route quotient is genuinely identifying. -/
theorem codiscretePair_quotMk_not_injective :
    Not (Function.Injective (Quot.mk codiscretePair.Route)) := by
  intro injective
  exact Bool.false_ne_true (injective (Quot.sound trivial))

/-- Constant families remain compatible with the identifying quotient. -/
noncomputable def codiscretePair_constantFactors :
    FamilyFactorization
      (routeQuotientReadout codiscretePair).observe
      (fun _ => PUnit) :=
  FamilyFactorization.constant _ PUnit

/-- Boolean negation is a nonidentity route-preserving endomorphism of the
codiscrete pair. -/
def codiscretePairNegation : codiscretePair ⟶ codiscretePair where
  toFun := Bool.not
  map_route := fun _ => trivial

/-- The substitution control is genuinely nonidentity. -/
theorem codiscretePairNegation_ne_identity :
    codiscretePairNegation ≠ 𝟙 codiscretePair := by
  intro sameMap
  have atTrue :=
    congrArg
      (fun map : RouteHom codiscretePair codiscretePair => map.toFun true)
      sameMap
  change Bool.not true = true at atTrue
  exact Bool.noConfusion atTrue

/-- The constant-family descent data survives reindexing along the nonidentity
endomorphism, giving a concrete substitution control at the route quotient. -/
noncomputable def codiscretePair_constantFactors_afterNegation :
    FamilyFactorization
      (routeQuotientReadout codiscretePair).observe
      (fun _ => PUnit) :=
  reindexRouteQuotientDescent codiscretePairNegation
    codiscretePair_constantFactors

/-- The singleton/Boolean family cannot descend through the codiscrete route
quotient: one target fibre cannot be equivalent to both source fibres. -/
theorem codiscreteVaryingFamily_doesNotDescend :
    Not
      (Nonempty
        (FamilyFactorization
          (routeQuotientReadout codiscretePair).observe
          codiscreteVaryingFamily)) := by
  exact FamilyFactorization.not_nonempty_of_nonEquivalent_fibres
    (left := false) (right := true) codiscretePair_sameReadout
    DependentFamilyObserverFactorization.Canary.unit_not_equiv_bool

/-- Consequently the identifying route quotient cannot transport every
dependent family. -/
theorem codiscretePair_not_allFamiliesDescend :
    Not
      (AllFamiliesDescend.{0, 0, uFibre}
        (routeQuotientReadout codiscretePair)) := by
  intro allFamilies
  exact codiscretePair_quotMk_not_injective
    ((allFamiliesDescend_iff_routeQuotient_injective codiscretePair).1
      allFamilies)

/-- Paired boundary: the route quotient supports every family on its discrete
fragment, while the same object-level construction fails universal dependent
descent on a genuinely identifying route type. -/
theorem discrete_and_identifying_boundary :
    AllFamiliesDescend.{0, 0, 0}
        (routeQuotientReadout (discreteOn.obj extBool)) /\
      Nonempty
        (FamilyFactorization
          (routeQuotientReadout codiscretePair).observe
          (fun _ => PUnit)) /\
      Not
        (Nonempty
          (FamilyFactorization
            (routeQuotientReadout codiscretePair).observe
            codiscreteVaryingFamily)) :=
  ⟨discrete_allFamiliesDescend extBool,
    ⟨codiscretePair_constantFactors⟩,
    codiscreteVaryingFamily_doesNotDescend⟩

/-- The intensional mode contains an object at which route quotient is not a
universal dependent-family readout. -/
theorem routeQuotient_not_universally_dependent :
    ∃ X : RouteType.{0},
      Not
        (AllFamiliesDescend.{0, 0, 0}
          (routeQuotientReadout X)) :=
  ⟨codiscretePair, codiscretePair_not_allFamiliesDescend⟩

#print axioms routeQuotientReadout
#print axioms allFamiliesDescend_iff_routeQuotient_injective
#print axioms reindexRouteQuotientDescent
#print axioms routeQuotientDescent_reindex
#print axioms discrete_allFamiliesDescend
#print axioms codiscretePair_sameReadout
#print axioms codiscretePair_quotMk_not_injective
#print axioms codiscreteVaryingFamily_doesNotDescend
#print axioms codiscretePair_not_allFamiliesDescend
#print axioms codiscretePairNegation_ne_identity
#print axioms codiscretePair_constantFactors_afterNegation
#print axioms discrete_and_identifying_boundary
#print axioms routeQuotient_not_universally_dependent

end Mettapedia.TypeTheory.OperationalIntensionalExtensionalDependentReadout
