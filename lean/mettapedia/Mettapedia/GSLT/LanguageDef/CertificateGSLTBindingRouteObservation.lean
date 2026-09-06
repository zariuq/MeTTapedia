import Mathlib.Data.Setoid.Basic
import Mettapedia.GSLT.Core.PolicyFamilySufficiency
import Mettapedia.GSLT.LanguageDef.CertificateGSLTBindingRouteFunctorCanary

/-!
# Observer-authorized quotients of binding-presentation routes

An observation of an authored route may forget distinctions only at the
capabilities it actually supports.  There are two related boundaries.

At the categorical boundary, a compositional observer is a functor.  The
kernel relation of the generated-authority functor is therefore a congruence
on binding-presentation routes.  Quotienting by that relation produces the
largest categorical erasure through which exact NIK authority generation
factors, and the induced realization is faithful.

At one fixed hom-set, a client can request a still coarser readout.  The
existing `PolicyFamily` criterion decides whether that readout is sufficient.
The canary below proves that checker acceptance alone supports an
acceptance-only client, but cannot support a revision-sensitive client which
also observes path length.  Thus equal answers authorize no unrequested
collapse of authored history.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLTBindingRouteObservation

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT.Core
open Mettapedia.GSLT.LanguageDef.CertifiedTheoryCategory
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory
open Mettapedia.GSLT.LanguageDef.CertificateGSLTHeterogeneousAuthority
open Mettapedia.GSLT.LanguageDef.CertificateGSLTBindingRouteFunctor

/-! ## The categorical quotient selected by exact generated authority -/

/-- Two authored routes are related exactly when they induce the same exact
generated NIK authority translation. -/
abbrev GeneratedAuthorityRelation :
    HomRel (CategoryTheory.Paths BindingPresentation) :=
  generationFunctor.homRel

/-- The binding-route category after erasing exactly those distinctions that
the generated-authority functor cannot observe. -/
abbrev GeneratedAuthorityQuotient :=
  CategoryTheory.Quotient GeneratedAuthorityRelation

/-- The canonical occurrence-erasing projection.  It identifies no more and
no fewer routes than exact generated authority identifies. -/
def quotientRouteFunctor :
    CategoryTheory.Functor
      (CategoryTheory.Paths BindingPresentation)
      GeneratedAuthorityQuotient :=
  CategoryTheory.Quotient.functor GeneratedAuthorityRelation

/-- Exact generated authority realized on its observer quotient. -/
def faithfulGenerationFunctor :
    CategoryTheory.Functor GeneratedAuthorityQuotient CertifiedTheory :=
  CategoryTheory.Quotient.lift GeneratedAuthorityRelation generationFunctor
    (by
      intro source target first second sameGenerated
      exact sameGenerated)

/-- Quotienting and then realizing recovers the original generated-authority
functor exactly. -/
theorem quotient_generation_commutes :
    CategoryTheory.Functor.comp quotientRouteFunctor
        faithfulGenerationFunctor = generationFunctor :=
  CategoryTheory.Quotient.lift_spec GeneratedAuthorityRelation
    generationFunctor
    (by
      intro source target first second sameGenerated
      exact sameGenerated)

/-- The quotient identifies precisely equality at generated authority.  In
particular, the quotient adds no accidental equations beyond its declared
observer. -/
theorem quotient_map_eq_iff_same_generated_authority
    {source target : BindingPresentation}
    (first second : Route source target) :
    quotientRouteFunctor.map first = quotientRouteFunctor.map second ↔
      generationFunctor.map first = generationFunctor.map second := by
  exact CategoryTheory.Quotient.functor_map_eq_iff
    GeneratedAuthorityRelation first second

/-- The induced realization is faithful: after the authorized erasure, exact
generated authority distinguishes every remaining route class. -/
instance faithfulGenerationFunctor_faithful :
    faithfulGenerationFunctor.Faithful := by
  dsimp only [faithfulGenerationFunctor, GeneratedAuthorityRelation]
  infer_instance

/-- The realization on the quotient is uniquely forced by its commuting
triangle with exact route generation. -/
theorem faithfulGenerationFunctor_unique
    (candidate :
      CategoryTheory.Functor GeneratedAuthorityQuotient CertifiedTheory)
    (commutes :
      CategoryTheory.Functor.comp quotientRouteFunctor candidate =
        generationFunctor) :
    candidate = faithfulGenerationFunctor :=
  CategoryTheory.Quotient.lift_unique GeneratedAuthorityRelation
    generationFunctor
    (by
      intro source target first second sameGenerated
      exact sameGenerated)
    candidate commutes

/-! ## A capability-relative quotient on one binding-route hom-set -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.CertificateGSLTBindingAuthorityCanary
open Mettapedia.GSLT.LanguageDef.CertificateGSLTBindingRouteFunctorCanary

/-- The exact checker observation for the source certificate transported
along one authored source-to-target route. -/
def acceptanceReadout (route : Route sourceNode targetNode) : Bool :=
  ((contract targetPresentation).checker ()).check
    ((generationFunctor.map route).mapClaim () sourceClaim)
    ((generationFunctor.map route).mapCertificate () sourceCertificate)

/-- Exact replay makes this particular acceptance observation constant over
all authored routes with these endpoints. -/
theorem acceptanceReadout_eq_true
    (route : Route sourceNode targetNode) :
    acceptanceReadout route = true := by
  unfold acceptanceReadout
  calc
    _ = ((contract sourcePresentation).checker ()).check sourceClaim
          sourceCertificate :=
      route_check_commutes route sourceClaim sourceCertificate
    _ = true := rfl

theorem acceptanceReadout_constant
    (first second : Route sourceNode targetNode) :
    acceptanceReadout first = acceptanceReadout second := by
  rw [acceptanceReadout_eq_true, acceptanceReadout_eq_true]

/-- Equality at the selected checker observation. -/
abbrev AcceptanceSetoid : Setoid (Route sourceNode targetNode) :=
  Setoid.ker acceptanceReadout

/-- Route classes visible to this acceptance-only observer. -/
abbrev AcceptanceClass := Quotient AcceptanceSetoid

/-- Forget an authored route down to its acceptance-only class. -/
def acceptanceClassOf (route : Route sourceNode targetNode) :
    AcceptanceClass :=
  Quotient.mk AcceptanceSetoid route

/-- The acceptance result itself descends to the observer quotient. -/
def acceptanceOnClass : AcceptanceClass → Bool :=
  Setoid.kerLift acceptanceReadout

@[simp] theorem acceptanceOnClass_classOf
    (route : Route sourceNode targetNode) :
    acceptanceOnClass (acceptanceClassOf route) = acceptanceReadout route :=
  rfl

/-- The observer quotient is exactly the realized range of the observation,
not the whole declared codomain when some outputs are unreachable. -/
noncomputable def acceptanceClassEquivObservedRange :
    AcceptanceClass ≃ Set.range acceptanceReadout :=
  Setoid.quotientKerEquivRange acceptanceReadout

/-- The direct and revised histories become equal only at this explicitly
declared acceptance observation. -/
theorem direct_revised_same_acceptance_class :
    acceptanceClassOf directRoute = acceptanceClassOf revisedRoute := by
  apply Quotient.sound
  exact acceptanceReadout_constant directRoute revisedRoute

inductive RoutePolicy where
  | acceptance
  | length
deriving DecidableEq

/-- A client family which asks both whether the certificate is accepted and
how many authored translation occurrences the route contains. -/
def routePolicyFamily : PolicyFamily (Route sourceNode targetNode) where
  Policy := RoutePolicy
  Result := fun
    | .acceptance => Bool
    | .length => Nat
  decide := fun
    | .acceptance => acceptanceReadout
    | .length => Quiver.Path.length

/-- The smaller client asks only for checker acceptance. -/
def acceptancePolicyFamily : PolicyFamily (Route sourceNode targetNode) :=
  routePolicyFamily.reindex (fun _ : Unit => RoutePolicy.acceptance)

/-- The acceptance readout is executable and sufficient for the
acceptance-only client. -/
theorem acceptanceReadout_supports_acceptancePolicyFamily :
    acceptancePolicyFamily.SupportsReadout acceptanceReadout := by
  refine ⟨{
    run := fun _ observed => observed
    agrees := ?_ }⟩
  intro policy route
  rfl

/-- Full route retention supports both acceptance and revision-sensitive
length. -/
theorem exactRoute_supports_routePolicyFamily :
    routePolicyFamily.SupportsReadout
      (id : Route sourceNode targetNode → Route sourceNode targetNode) := by
  refine ⟨{
    run := fun policy route => routePolicyFamily.decide policy route
    agrees := ?_ }⟩
  intro policy route
  rfl

/-- Acceptance alone is not sufficient for the larger client family: the
direct and revised routes collide at acceptance but differ in authored
length. -/
theorem acceptanceReadout_refuses_routePolicyFamily :
    ¬ routePolicyFamily.SupportsReadout acceptanceReadout := by
  apply routePolicyFamily.not_supportsReadout_of_policy_collision
    acceptanceReadout
    (first := directRoute) (second := revisedRoute)
    (acceptanceReadout_constant directRoute revisedRoute)
    RoutePolicy.length
  change directRoute.length ≠ revisedRoute.length
  simp

/-- Equivalently, no function on acceptance classes can reconstruct the
authored route length. -/
theorem routeLength_does_not_descend_to_acceptanceClass :
    ¬ ∃ recoverLength : AcceptanceClass → Nat,
      ∀ route, recoverLength (acceptanceClassOf route) = route.length := by
  rintro ⟨recoverLength, recovers⟩
  have sameRecovered :=
    congrArg recoverLength direct_revised_same_acceptance_class
  rw [recovers directRoute, recovers revisedRoute] at sameRecovered
  simp at sameRecovered

/-- The lawful and unlawful erasures coexist at one state space.  Lossiness
is authorized by the requested capabilities, never by the compactness of the
readout alone. -/
theorem acceptance_erasure_is_policy_relative :
    acceptancePolicyFamily.SupportsReadout acceptanceReadout ∧
      ¬ routePolicyFamily.SupportsReadout acceptanceReadout ∧
      directRoute ≠ revisedRoute ∧
      acceptanceClassOf directRoute = acceptanceClassOf revisedRoute :=
  ⟨acceptanceReadout_supports_acceptancePolicyFamily,
    acceptanceReadout_refuses_routePolicyFamily,
    directRoute_ne_revisedRoute,
    direct_revised_same_acceptance_class⟩

#print axioms quotient_generation_commutes
#print axioms quotient_map_eq_iff_same_generated_authority
#print axioms faithfulGenerationFunctor_unique
#print axioms acceptanceReadout_eq_true
#print axioms direct_revised_same_acceptance_class
#print axioms acceptanceReadout_supports_acceptancePolicyFamily
#print axioms exactRoute_supports_routePolicyFamily
#print axioms acceptanceReadout_refuses_routePolicyFamily
#print axioms routeLength_does_not_descend_to_acceptanceClass
#print axioms acceptance_erasure_is_policy_relative

end Canary

end Mettapedia.GSLT.LanguageDef.CertificateGSLTBindingRouteObservation
