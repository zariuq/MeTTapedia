import Mathlib.CategoryTheory.Whiskering
import Mettapedia.TypeTheory.RouteSensitiveDisplayedFamily

/-!
# Observation and displayed-family pullback

A natural observation of contextual terms induces a functor between their
categories of elements.  Precomposition along that functor pulls every
substitution-coherent displayed family on the observed terms back to the
source terms.  The essential image of this pullback is the precise
categorical fragment whose dependency is expressible through the observer.

For open Boolean value-and-route terms, the value-only pullback has a proper
essential image: route-sensitive dependency is outside it.  The compatible
joint value-and-route observation transports all displayed families because
its base map is an isomorphism.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedFamilyObservation

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.TypeTheory.CwfTermJointObservation
open Mettapedia.TypeTheory.DependentFamilyObserverFactorization
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.RouteSensitiveDisplayedFamily

universe uContext vContext uBase uFibre

variable {Context : Type uContext} [Category.{vContext} Context]

/-- Pull a displayed family back along the functor on categories of elements
induced by a natural observation. -/
def observationPullback
    {source target : Face.{uContext, vContext, uBase} Context}
    (observation : source ⟶ target) :
    DisplayedFamily.{uContext, vContext, uBase, uFibre} target ⥤
      DisplayedFamily.{uContext, vContext, uBase, uFibre} source :=
  (Functor.whiskeringLeft source.Elements target.Elements (Type uFibre)).obj
    (NatTrans.mapElements observation)

/-- A displayed family factors through an observation when it belongs to the
essential image of observation pullback. -/
def FactorsThrough
    {source target : Face.{uContext, vContext, uBase} Context}
    (observation : source ⟶ target)
    (family : DisplayedFamily.{uContext, vContext, uBase, uFibre} source) :
    Prop :=
  ∃ targetFamily :
      DisplayedFamily.{uContext, vContext, uBase, uFibre} target,
    Nonempty
      (family ≅ (observationPullback observation).obj targetFamily)

/-- Every literal pullback lies in the observation-expressible fragment. -/
theorem pullback_factors
    {source target : Face.{uContext, vContext, uBase} Context}
    (observation : source ⟶ target)
    (targetFamily :
      DisplayedFamily.{uContext, vContext, uBase, uFibre} target) :
    FactorsThrough observation
      ((observationPullback observation).obj targetFamily) :=
  ⟨targetFamily, ⟨Iso.refl _⟩⟩

/-! ## Properness of the value-only fragment -/

namespace OpenTermCanary

private def unitContext : SetFamilyContextᵒᵖ :=
  Opposite.op ⟨PUnit⟩

private def falseRouteElement : valueRouteTerms.Elements :=
  ⟨unitContext, fun _ => (false, false)⟩

private def trueRouteElement : valueRouteTerms.Elements :=
  ⟨unitContext, fun _ => (false, true)⟩

/-- The value observation sends the two route-distinct elements to the same
object in the observed category of elements. -/
private theorem valueElements_same :
    (NatTrans.mapElements (coordinateObservation .left)).obj
        falseRouteElement =
      (NatTrans.mapElements (coordinateObservation .left)).obj
        trueRouteElement :=
  rfl

/-- Route-sensitive dependency is not isomorphic to the pullback of any
displayed family over visible values.  Thus the value-only displayed fragment
is categorically proper, not merely pointwise incomplete. -/
theorem routeSensitive_not_in_value_essentialImage :
    ¬ FactorsThrough (coordinateObservation .left)
      routeSensitiveFamily := by
  rintro ⟨observedFamily, ⟨isomorphism⟩⟩
  let atFalse := (isomorphism.app falseRouteElement).toEquiv
  let atTrue := (isomorphism.app trueRouteElement).toEquiv
  have observedTypeAgreement :
      observedFamily.obj
          ((NatTrans.mapElements (coordinateObservation .left)).obj
            falseRouteElement) =
        observedFamily.obj
          ((NatTrans.mapElements (coordinateObservation .left)).obj
            trueRouteElement) :=
    congrArg observedFamily.obj valueElements_same
  let sectionEquivalence :=
    atFalse.trans
      ((Equiv.cast observedTypeAgreement).trans atTrue.symm)
  have concreteSectionEquivalence :
      ((Opposite.unop unitContext).val → PUnit) ≃
        ((Opposite.unop unitContext).val → Bool) := by
    simpa [sectionEquivalence, atFalse, atTrue, observationPullback,
      routeSensitiveFamily, routeFibre, falseRouteElement,
      trueRouteElement] using sectionEquivalence
  letI : Unique (Opposite.unop unitContext).val := by
    change Unique PUnit
    infer_instance
  have unitBoolEquivalence : PUnit ≃ Bool :=
    (Equiv.piUnique
      (fun _ : (Opposite.unop unitContext).val => PUnit)).symm.trans
      (concreteSectionEquivalence.trans
        (Equiv.piUnique
          (fun _ : (Opposite.unop unitContext).val => Bool)))
  exact Canary.unit_not_equiv_bool ⟨unitBoolEquivalence⟩

/-- The joint observation carries the same family by an equivalence of whole
displayed-family categories. -/
theorem routeSensitive_in_joint_equivalent_image :
    Nonempty
      (routeSensitiveFamily ≅
        Mettapedia.TypeTheory.DisplayedPresheafTransport.OpenTermCanary.valueAndRouteDisplayedFamilies.inverse.obj
          compatibleRouteSensitiveFamily) :=
  ⟨routeSensitiveRoundtrip⟩

/-- Paired canary: ordinary pullbacks provide a nonempty value-expressible
fragment, that fragment excludes route-sensitive dependency, and the joint
observer recovers it exactly. -/
theorem displayed_observation_boundary
    (observedFamily : DisplayedFamily.{1, 0, 0, 0} booleanTerms) :
    FactorsThrough (coordinateObservation .left)
        ((observationPullback (coordinateObservation .left)).obj
          observedFamily) ∧
      ¬ FactorsThrough (coordinateObservation .left)
        routeSensitiveFamily ∧
      Nonempty
        (routeSensitiveFamily ≅
          Mettapedia.TypeTheory.DisplayedPresheafTransport.OpenTermCanary.valueAndRouteDisplayedFamilies.inverse.obj
            compatibleRouteSensitiveFamily) :=
  ⟨pullback_factors (coordinateObservation .left) observedFamily,
    routeSensitive_not_in_value_essentialImage,
    routeSensitive_in_joint_equivalent_image⟩

end OpenTermCanary

#print axioms observationPullback
#print axioms pullback_factors
#print axioms OpenTermCanary.routeSensitive_not_in_value_essentialImage
#print axioms OpenTermCanary.routeSensitive_in_joint_equivalent_image
#print axioms OpenTermCanary.displayed_observation_boundary

end Mettapedia.TypeTheory.DisplayedFamilyObservation
