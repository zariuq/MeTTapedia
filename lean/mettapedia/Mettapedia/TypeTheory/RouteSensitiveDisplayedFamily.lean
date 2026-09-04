import Mettapedia.TypeTheory.DependentFamilyObserverFactorization
import Mettapedia.TypeTheory.DisplayedPresheafTransport

/-!
# Route-sensitive displayed families over open terms

An open term may expose an extensional value while retaining a distinct
route or occurrence component.  This module constructs a genuinely varying
displayed family whose fibres depend on that retained route, with a coherent
action under every substitution of the set-families CwF.

The jointly separating value-and-route observation transports the complete
displayed family.  The value observation alone cannot support even its fibre
at the unit context: two terms with the same visible value have respectively
singleton and two-element fibres.  As a positive control, a family depending
only on the visible value does factor through the value observation.

This is a discriminator for extensional--intensional interfaces.  It does
not prescribe whether a language should permit route-sensitive types.  It
states the exact extra information such types require.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.RouteSensitiveDisplayedFamily

open CategoryTheory
open Mettapedia.TypeTheory.CwfTermJointObservation
open Mettapedia.TypeTheory.DependentFamilyObserverFactorization
open Mettapedia.TypeTheory.DisplayedPresheafTransport

/-! ## A substitution-coherent route-sensitive family -/

/-- The fibre selected by the retained route of an open term at a point. -/
def routeFibre {Context : Type} (term : Context → Bool × Bool)
    (point : Context) : Type :=
  if (term point).2 then Bool else PUnit

/-- Substitution preserves the selected route fibre because a morphism in
the category of elements preserves the open term. -/
private theorem routeFibre_natural
    {source target : valueRouteTerms.Elements}
    (substitution : source ⟶ target)
    (point : target.1.unop.val) :
    routeFibre source.2 (substitution.val.unop point) =
      routeFibre target.2 point := by
  have termAgreement := congrFun substitution.property point
  exact congrArg (fun pair : Bool × Bool =>
    if pair.2 then Bool else PUnit) termAgreement

/-- Sections of the route-selected fibres form a displayed family over the
open value-and-route term presheaf.  Its map is ordinary reindexing along a
context substitution, followed by transport along term preservation. -/
def routeSensitiveFamily :
    DisplayedFamily.{1, 0, 0, 0} valueRouteTerms where
  obj element :=
    ∀ point : element.1.unop.val, routeFibre element.2 point
  map substitution := TypeCat.ofHom fun displayed point =>
    cast (routeFibre_natural substitution point)
      (displayed (substitution.val.unop point))
  map_id element := by
    apply ConcreteCategory.hom_ext
    intro displayed
    funext point
    change cast (routeFibre_natural (𝟙 element) point) (displayed point) =
      displayed point
    exact cast_eq (routeFibre_natural (𝟙 element) point) (displayed point)
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro displayed
    funext point
    change cast _ (displayed (first.val.unop (second.val.unop point))) =
      cast _ (cast _ (displayed (first.val.unop (second.val.unop point))))
    simp only [cast_cast]

/-- The route-sensitive family transported to the compatible joint-view
base. -/
noncomputable def compatibleRouteSensitiveFamily :
    DisplayedFamily.{1, 0, 0, 0}
      (_root_.Mettapedia.Computability.ContextualJointObservation.ContextualObservationFamily.compatibleFace
        valueAndRoute) :=
  OpenTermCanary.valueAndRouteDisplayedFamilies.functor.obj
    routeSensitiveFamily

/-- Transport through the joint value-and-route view and back recovers the
route-sensitive family as a functor. -/
noncomputable def routeSensitiveRoundtrip :
    routeSensitiveFamily ≅
      OpenTermCanary.valueAndRouteDisplayedFamilies.inverse.obj
        compatibleRouteSensitiveFamily :=
  OpenTermCanary.valueAndRouteDisplayedFamilies.unitIso.app
    routeSensitiveFamily

/-! ## The value-only factorization boundary at the unit context -/

private def unitContext : SetFamilyContextᵒᵖ :=
  Opposite.op ⟨PUnit⟩

/-- The value coordinate at the unit context. -/
def unitValueObservation :
    valueRouteTerms.obj unitContext → booleanTerms.obj unitContext :=
  (coordinateObservation .left).app unitContext

/-- A type family selected only by the visible value. -/
def visibleFibre (valueTerm : booleanTerms.obj unitContext) : Type :=
  if valueTerm PUnit.unit then Bool else PUnit

/-- The pullback of `visibleFibre` along the value observer. -/
def unitValueSensitiveFamily
    (term : valueRouteTerms.obj unitContext) : Type :=
  visibleFibre (unitValueObservation term)

/-- Positive control: a value-sensitive family factors through the value
observer by construction. -/
def unitValueSensitiveFactors :
    FamilyFactorization unitValueObservation unitValueSensitiveFamily :=
  FamilyFactorization.pullback unitValueObservation visibleFibre

/-- The fibre selected by the retained route at the unit context. -/
def unitRouteSensitiveFamily
    (term : valueRouteTerms.obj unitContext) : Type :=
  routeFibre term PUnit.unit

private def falseRouteTerm : valueRouteTerms.obj unitContext :=
  fun _ => (false, false)

private def trueRouteTerm : valueRouteTerms.obj unitContext :=
  fun _ => (false, true)

/-- Negative control: value alone identifies two terms whose route-sensitive
fibres have different cardinalities, so no value-indexed family can represent
both up to equivalence. -/
theorem unitRouteSensitive_does_not_factor_through_value :
    ¬ Nonempty
      (FamilyFactorization unitValueObservation unitRouteSensitiveFamily) := by
  exact FamilyFactorization.not_nonempty_of_nonEquivalent_fibres
    (left := falseRouteTerm) (right := trueRouteTerm) rfl
    Canary.unit_not_equiv_bool

/-- Paired boundary: the value observer supports exactly value-indexed
variation in this control, while route-indexed variation requires the joint
view (or another observer retaining the route). -/
theorem value_and_joint_displayed_boundary :
    Nonempty
        (FamilyFactorization unitValueObservation unitValueSensitiveFamily) ∧
      ¬ Nonempty
        (FamilyFactorization unitValueObservation unitRouteSensitiveFamily) ∧
      Nonempty
        (routeSensitiveFamily ≅
          OpenTermCanary.valueAndRouteDisplayedFamilies.inverse.obj
            compatibleRouteSensitiveFamily) :=
  ⟨⟨unitValueSensitiveFactors⟩,
    unitRouteSensitive_does_not_factor_through_value,
    ⟨routeSensitiveRoundtrip⟩⟩

#print axioms routeSensitiveFamily
#print axioms compatibleRouteSensitiveFamily
#print axioms routeSensitiveRoundtrip
#print axioms unitValueSensitiveFactors
#print axioms unitRouteSensitive_does_not_factor_through_value
#print axioms value_and_joint_displayed_boundary

end Mettapedia.TypeTheory.RouteSensitiveDisplayedFamily
