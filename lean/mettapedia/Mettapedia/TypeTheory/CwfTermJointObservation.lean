import Mettapedia.Computability.ContextualJointObservation
import Mettapedia.GSLT.Core.ContextualLadderBaseCategory

/-!
# Joint observations of open terms in the set-families CwF

Terms of a constant type `A` in the set-families CwF form a presheaf:
at context `Γ` they are functions `Γ → A`, and substitution acts by
precomposition.  This module instantiates contextual joint observation on
the nonconstant presheaf of open terms of type `Bool × Bool`.

The first component is read as an extensional value and the second as a
retained route or occurrence tag.  Each projection loses open-term
information.  Together they separate terms at every context, so the source
term presheaf is naturally isomorphic to the compatible family of its two
views.  Consequently every pointwise dependent family descends through the
joint view.

This is a substitution-coherent instance, not a complete CwF comparison.  It
does not assert that either projection preserves dependent types, context
comprehension, identity routes, effects, or cost by itself.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.CwfTermJointObservation

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.Computability.ContextualJointObservation
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.JointObservationDependentDescent
open Mettapedia.TypeTheory.JointObservationDependentDescent.Canary

/-- The category of contexts and substitutions of the small set-families
CwF. -/
abbrev SetFamilyContext := (familiesCwf.{0}).base.Context

/-- Open terms of one constant type, with substitution by precomposition. -/
def constantTermFace (A : Type) :
    Face.{1, 0, 0} SetFamilyContext where
  obj context := context.unop.val → A
  map substitution := TypeCat.ofHom fun term point =>
    term (substitution.unop point)
  map_id context := by
    apply ConcreteCategory.hom_ext
    intro term
    rfl
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro term
    rfl

/-- Postcomposition gives a natural map between constant-term presheaves. -/
def postcompose {A B : Type} (map : A → B) :
    constantTermFace A ⟶ constantTermFace B where
  app _ := TypeCat.ofHom fun term point => map (term point)
  naturality := by
    intro first second substitution
    apply ConcreteCategory.hom_ext
    intro term
    rfl

/-- Open terms carrying both a visible Boolean value and a retained Boolean
route tag. -/
def valueRouteTerms : Face.{1, 0, 0} SetFamilyContext :=
  constantTermFace (Bool × Bool)

/-- Open Boolean observations. -/
def booleanTerms : Face.{1, 0, 0} SetFamilyContext :=
  constantTermFace Bool

def coordinateObservation (coordinate : Coordinate) :
    valueRouteTerms ⟶ booleanTerms :=
  postcompose
    (match coordinate with
    | .left => (Prod.fst : Bool × Bool → Bool)
    | .right => Prod.snd)

/-- Value and route are two natural observations of one open-term
presheaf. -/
def valueAndRoute : ContextualObservationFamily valueRouteTerms where
  Index := Coordinate
  target _ := booleanTerms
  observe := coordinateObservation

/-- The two views jointly separate open terms at every context. -/
theorem valueAndRoute_pointwiseSeparating :
    valueAndRoute.PointwiseJointlySeparating := by
  intro context left right sameViews
  funext point
  apply Prod.ext
  · exact congrFun (congrFun sameViews .left) point
  · exact congrFun (congrFun sameViews .right) point

/-- The source open-term presheaf is exactly its compatible value-and-route
view, naturally in context substitution. -/
noncomputable def valueAndRoute_iso :
    valueRouteTerms ≅
      ContextualObservationFamily.compatibleFace valueAndRoute :=
  ContextualObservationFamily.compatibleIso valueAndRoute
    valueAndRoute_pointwiseSeparating

/-- Every pointwise dependent family over open value-and-route terms descends
through their compatible joint observation. -/
theorem valueAndRoute_allFamiliesDescend :
    valueAndRoute.PointwiseAllFamiliesDescend :=
  (ContextualObservationFamily.pointwiseAllFamiliesDescend_iff_jointlySeparating
    valueAndRoute).2 valueAndRoute_pointwiseSeparating

/-! ## Individual-loss and substitution controls -/

private def unitContext : SetFamilyContextᵒᵖ :=
  Opposite.op ⟨PUnit⟩

theorem valueObservation_not_separating_at_unit :
    ¬ (valueAndRoute.atContext unitContext).SeparatesAt .left := by
  intro separates
  let first : valueRouteTerms.obj unitContext := fun _ => (false, false)
  let second : valueRouteTerms.obj unitContext := fun _ => (false, true)
  have sameValue :
      (valueAndRoute.atContext unitContext).observe .left first =
        (valueAndRoute.atContext unitContext).observe .left second := rfl
  have sameTerm := separates sameValue
  have sameAtUnit := congrFun sameTerm PUnit.unit
  change (false, false) = (false, true) at sameAtUnit
  exact Bool.false_ne_true (congrArg Prod.snd sameAtUnit)

theorem routeObservation_not_separating_at_unit :
    ¬ (valueAndRoute.atContext unitContext).SeparatesAt .right := by
  intro separates
  let first : valueRouteTerms.obj unitContext := fun _ => (false, false)
  let second : valueRouteTerms.obj unitContext := fun _ => (true, false)
  have sameRoute :
      (valueAndRoute.atContext unitContext).observe .right first =
        (valueAndRoute.atContext unitContext).observe .right second := rfl
  have sameTerm := separates sameRoute
  have sameAtUnit := congrFun sameTerm PUnit.unit
  change (false, false) = (true, false) at sameAtUnit
  exact Bool.false_ne_true (congrArg Prod.fst sameAtUnit)

private def boolContextObject : SetFamilyContext := ⟨Bool⟩
private def unitContextObject : SetFamilyContext := ⟨PUnit⟩

private def selectFalse : unitContextObject ⟶ boolContextObject :=
  fun _ => false

private def diagonalOpenTerm :
    valueRouteTerms.obj (Opposite.op boolContextObject) :=
  fun value => (value, value)

/-- A genuine nonidentity substitution acts by selecting the corresponding
open-term value; the instance is not merely a family of constant carriers. -/
theorem substitution_selects_open_term :
    valueRouteTerms.map (Quiver.Hom.op selectFalse) diagonalOpenTerm
        PUnit.unit =
      (false, false) :=
  rfl

/-- Positive and negative controls for the contextual instance. -/
theorem openTerm_jointObservation_boundary :
    (¬ (valueAndRoute.atContext unitContext).SeparatesAt .left) ∧
      (¬ (valueAndRoute.atContext unitContext).SeparatesAt .right) ∧
      valueAndRoute.PointwiseJointlySeparating ∧
      Nonempty
        (valueRouteTerms ≅
          ContextualObservationFamily.compatibleFace valueAndRoute) ∧
      valueAndRoute.PointwiseAllFamiliesDescend :=
  ⟨valueObservation_not_separating_at_unit,
    routeObservation_not_separating_at_unit,
    valueAndRoute_pointwiseSeparating,
    ⟨valueAndRoute_iso⟩,
    valueAndRoute_allFamiliesDescend⟩

#print axioms constantTermFace
#print axioms postcompose
#print axioms valueAndRoute_pointwiseSeparating
#print axioms valueAndRoute_iso
#print axioms valueAndRoute_allFamiliesDescend
#print axioms valueObservation_not_separating_at_unit
#print axioms routeObservation_not_separating_at_unit
#print axioms substitution_selects_open_term
#print axioms openTerm_jointObservation_boundary

end Mettapedia.TypeTheory.CwfTermJointObservation
