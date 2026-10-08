import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorNormalizationClosed
import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorNormalizationEqualizers
import Mettapedia.GSLT.Core.RelativeClosedInterpretationPreservationControls

/-!
# Complete witnesses through a weak closed presentation

The native interpretation is followed by the actual `ULift` functor. Its
images of products have an outer wrapper, while products of its images have
two separately wrapped components. Canonical comparisons retain both values.
Normalization also retains the independently supplied negation arrow.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedFunctorNormalizationControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open GeneratedCategory Interpretation FunctorNormalization
open RelativeClosedInterpretationPreservationControls

private instance identity_closed : MonoidalClosedFunctor (𝟭 Type) where
  comparison_iso argument := by
    have (result : Type) : IsIso ((expComparison (𝟭 Type) argument).natTrans.app result) := by
      rw [Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence.exponential_identity]
      exact IsIso.id ((ihom argument).obj result)
    exact NatIso.isIso_of_isIso_app _

private instance raised_lex : PreservesFiniteLimits uliftFunctor.{0, 0} :=
  preservesFiniteLimits_of_natIso uliftFunctorTrivial.symm

private instance raised_closed : MonoidalClosedFunctor uliftFunctor.{0, 0} :=
  Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence.closed_of_naturalIso uliftFunctorTrivial

abbrev weak : Object signature ⥤ Type := interpreted ⋙ uliftFunctor.{0, 0}

instance weak_lex : PreservesFiniteLimits weak :=
  comp_preservesFiniteLimits interpreted uliftFunctor

instance weak_closed : MonoidalClosedFunctor weak :=
  Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence.closed_composition interpreted uliftFunctor

abbrev normalized : Object signature ⥤ Type := normalizedFunctor weak

theorem wrapped_negation (value : Bool) : weak.map (declared true) (ULift.up value) =
    ULift.up (Bool.not value) := by
  change ULift.up (interpreted.map (declared true) value) = _
  rw [actual_negation]
  rfl

theorem normalized_data_object : normalized.obj dataObject = ULift Bool :=
  (congrArg ObjectImage.value (objectImage_named weak ())).trans rfl

theorem data_comparison_hom : (objectImage weak dataObject).comparison.hom ≫
    eqToHom normalized_data_object = 𝟙 (ULift Bool) :=
  comparison_transport weak (objectImage_named weak ())

theorem data_comparison_inv : (objectImage weak dataObject).comparison.inv =
    eqToHom normalized_data_object := by
  apply (cancel_epi (objectImage weak dataObject).comparison.hom).mp
  rw [Iso.hom_inv_id, data_comparison_hom]
  rfl

def normalizedNegation : ULift Bool ⟶ ULift Bool :=
  eqToHom normalized_data_object.symm ≫ normalized.map (declared true) ≫
    eqToHom normalized_data_object

theorem normalizedNegation_readout (value : Bool) :
    normalizedNegation (ULift.up value) = ULift.up (Bool.not value) := by
  have complete : normalizedNegation = weak.map (declared true) := by
    unfold normalizedNegation
    rw [normalized_map, data_comparison_inv]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [data_comparison_hom]
    rfl
  exact (congrArg (fun arrow : ULift Bool ⟶ ULift Bool => arrow (ULift.up value)) complete).trans
    (wrapped_negation value)

theorem normalized_negation_retains_both_arguments :
    (normalizedNegation (ULift.up false)).down = true ∧
      (normalizedNegation (ULift.up true)).down = false := by
  rw [normalizedNegation_readout, normalizedNegation_readout]
  exact ⟨rfl, rfl⟩

theorem constant_readout_rejected :
    (normalizedNegation (ULift.up false)).down ≠
      (normalizedNegation (ULift.up true)).down := by
  rw [normalized_negation_retains_both_arguments.1, normalized_negation_retains_both_arguments.2]
  exact Ne.symm Bool.false_ne_true

def productReadout : ULift (Bool × Bool) ⟶ ULift Bool × ULift Bool :=
  (objectImage weak (product dataObject dataObject)).comparison.hom ≫
    eqToHom ((normalized_product_object weak dataObject dataObject).trans
      (congrArg₂ (fun first second : Type => first ⊗ second)
        normalized_data_object normalized_data_object))

theorem productReadout_comparison : productReadout =
    CartesianMonoidalCategory.prodComparison weak dataObject dataObject := by
  have tensor_cast {first second before after : Type} (input : first = before)
      (output : second = after) :
      eqToHom (congrArg₂ (fun left right : Type => left ⊗ right) input output) =
        (eqToHom input ⊗ₘ eqToHom output) := by
    cases input
    cases output
    simp only [eqToHom_refl, id_tensorHom_id]
  unfold productReadout
  rw [← eqToHom_trans (normalized_product_object weak dataObject dataObject)
    (congrArg₂ (fun first second : Type => first ⊗ second)
      normalized_data_object normalized_data_object), ← Category.assoc,
    comparison_transport weak (objectImage_product weak dataObject dataObject)]
  change (CartesianMonoidalCategory.prodComparison weak dataObject dataObject ≫
    ((objectImage weak dataObject).comparison.hom ⊗ₘ
      (objectImage weak dataObject).comparison.hom)) ≫ eqToHom _ = _
  rw [tensor_cast normalized_data_object normalized_data_object, Category.assoc,
    tensorHom_comp_tensorHom, data_comparison_hom]
  rfl

theorem productReadout_pair (first second : Bool) :
    productReadout (ULift.up (first, second)) = (ULift.up first, ULift.up second) := by
  rw [productReadout_comparison]
  have choices := CartesianMonoidalCategory.prodComparison_comp interpreted uliftFunctor.{0, 0}
    (A := dataObject) (B := dataObject)
  change CartesianMonoidalCategory.prodComparison weak dataObject dataObject = _ at choices
  rw [choices, functor_productComparison]
  change ((𝟙 (ULift (Bool × Bool))) ≫
    CartesianMonoidalCategory.prodComparison uliftFunctor Bool Bool) (ULift.up (first, second)) = _
  rfl

theorem distinct_coordinates_survive :
    (productReadout (ULift.up (false, true))).1.down = false ∧
      (productReadout (ULift.up (false, true))).2.down = true := by
  rw [productReadout_pair]
  exact ⟨rfl, rfl⟩

theorem omitted_first_coordinate_rejected :
    (productReadout (ULift.up (false, true))).1.down ≠
      (productReadout (ULift.up (false, true))).2.down := by
  rw [distinct_coordinates_survive.1, distinct_coordinates_survive.2]
  exact Bool.false_ne_true

def completeComparison : weak ≅ normalized := comparison weak

end Mettapedia.GSLT.Core.RelativeClosedFunctorNormalizationControls
