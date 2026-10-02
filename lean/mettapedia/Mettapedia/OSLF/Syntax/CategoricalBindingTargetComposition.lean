import Mettapedia.OSLF.Syntax.CategoricalBindingTargetChange

/-!
# Identity and composition of selected-exponential preservation

Preservation is stable under identity and composition of target functors.
The evaluation comparison for a composite is the composite of its actual
product comparisons.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.CategoricalBindingModel

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

universe u v u' v' u'' v''

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable {D' : Type u'} [Category.{v'} D'] [CartesianMonoidalCategory D']
variable {D'' : Type u''} [Category.{v''} D''] [CartesianMonoidalCategory D'']

/-- Identity preserves every selected function object. -/
instance identityExponentialPreservation : ExponentialPreservation (𝟭 D) where
  image E := E
  eval_image E := by
    rw [← productComparisonIso_inv, prodComparisonIso_id]
    simp only [Iso.refl_inv, Functor.id_map, Functor.id_obj, Category.id_comp]

variable (H : D ⥤ D') (K : D' ⥤ D'')
variable [PreservesFiniteProducts H] [PreservesFiniteProducts K]
variable [ExponentialPreservation H] [ExponentialPreservation K]

/-- Successive target changes preserve every selected function object. -/
instance compositeExponentialPreservation : ExponentialPreservation (H ⋙ K) where
  image E := ExponentialPreservation.image (H := K) (ExponentialPreservation.image (H := H) E)
  eval_image E := by
    rw [ExponentialPreservation.eval_image, ExponentialPreservation.eval_image, K.map_comp]
    rw [← productComparisonIso_inv K, ← productComparisonIso_inv H,
      ← productComparisonIso_inv (H ⋙ K)]
    simp only [prodComparisonIso_comp, Iso.trans_inv, Functor.mapIso_inv,
      Functor.comp_map, Category.assoc]


end Mettapedia.OSLF.Binding.CategoricalBindingModel
