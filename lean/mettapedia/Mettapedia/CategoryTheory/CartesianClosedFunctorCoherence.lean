import Mathlib.CategoryTheory.Monoidal.Closed.Functor
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# Coherence of cartesian closed functor comparisons

Canonical exponential comparisons compose. Invertibility can consequently
be reflected through a fully faithful closed interpretation. These laws use
the selected product and evaluation comparisons, rather than equality of
independently chosen exponential objects.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits (PreservesLimitsOfShape WalkingPair)
open MonoidalCategory MonoidalClosed CartesianMonoidalCategory

universe v u₁ u₂ u₃
variable {C : Type u₁} [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]
variable {D : Type u₂} [Category.{v} D] [CartesianMonoidalCategory D] [MonoidalClosed D]
variable {E : Type u₃} [Category.{v} E] [CartesianMonoidalCategory E] [MonoidalClosed E]

variable (F : C ⥤ D) (G : D ⥤ E)
variable [PreservesLimitsOfShape (Discrete WalkingPair) F]
variable [PreservesLimitsOfShape (Discrete WalkingPair) G]

/-- The canonical comparison for a composite is the composite of the
two actual canonical comparisons. -/
theorem exponential_composition (A B : C) :
    (expComparison (F ⋙ G) A).natTrans.app B =
      G.map ((expComparison F A).natTrans.app B) ≫
        (expComparison G (F.obj A)).natTrans.app (F.obj B) := by
  apply uncurry_injective
  rw [uncurry_expComparison, uncurry_natural_left, uncurry_expComparison]
  simp only [Functor.comp_obj, Functor.comp_map]
  rw [← Category.assoc, ← prodComparison_inv_natural_whiskerLeft,
    Category.assoc, ← G.map_comp, expComparison_ev]
  simp only [prodComparison_comp, IsIso.inv_comp, ← Functor.map_inv,
    Functor.map_comp, Category.assoc]

/-- Closed functors compose through their earned canonical comparisons. -/
theorem closed_composition [MonoidalClosedFunctor F] [MonoidalClosedFunctor G] :
    MonoidalClosedFunctor (F ⋙ G) where
  comparison_iso A := by
    have (B : C) : IsIso ((expComparison (F ⋙ G) A).natTrans.app B) := by
      rw [exponential_composition]
      infer_instance
    exact NatIso.isIso_of_isIso_app _

variable {F} {H : C ⥤ D}
variable [PreservesLimitsOfShape (Discrete WalkingPair) H]

omit [MonoidalClosed C] [MonoidalClosed D]
    [PreservesLimitsOfShape (Discrete WalkingPair) F]
    [PreservesLimitsOfShape (Discrete WalkingPair) H] in
/-- Product comparisons are natural in an isomorphism of functors. -/
theorem product_naturalIso (change : F ≅ H) (A B : C) :
    prodComparison F A B ≫ (change.hom.app A ⊗ₘ change.hom.app B) =
      change.hom.app (A ⊗ B) ≫ prodComparison H A B := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, tensorHom_fst, prodComparison_fst, prodComparison_fst_assoc]
    exact change.hom.naturality (fst A B)
  · simp only [Category.assoc, tensorHom_snd, prodComparison_snd, prodComparison_snd_assoc]
    exact change.hom.naturality (snd A B)

omit [MonoidalClosed C] [MonoidalClosed D] in
/-- The inverse product comparisons retain the change in both object
arguments. -/
theorem product_inverse_naturalIso (change : F ≅ H) (A B : C) :
    change.inv.app A ▷ F.obj B ≫ inv (prodComparison F A B) ≫
        change.hom.app (A ⊗ B) =
      H.obj A ◁ change.hom.app B ≫ inv (prodComparison H A B) := by
  apply (cancel_mono (prodComparison H A B)).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← product_naturalIso change A B]
  simp only [IsIso.inv_hom_id_assoc]
  rw [tensorHom_def]
  rw [← Category.assoc, ← comp_whiskerRight]
  simp only [change.inv_hom_id_app,
    id_whiskerRight, Category.id_comp]

/-- The exponential comparison commutes with an actual change of
functor, including the contravariant domain component. -/
theorem exponential_naturalIso (change : F ≅ H) (A B : C) :
    (expComparison F A).natTrans.app B ≫
        (pre (change.inv.app A)).app (F.obj B) ≫
        (ihom (H.obj A)).map (change.hom.app B) =
      change.hom.app ((ihom A).obj B) ≫ (expComparison H A).natTrans.app B := by
  apply uncurry_injective
  rw [← Category.assoc, uncurry_natural_right, uncurry_pre_app,
    uncurry_expComparison, uncurry_natural_left, uncurry_expComparison]
  simp only [Category.assoc]
  have naturality := change.hom.naturality ((ihom.ev A).app B)
  change F.map ((ihom.ev A).app B) ≫ change.hom.app B =
    change.hom.app (A ⊗ (ihom A).obj B) ≫ H.map ((ihom.ev A).app B) at naturality
  rw [naturality]
  simpa only [Functor.comp_obj, Category.assoc] using
    congrArg (fun arrow => arrow ≫ H.map ((ihom.ev A).app B))
      (product_inverse_naturalIso change A ((ihom A).obj B))

/-- Closedness is invariant under the actual isomorphism of functors,
with no equality of their chosen object presentations required. -/
theorem closed_of_naturalIso (change : F ≅ H) [MonoidalClosedFunctor H] :
    MonoidalClosedFunctor F where
  comparison_iso A := by
    have (B : C) : IsIso ((expComparison F A).natTrans.app B) := by
      have : IsIso (pre (change.inv.app A)) := by
        change IsIso (internalHom.map (Quiver.Hom.op (change.inv.app A)))
        infer_instance
      have : IsIso ((expComparison F A).natTrans.app B ≫
          (pre (change.inv.app A)).app (F.obj B) ≫
          (ihom (H.obj A)).map (change.hom.app B)) := by
        rw [exponential_naturalIso change A B]
        infer_instance
      exact IsIso.of_isIso_comp_right ((expComparison F A).natTrans.app B)
        ((pre (change.inv.app A)).app (F.obj B) ≫
          (ihom (H.obj A)).map (change.hom.app B))
    exact NatIso.isIso_of_isIso_app _

variable (F)

/-- A closed interpretation which reflects isomorphisms also reflects
closedness of any product-preserving functor before it. -/
theorem closed_of_composition [G.ReflectsIsomorphisms]
    [MonoidalClosedFunctor G] [MonoidalClosedFunctor (F ⋙ G)] :
    MonoidalClosedFunctor F where
  comparison_iso A := by
    have (B : C) : IsIso ((expComparison F A).natTrans.app B) := by
      have : IsIso (G.map ((expComparison F A).natTrans.app B) ≫
          (expComparison G (F.obj A)).natTrans.app (F.obj B)) := by
        rw [← exponential_composition]
        infer_instance
      have : IsIso (G.map ((expComparison F A).natTrans.app B)) :=
        IsIso.of_isIso_comp_right (G.map ((expComparison F A).natTrans.app B))
          ((expComparison G (F.obj A)).natTrans.app (F.obj B))
      exact isIso_of_reflects_iso _ G
    exact NatIso.isIso_of_isIso_app _

/-- The chosen comparison of the identity functor really is the identity
on the complete exponential object. -/
theorem exponential_identity (A B : C) :
    (expComparison (𝟭 C) A).natTrans.app B = 𝟙 ((ihom A).obj B) := by
  apply uncurry_injective
  rw [uncurry_expComparison, uncurry_id_eq_ev (A := A) (X := B)]
  have inverse : inv (prodComparison (𝟭 C) A ((ihom A).obj B)) =
      𝟙 (A ⊗ (ihom A).obj B) :=
    IsIso.inv_eq_of_hom_inv_id (by
      rw [prodComparison_id]
      exact Category.id_comp (𝟙 (A ⊗ (ihom A).obj B)))
  rw [inverse, Functor.id_map]
  exact Category.id_comp ((ihom.ev A).app B)

end Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence
