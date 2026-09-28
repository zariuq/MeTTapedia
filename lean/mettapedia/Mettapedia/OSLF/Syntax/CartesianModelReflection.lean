import Mettapedia.OSLF.Syntax.CartesianModelOrthogonality
import Mathlib.CategoryTheory.Presentable.OrthogonalReflection
import Mathlib.CategoryTheory.Presentable.Presheaf
import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# Reflection into cartesian interpretations of authored contexts

The orthogonality presentation of finite-product preservation has a small
family of generating maps. Their endpoints are finitely presentable, so the
orthogonal-reflection construction applies without an extra preservation
assumption. This yields the actual left adjoint to the inclusion of
cartesian models and its idempotent monad on the presheaf category.

This reflection imposes the authored context-product equations. It is one
component of a relative classifying construction, not the free extension by
operations, predicates, exponentials or proof-relevant reductions.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open Mettapedia.OSLF.FormalFiniteLimits (CovariantPresheaf)

set_option autoImplicit false
namespace Mettapedia.OSLF.CartesianContextModels
variable (C : Type) [SmallCategory C]

/-- Covariant representables are presentable because maps out of them are
evaluation, and evaluation preserves the required filtered colimits. -/
theorem represented_presentable (κ : Cardinal.{0}) [Fact κ.IsRegular] (X : C) :
    IsCardinalPresentable
      (coyoneda.obj (op X) : CovariantPresheaf C) κ := by
  have heval : ((evaluation C Type).obj X).IsCardinalAccessible κ := by
    refine ⟨fun J _ _ => ?_⟩
    have : HasColimitsOfShape J Type := inferInstance
    infer_instance
  exact Functor.isCardinalAccessible_of_natIso
    ((curriedCoyonedaLemma (C := C)).app X).symm κ

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- A binary coproduct of represented contexts is finitely presentable in the
ambient presheaf category. -/
theorem represented_coprod_presentable (X Y : C) :
    IsCardinalPresentable
      ((coyoneda.obj (op X) ⨿ coyoneda.obj (op Y)) : CovariantPresheaf C)
      Cardinal.aleph0.{0} := by
  let A : CovariantPresheaf C := coyoneda.obj (op X)
  let B : CovariantPresheaf C := coyoneda.obj (op Y)
  have hJ : HasCardinalLT (Arrow (Discrete WalkingPair)) Cardinal.aleph0 :=
    hasCardinalLT_of_finite _ _ (le_refl _)
  have : ∀ k : Discrete WalkingPair,
      IsCardinalPresentable
        ((pair (coyoneda.obj (op X)) (coyoneda.obj (op Y))).obj k)
          Cardinal.aleph0 := by
    rintro ⟨k⟩
    cases k <;> exact represented_presentable C Cardinal.aleph0 _
  exact isCardinalPresentable_of_isColimit
    (BinaryCofan.mk (coprod.inl : A ⟶ A ⨿ B)
      (coprod.inr : B ⟶ A ⨿ B))
      (coprodIsCoprod A B) Cardinal.aleph0 hJ

/-- The initial presheaf is finitely presentable. -/
theorem initial_presentable :
    IsCardinalPresentable
      (⊥_ (CovariantPresheaf C)) Cardinal.aleph0.{0} := by
  let Z : CovariantPresheaf C := ⊥_ (CovariantPresheaf C)
  let c : Cocone (Functor.empty.{0} (CovariantPresheaf C)) :=
    asEmptyCocone Z
  have hc : IsColimit c :=
    (isColimitEquivIsInitialOfIsEmpty
      (C := CovariantPresheaf C) c).symm initialIsInitial
  have hJ : HasCardinalLT (Arrow (Discrete PEmpty.{1}))
      Cardinal.aleph0.{0} :=
    hasCardinalLT_of_finite _ _ (le_refl _)
  have : ∀ k : Discrete PEmpty.{1},
      IsCardinalPresentable ((Functor.empty.{0}
        (CovariantPresheaf C)).obj k) Cardinal.aleph0.{0} := by
    rintro ⟨k⟩
    cases k
  exact isCardinalPresentable_of_isColimit c hc Cardinal.aleph0 hJ

variable [HasFiniteProducts C]

/-- Every map imposing an authored cartesian law has finitely presentable
source and target, including the empty-context law. -/
theorem cartesianLaws_endpoints_presentable
    {A B : CovariantPresheaf C} (f : A ⟶ B)
    (hf : (cartesianLaws C) f) :
    IsCardinalPresentable A Cardinal.aleph0.{0} ∧
      IsCardinalPresentable B Cardinal.aleph0.{0} := by
  change (⨆ index, cartesianLawAt C index) f at hf
  obtain ⟨index, hindex⟩ :=
    (MorphismProperty.iSup_iff (cartesianLawAt C) f).mp hf
  cases index with
  | none =>
      change (MorphismProperty.single (terminalLocalizingMap C)) f at hindex
      cases hindex with
      | mk _ =>
          exact ⟨initial_presentable C,
            represented_presentable C Cardinal.aleph0 (⊤_ C)⟩
  | some pair =>
      rcases pair with ⟨X, Y⟩
      change (MorphismProperty.single (productLocalizingMap C X Y)) f at hindex
      cases hindex with
      | mk _ =>
          exact ⟨represented_coprod_presentable C X Y,
            represented_presentable C Cardinal.aleph0 (X ⨯ Y)⟩

/-- The small cartesian-law family admits its actual orthogonal reflection. -/
theorem cartesianLaws_reflective :
    (cartesianLaws C).isLocal.ι.IsRightAdjoint := by
  have : MorphismProperty.IsSmall.{0} (cartesianLaws C) := inferInstance
  have : LocallySmall.{0} (CovariantPresheaf C) := inferInstance
  have : HasColimitsOfSize.{0, 0} (CovariantPresheaf C) := inferInstance
  exact MorphismProperty.isRightAdjoint_ι_isLocal
    (cartesianLaws C) Cardinal.aleph0
      (fun {X Y} f hf => cartesianLaws_endpoints_presentable C f hf)

/-- The category of interpretations preserving the authored context products
is a reflective subcategory of all set-valued interpretations. -/
noncomputable instance productModel_reflective : Reflective (ProductModel C).ι := by
  have h : ((ProductModel C).ι).IsRightAdjoint := by
    rw [productModel_eq_cartesianLocal C]
    exact cartesianLaws_reflective C
  have : ((ProductModel C).ι).IsRightAdjoint := h
  exact ⟨((ProductModel C).ι).leftAdjoint,
    Adjunction.ofIsRightAdjoint (ProductModel C).ι⟩

/-- The reflector sends any interpretation to a cartesian model of the
authored context equations. -/
noncomputable def cartesianReflection : CovariantPresheaf C ⥤ Models C :=
  reflector (ProductModel C).ι

noncomputable def cartesianReflectionAdjunction :
    cartesianReflection C ⊣ (ProductModel C).ι :=
  reflectorAdjunction (ProductModel C).ι

/-- Universal property of cartesianization, stated as an explicit hom-set
equivalence for arbitrary interpretations and cartesian models. -/
noncomputable def cartesianReflectionHomEquiv
    (F : CovariantPresheaf C) (M : Models C) :
    ((cartesianReflection C).obj F ⟶ M) ≃
      (F ⟶ (ProductModel C).ι.obj M) :=
  (cartesianReflectionAdjunction C).homEquiv F M

/-- The monad imposes precisely the authored finite-product equations. It is
not the later generated-theory monad adjoining operations and reductions. -/
noncomputable def cartesianizationMonad : Monad (CovariantPresheaf C) :=
  (cartesianReflectionAdjunction C).toMonad

/-- Applying cartesianization twice imposes no further context equations. -/
instance cartesianizationMonad_mul_isIso :
    IsIso (cartesianizationMonad C).μ := by
  change IsIso (reflectorAdjunction (ProductModel C).ι).toMonad.μ
  infer_instance

/-- A model already satisfying the authored cartesian laws is unchanged by
reflection, up to the canonical unit isomorphism. -/
theorem cartesianReflection_model_unit_isIso (M : Models C) :
    IsIso ((cartesianReflectionAdjunction C).unit.app
      ((ProductModel C).ι.obj M)) := by
  change IsIso ((reflectorAdjunction (ProductModel C).ι).unit.app
    ((ProductModel C).ι.obj M))
  infer_instance

/-- The constant two-element interpretation is a genuine negative control:
its cartesianization unit cannot be an isomorphism. -/
theorem cartesianReflection_bool_unit_not_isIso :
    ¬ IsIso ((cartesianReflectionAdjunction C).unit.app
      ((Functor.const C).obj Bool)) := by
  intro h
  have : IsIso ((cartesianReflectionAdjunction C).unit.app
      ((Functor.const C).obj Bool)) := h
  have htarget : ProductModel C
      ((ProductModel C).ι.obj
        ((cartesianReflection C).obj ((Functor.const C).obj Bool))) :=
    ((cartesianReflection C).obj ((Functor.const C).obj Bool)).property
  have hsource : ProductModel C ((Functor.const C).obj Bool) :=
    (ProductModel C).prop_of_iso
      (asIso ((cartesianReflectionAdjunction C).unit.app
        ((Functor.const C).obj Bool))).symm htarget
  exact constantBool_not_model C hsource

end Mettapedia.OSLF.CartesianContextModels
