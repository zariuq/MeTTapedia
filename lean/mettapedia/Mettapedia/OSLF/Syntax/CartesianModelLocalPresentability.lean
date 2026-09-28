import Mettapedia.OSLF.Syntax.CartesianModelReflection
import Mathlib.CategoryTheory.Presentable.Adjunction
import Mathlib.CategoryTheory.Presentable.Type

/-!
# Local finite presentability of authored cartesian models

The category of set-valued interpretations preserving an authored small
category's finite context products is locally finitely presentable.  The
proof uses the explicit terminal and binary-product localizing maps, whose
endpoints were shown finitely presentable, rather than assuming an abstract
reflection preserves filtered colimits.

This provides the model-theoretic starting point for a relative finite-limit
presentation. It does not add the generated operations, exponentials, or
proof-relevant reductions of the full classifying theory.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.CartesianContextModels

open CategoryTheory CategoryTheory.Limits
open Mettapedia.OSLF.FormalFiniteLimits (CovariantPresheaf)

variable (C : Type) [SmallCategory C]

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- The covariant representables are dense: every interpretation is a
colimit of its represented elements. This follows by transporting the
ordinary Yoneda density theorem across double-opposite equivalence. -/
theorem coyoneda_dense : (coyoneda (C := C)).IsDense := by
  let e : (Cᵒᵖᵒᵖ ⥤ Type) ≌ (C ⥤ Type) :=
    (opOpEquivalence C).congrLeft
  have : (e.functor).IsEquivalence := e.isEquivalence_functor
  have hd : ((yoneda (C := Cᵒᵖ)) ⋙ e.functor).IsDense := inferInstance
  exact Functor.IsDense.of_iso (Coyoneda.opIso (C := C))

/-- Covariant presheaves are locally finitely presentable. This explicit
variance bridge is needed because Mathlib's presheaf instance is phrased
contravariantly. -/
theorem covariant_presheaves_locally_finitely_presentable :
    IsCardinalLocallyPresentable
      (CovariantPresheaf C) Cardinal.aleph0.{0} := by
  let P : ObjectProperty (CovariantPresheaf C) :=
    ObjectProperty.ofObj (coyoneda (C := C)).obj
  have hd : (coyoneda (C := C)).IsDense := coyoneda_dense C
  have hgen : P.IsStrongGenerator := by
    exact Functor.isStrongGenerator_of_isDense (coyoneda (C := C))
  have hsmall : ObjectProperty.Small.{0} P := inferInstance
  apply (IsCardinalLocallyPresentable.iff_exists_isStrongGenerator
    (CovariantPresheaf C) Cardinal.aleph0).2
  refine ⟨P, hsmall, hgen, ?_⟩
  intro X hX
  change ObjectProperty.ofObj (coyoneda (C := C)).obj X at hX
  cases hX with
  | mk Y => exact represented_presentable C Cardinal.aleph0 Y.unop

variable [HasFiniteProducts C]

/-- Product-preserving set-valued interpretations of a small authored context
category form a locally finitely presentable category. -/
theorem models_locally_finitely_presentable :
    IsCardinalLocallyPresentable (Models C) Cardinal.aleph0.{0} := by
  have hambient : IsCardinalLocallyPresentable
      (CovariantPresheaf C) Cardinal.aleph0.{0} :=
    covariant_presheaves_locally_finitely_presentable C
  have hlocal : IsCardinalLocallyPresentable
      (cartesianLaws C).isLocal.FullSubcategory Cardinal.aleph0 :=
    MorphismProperty.isLocallyPresentable_isLocal
    (cartesianLaws C) Cardinal.aleph0
      (fun {A B} f hf => cartesianLaws_endpoints_presentable C f hf)
  have heq : ProductModel C = (cartesianLaws C).isLocal :=
    productModel_eq_cartesianLocal C
  exact (congrArg (fun P : ObjectProperty (CovariantPresheaf C) =>
    IsCardinalLocallyPresentable P.FullSubcategory Cardinal.aleph0)
      heq.symm).mp hlocal

/-- The inclusion of cartesian models preserves filtered colimits. This is
the accessibility input used to transport finite presentability through
cartesian reflection. -/
theorem model_inclusion_finitary :
    ((ProductModel C).ι).IsCardinalAccessible Cardinal.aleph0.{0} := by
  have ha : ((cartesianLaws C).isLocal.ι).IsCardinalAccessible
      Cardinal.aleph0.{0} :=
    MorphismProperty.isCardinalAccessible_ι_isLocal
      (cartesianLaws C) Cardinal.aleph0
        (fun {A B} f hf => cartesianLaws_endpoints_presentable C f hf)
  have heq : ProductModel C = (cartesianLaws C).isLocal :=
    productModel_eq_cartesianLocal C
  exact (congrArg (fun P : ObjectProperty (CovariantPresheaf C) =>
    P.ι.IsCardinalAccessible Cardinal.aleph0) heq.symm).mp ha

/-- A represented authored context is finitely presentable in the category
of cartesian models itself, not only in the surrounding presheaf category. -/
theorem represented_model_presentable (X : Cᵒᵖ) :
    IsCardinalPresentable ((representedContext C).obj X)
      Cardinal.aleph0.{0} := by
  have hinc : ((ProductModel C).ι).IsCardinalAccessible Cardinal.aleph0 :=
    model_inclusion_finitary C
  have hamb : IsCardinalPresentable
      (coyoneda.obj X : CovariantPresheaf C) Cardinal.aleph0 :=
    represented_presentable C Cardinal.aleph0 X.unop
  have hreflect : IsCardinalPresentable
      ((cartesianReflection C).obj (coyoneda.obj X))
      Cardinal.aleph0 :=
    (cartesianReflectionAdjunction C).isCardinalPresentable_leftAdjoint_obj
      Cardinal.aleph0 (coyoneda.obj X)
  have hcounit : IsIso ((cartesianReflectionAdjunction C).counit.app
      ((representedContext C).obj X)) := by
    change IsIso ((reflectorAdjunction (ProductModel C).ι).counit.app
      ((representedContext C).obj X))
    infer_instance
  have hiso : (cartesianReflection C).obj (coyoneda.obj X) ≅
      (representedContext C).obj X := by
    let f : (cartesianReflection C).obj (coyoneda.obj X) ⟶
        (representedContext C).obj X :=
      (cartesianReflectionAdjunction C).counit.app
        ((representedContext C).obj X)
    haveI hf : IsIso f := hcounit
    exact asIso f
  exact isCardinalPresentable_of_iso hiso Cardinal.aleph0

end Mettapedia.OSLF.CartesianContextModels
