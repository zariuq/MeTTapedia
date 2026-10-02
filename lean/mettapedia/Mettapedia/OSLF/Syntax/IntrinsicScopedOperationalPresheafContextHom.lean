import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafEvents

/-!
# Contextual presheaf functions are actual context extensions

The product-context/Yoneda comparison holds for every presheaf, including
retained event fibers. It reads natural functions at the extended context
and reconstructs them by genuine presheaf restriction.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafContextHom

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open IntrinsicScopedConditionalPresheaf (Base)
open IntrinsicScopedOperationalPresheafEvents (binderExtension)
open MultiBinderPresheaf (binders extendScope)

universe u
variable {S : Signature}

private abbrev Extended (A : BindingCloneAlgebra.Algebra.{u} S) (Γ : Ctx S) (X : Base A) :=
  concat A.substitution.toClone (ContextObject.ofList A.substitution.toClone Γ) X.unop

private def fromTensorNat (A : BindingCloneAlgebra.Algebra.{u} S) (Γ : Ctx S)
    (F : Base A ⥤ Type u) (X : Base A)
    (f : (binders A Γ ⊗ yoneda.obj X.unop) ⟶ F) :
    F.obj ((binderExtension A Γ).obj X) :=
  f.app (Opposite.op (Extended A Γ X))
    (fstProjection A.substitution.toClone _ _, sndProjection A.substitution.toClone _ _)

private def toTensorNat (A : BindingCloneAlgebra.Algebra.{u} S) (Γ : Ctx S)
    (F : Base A ⥤ Type u) (X : Base A)
    (value : F.obj ((binderExtension A Γ).obj X)) :
    (binders A Γ ⊗ yoneda.obj X.unop) ⟶ F where
  app stage := TypeCat.ofHom (fun input => F.map (Quiver.Hom.op
    (pair A.substitution.toClone input.1 input.2)) value)
  naturality stage other arrow := by
    apply ConcreteCategory.hom_ext
    rintro ⟨argument, environment⟩
    change stage.unop ⟶ ContextObject.ofList A.substitution.toClone Γ at argument
    change stage.unop ⟶ X.unop at environment
    have paired : pair A.substitution.toClone (arrow.unop ≫ argument)
        (arrow.unop ≫ environment) = arrow.unop ≫ pair A.substitution.toClone argument environment := by
      symm
      apply categorical_pair_unique A.substitution.toClone
      · rw [Category.assoc, categorical_pair_fst]
      · rw [Category.assoc, categorical_pair_snd]
    change F.map (Quiver.Hom.op (pair A.substitution.toClone
      (arrow.unop ≫ argument) (arrow.unop ≫ environment))) value =
      F.map arrow (F.map (Quiver.Hom.op (pair A.substitution.toClone argument environment)) value)
    rw [paired]
    exact ConcreteCategory.congr_hom (F.map_comp _ _) value

private def tensorNatEquiv (A : BindingCloneAlgebra.Algebra.{u} S) (Γ : Ctx S)
    (F : Base A ⥤ Type u) (X : Base A) :
    ((binders A Γ ⊗ yoneda.obj X.unop) ⟶ F) ≃
      F.obj ((binderExtension A Γ).obj X) where
  toFun := fromTensorNat A Γ F X
  invFun := toTensorNat A Γ F X
  left_inv f := by
    apply NatTrans.ext
    funext stage
    apply ConcreteCategory.hom_ext
    rintro ⟨argument, environment⟩
    change stage.unop ⟶ ContextObject.ofList A.substitution.toClone Γ at argument
    change stage.unop ⟶ X.unop at environment
    let C := A.substitution.toClone
    let canonical : (binders A Γ ⊗ yoneda.obj X.unop).obj
        (Opposite.op (Extended A Γ X)) :=
      (fstProjection C _ _, sndProjection C _ _)
    have natural := f.naturality_apply (Quiver.Hom.op (pair C argument environment)) canonical
    change f.app stage
        (pair C argument environment ≫ fstProjection C _ _,
          pair C argument environment ≫ sndProjection C _ _) =
      F.map (Quiver.Hom.op (pair C argument environment))
        (fromTensorNat A Γ F X f) at natural
    rw [categorical_pair_fst, categorical_pair_snd] at natural
    exact natural.symm
  right_inv value := by
    change F.map (Quiver.Hom.op (pair A.substitution.toClone
      (fstProjection A.substitution.toClone _ _) (sndProjection A.substitution.toClone _ _))) value = value
    have paired : pair A.substitution.toClone (fstProjection A.substitution.toClone _ _)
        (sndProjection A.substitution.toClone _ _) = 𝟙 (Extended A Γ X) := by
      simpa only [Category.id_comp] using
        categorical_pair_eta A.substitution.toClone (𝟙 (Extended A Γ X))
    rw [paired]
    exact ConcreteCategory.congr_hom (F.map_id _) value

/-- At each stage, a contextual function is exactly a value at the extended context. -/
def contextHomAtEquiv (A : BindingCloneAlgebra.Algebra.{u} S) (Γ : Ctx S)
    (F : Base A ⥤ Type u) (X : Base A) :
    ((binders A Γ).functorHom F).obj X ≃ F.obj ((binderExtension A Γ).obj X) :=
  (yonedaEquiv.symm).trans ((FunctorToTypes.functorHomEquiv
    (binders A Γ) (yoneda.obj X.unop) F).trans (tensorNatEquiv A Γ F X))

/-- Read a contextual function at the actual extended context and its projections. -/
theorem contextHomAtEquiv_apply (A : BindingCloneAlgebra.Algebra.{u} S) (Γ : Ctx S)
    (F : Base A ⥤ Type u) (X : Base A)
    (function : ((binders A Γ).functorHom F).obj X) :
    contextHomAtEquiv A Γ F X function =
      function.app (Opposite.op (Extended A Γ X))
        (Quiver.Hom.op (sndProjection A.substitution.toClone _ _))
        (fstProjection A.substitution.toClone _ _) := by
  change fromTensorNat A Γ F X
    ((FunctorToTypes.functorHomEquiv (binders A Γ) (yoneda.obj X.unop) F)
      (yonedaEquiv.symm function)) = _
  change function.app (Opposite.op (Extended A Γ X))
    (Quiver.Hom.op (sndProjection A.substitution.toClone _ _) ≫ 𝟙 _)
    (fstProjection A.substitution.toClone _ _) = _
  rw [Category.comp_id]

/-- Context extension is natural for every presheaf and every ambient substitution. -/
theorem contextHomAtEquiv_reindex (A : BindingCloneAlgebra.Algebra.{u} S) (Γ : Ctx S)
    (F : Base A ⥤ Type u) {X Y : Base A} (f : X ⟶ Y)
    (function : ((binders A Γ).functorHom F).obj X) :
    contextHomAtEquiv A Γ F Y (((binders A Γ).functorHom F).map f function) =
      F.map ((binderExtension A Γ).map f) (contextHomAtEquiv A Γ F X function) := by
  rw [contextHomAtEquiv_apply, contextHomAtEquiv_apply]
  let input := ContextObject.ofList A.substitution.toClone Γ
  let extension := extendScope A Γ f.unop
  have natural := function.naturality (Quiver.Hom.op extension)
    (Quiver.Hom.op (sndProjection A.substitution.toClone input X.unop))
  have pointwise := ConcreteCategory.congr_hom natural
    (fstProjection A.substitution.toClone input X.unop)
  change function.app (Opposite.op (Extended A Γ Y))
      (Quiver.Hom.op (sndProjection A.substitution.toClone input X.unop) ≫
        Quiver.Hom.op extension)
      (extension ≫ fstProjection A.substitution.toClone input X.unop) =
    F.map (Quiver.Hom.op extension)
      (function.app (Opposite.op (Extended A Γ X))
        (Quiver.Hom.op (sndProjection A.substitution.toClone input X.unop))
        (fstProjection A.substitution.toClone input X.unop)) at pointwise
  have sndLaw : Quiver.Hom.op (sndProjection A.substitution.toClone input X.unop) ≫
      Quiver.Hom.op extension = f ≫
        Quiver.Hom.op (sndProjection A.substitution.toClone input Y.unop) := by
    simpa only [op_comp, Quiver.Hom.op_unop] using congrArg Quiver.Hom.op
      (MultiBinderPresheaf.extendScope_snd A Γ f.unop)
  rw [sndLaw, MultiBinderPresheaf.extendScope_fst] at pointwise
  exact pointwise

/-- Whole-context functions into an arbitrary presheaf are its context-extension pullback. -/
def contextHomIso (A : BindingCloneAlgebra.Algebra.{u} S) (Γ : Ctx S)
    (F : Base A ⥤ Type u) : (binders A Γ).functorHom F ≅ binderExtension A Γ ⋙ F :=
  NatIso.ofComponents (fun X => (contextHomAtEquiv A Γ F X).toIso)
    (fun f => ConcreteCategory.hom_ext _ _ (contextHomAtEquiv_reindex A Γ F f))

/-- Applying a natural map to contextual functions reads its component at the extended context. -/
theorem contextHomAtEquiv_map (A : BindingCloneAlgebra.Algebra.{u} S) (Γ : Ctx S)
    {F G : Base A ⥤ Type u} (map : F ⟶ G) (X : Base A)
    (function : ((binders A Γ).functorHom F).obj X) :
    contextHomAtEquiv A Γ G X
        (((FunctorToTypes.rightAdj (binders A Γ)).map map).app X function) =
      map.app ((binderExtension A Γ).obj X) (contextHomAtEquiv A Γ F X function) := by
  let mapped : ((binders A Γ).functorHom G).obj X :=
    ((FunctorToTypes.rightAdj (binders A Γ)).map map).app X function
  exact (contextHomAtEquiv_apply A Γ G X mapped).trans
    (congrArg (map.app ((binderExtension A Γ).obj X))
      (contextHomAtEquiv_apply A Γ F X function).symm)

end Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafContextHom
