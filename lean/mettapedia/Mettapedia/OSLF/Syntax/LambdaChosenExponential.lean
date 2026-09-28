import Mettapedia.OSLF.Syntax.LambdaExponentialComparison
import Mathlib.CategoryTheory.Monoidal.Closed.Types

/-!
# The Chapter 7 binder body as the chosen presheaf internal hom

The explicit binder-body presheaf has a hom-set exponential property. This
module compares it with Mathlib's chosen internal hom, proves the comparison
is natural in every test presheaf and gives inverse maps. Transporting chosen
evaluation agrees with capture-avoiding body application. Authored beta
remains an operational reduction, rather than equality of raw syntax.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Mettapedia.OSLF.Binding.LambdaExponentialComparison

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalClosed
open Mettapedia.OSLF.Binding.LambdaCategoricalModel
open Mettapedia.OSLF.Binding.LambdaPresheafOperations
open Mettapedia.OSLF.Binding.ContextualTermAbstraction
open Mettapedia.OSLF.Binding.LambdaContextualRung

noncomputable def tensorToPointwise (F : Base ⥤ Type) :
    Programs ⊗ F ≅ FunctorToTypes.prod F Programs :=
  (CartesianMonoidalCategory.tensorLeftIsoProd Programs).app F ≪≫
    prod.braiding Programs F ≪≫
      FunctorToTypes.binaryProductIso F Programs

noncomputable def chosenCurryEquiv (F : Base ⥤ Type) :
    (FunctorToTypes.prod F Programs ⟶ Programs) ≃
      (F ⟶ (ihom Programs).obj Programs) where
  toFun f := MonoidalClosed.curry ((tensorToPointwise F).hom ≫ f)
  invFun g := (tensorToPointwise F).inv ≫ MonoidalClosed.uncurry g
  left_inv f := by
    simp [MonoidalClosed.uncurry_curry]
  right_inv g := by
    simp [MonoidalClosed.curry_uncurry]

theorem binaryProductIso_natural_left {G F : Base ⥤ Type} (α : G ⟶ F) :
    prod.map α (𝟙 Programs) ≫
        (FunctorToTypes.binaryProductIso F Programs).hom =
      (FunctorToTypes.binaryProductIso G Programs).hom ≫
        productPrecompose Srt.term α := by
  have leftProjection :
      productPrecompose Srt.term α ≫ FunctorToTypes.prod.fst =
        FunctorToTypes.prod.fst ≫ α := by
    ext X pair
    rfl
  have rightProjection :
      productPrecompose Srt.term α ≫ FunctorToTypes.prod.snd =
        FunctorToTypes.prod.snd := by
    ext X pair
    rfl
  have fstEqual :
      (prod.map α (𝟙 Programs) ≫
        (FunctorToTypes.binaryProductIso F Programs).hom) ≫
          FunctorToTypes.prod.fst =
      ((FunctorToTypes.binaryProductIso G Programs).hom ≫
        productPrecompose Srt.term α) ≫ FunctorToTypes.prod.fst := by
    simp only [Category.assoc, FunctorToTypes.binaryProductIso_hom_comp_fst,
      prod.map_fst, leftProjection]
    rw [← Category.assoc,
      FunctorToTypes.binaryProductIso_hom_comp_fst]
  have sndEqual :
      (prod.map α (𝟙 Programs) ≫
        (FunctorToTypes.binaryProductIso F Programs).hom) ≫
          FunctorToTypes.prod.snd =
      ((FunctorToTypes.binaryProductIso G Programs).hom ≫
        productPrecompose Srt.term α) ≫ FunctorToTypes.prod.snd := by
    simp only [Category.assoc, FunctorToTypes.binaryProductIso_hom_comp_snd,
      prod.map_snd, rightProjection, Category.comp_id]
  ext X pair
  · exact congrArg (fun h => h.app X pair) fstEqual
  · exact congrArg (fun h => h.app X pair) sndEqual

theorem tensorToPointwise_natural {G F : Base ⥤ Type} (α : G ⟶ F) :
    Programs ◁ α ≫ (tensorToPointwise F).hom =
      (tensorToPointwise G).hom ≫ productPrecompose Srt.term α := by
  have first :
      Programs ◁ α ≫ (tensorLeftIsoProd Programs).hom.app F =
        (tensorLeftIsoProd Programs).hom.app G ≫ prod.map (𝟙 Programs) α :=
    (tensorLeftIsoProd Programs).hom.naturality α
  have second :
      prod.map (𝟙 Programs) α ≫ (prod.braiding Programs F).hom =
        (prod.braiding Programs G).hom ≫ prod.map α (𝟙 Programs) :=
    braid_natural (𝟙 Programs) α
  change Programs ◁ α ≫
        (tensorLeftIsoProd Programs).hom.app F ≫
          (prod.braiding Programs F).hom ≫
            (FunctorToTypes.binaryProductIso F Programs).hom =
      (tensorLeftIsoProd Programs).hom.app G ≫
        (prod.braiding Programs G).hom ≫
          (FunctorToTypes.binaryProductIso G Programs).hom ≫
            productPrecompose Srt.term α
  rw [← Category.assoc (Programs ◁ α), first]
  simp only [Category.assoc]
  rw [← Category.assoc (prod.map (𝟙 Programs) α), second]
  simp only [Category.assoc]
  rw [binaryProductIso_natural_left α]

theorem chosenCurryEquiv_natural_test {G F : Base ⥤ Type}
    (α : G ⟶ F) (op : FunctorToTypes.prod F Programs ⟶ Programs) :
    chosenCurryEquiv G (productPrecompose Srt.term α ≫ op) =
      α ≫ chosenCurryEquiv F op := by
  change MonoidalClosed.curry
      ((tensorToPointwise G).hom ≫ productPrecompose Srt.term α ≫ op) =
    α ≫ MonoidalClosed.curry ((tensorToPointwise F).hom ≫ op)
  calc
    MonoidalClosed.curry
        ((tensorToPointwise G).hom ≫ productPrecompose Srt.term α ≫ op) =
      MonoidalClosed.curry
        (((tensorToPointwise G).hom ≫ productPrecompose Srt.term α) ≫ op) := by
          rw [Category.assoc]
    _ = MonoidalClosed.curry
        ((Programs ◁ α ≫ (tensorToPointwise F).hom) ≫ op) := by
          rw [tensorToPointwise_natural α]
    _ = α ≫ MonoidalClosed.curry ((tensorToPointwise F).hom ≫ op) := by
          rw [Category.assoc, MonoidalClosed.curry_natural_left]

theorem chosenUncurryEquiv_natural_test {G F : Base ⥤ Type}
    (α : G ⟶ F) (body : F ⟶ (ihom Programs).obj Programs) :
    (chosenCurryEquiv G).symm (α ≫ body) =
      productPrecompose Srt.term α ≫ (chosenCurryEquiv F).symm body := by
  apply (chosenCurryEquiv G).injective
  rw [chosenCurryEquiv_natural_test]
  simp only [Equiv.apply_symm_apply]

/-- Compare the explicit binder-body representation with Mathlib's chosen
internal-hom object for the two program presheaves. -/
noncomputable def bodyToChosen :
    Bodies ⟶ (ihom Programs).obj Programs :=
  chosenCurryEquiv Bodies ((lambdaHomEquiv Bodies).symm (𝟙 Bodies))

noncomputable def chosenToBody :
    (ihom Programs).obj Programs ⟶ Bodies :=
  lambdaHomEquiv ((ihom Programs).obj Programs)
    ((chosenCurryEquiv ((ihom Programs).obj Programs)).symm
      (𝟙 ((ihom Programs).obj Programs)))

theorem bodyToChosen_chosenToBody :
    bodyToChosen ≫ chosenToBody = 𝟙 Bodies := by
  apply (lambdaHomEquiv Bodies).symm.injective
  have h : (lambdaHomEquiv Bodies).symm (bodyToChosen ≫ chosenToBody) =
      productPrecompose Srt.term bodyToChosen ≫
        (lambdaHomEquiv ((ihom Programs).obj Programs)).symm chosenToBody := by
    simpa [lambdaHomEquiv, boundTermHomEquiv, Equiv.symm] using
      (uncurryBody_natural_test Srt.term Srt.term bodyToChosen chosenToBody)
  rw [h]
  rw [chosenToBody, Equiv.symm_apply_apply]
  apply (chosenCurryEquiv Bodies).injective
  rw [chosenCurryEquiv_natural_test]
  simp only [Equiv.apply_symm_apply, Category.comp_id]
  rfl

theorem chosenToBody_bodyToChosen :
    chosenToBody ≫ bodyToChosen = 𝟙 ((ihom Programs).obj Programs) := by
  apply (chosenCurryEquiv ((ihom Programs).obj Programs)).symm.injective
  have h :
      (chosenCurryEquiv ((ihom Programs).obj Programs)).symm
        (chosenToBody ≫ bodyToChosen) =
        productPrecompose Srt.term chosenToBody ≫
          (chosenCurryEquiv Bodies).symm bodyToChosen :=
    chosenUncurryEquiv_natural_test chosenToBody bodyToChosen
  rw [h, bodyToChosen, Equiv.symm_apply_apply]
  apply (lambdaHomEquiv ((ihom Programs).obj Programs)).injective
  change curryBody ((ihom Programs).obj Programs) Srt.term Srt.term
      (productPrecompose Srt.term chosenToBody ≫
        (lambdaHomEquiv Bodies).symm (𝟙 Bodies)) =
    (lambdaHomEquiv ((ihom Programs).obj Programs))
      ((chosenCurryEquiv ((ihom Programs).obj Programs)).symm
        (𝟙 ((ihom Programs).obj Programs)))
  rw [curryBody_natural_test]
  have bodyId :
      curryBody Bodies Srt.term Srt.term
        ((lambdaHomEquiv Bodies).symm (𝟙 Bodies)) = 𝟙 Bodies := by
    change (lambdaHomEquiv Bodies)
      ((lambdaHomEquiv Bodies).symm (𝟙 Bodies)) = 𝟙 Bodies
    exact Equiv.apply_symm_apply (lambdaHomEquiv Bodies) (𝟙 Bodies)
  rw [bodyId, Category.comp_id]
  rfl

/-- The explicit body presheaf is isomorphic to the chosen presheaf
internal hom, compatibly with every test presheaf. -/
noncomputable def bodyChosenIso :
    Bodies ≅ (ihom Programs).obj Programs where
  hom := bodyToChosen
  inv := chosenToBody
  hom_inv_id := bodyToChosen_chosenToBody
  inv_hom_id := chosenToBody_bodyToChosen

/-- The chosen internal-hom evaluation, transported across the isomorphism,
is the authored capture-avoiding application of a binder body. -/
theorem chosenEvaluation_eq_exponentialEvaluation :
    (tensorToPointwise Bodies).inv ≫
        MonoidalClosed.uncurry bodyToChosen =
      exponentialEvaluation := by
  simp [chosenCurryEquiv, lambdaHomEquiv, boundTermHomEquiv,
    bodyToChosen, exponentialEvaluation, Equiv.symm]

/-- The chosen evaluation is capture-avoiding application in the authored
lambda model, including open contexts. -/
theorem chosenEvaluation_eq_bodyAt :
    (tensorToPointwise Bodies).inv ≫
        MonoidalClosed.uncurry bodyToChosen = bodyAt := by
  rw [chosenEvaluation_eq_exponentialEvaluation,
    exponentialEvaluation_eq_bodyAt]

/-- Authored beta uses the same chosen evaluation as its contractum while
retaining the redex as a distinct raw syntax tree. -/
theorem betaPairs_use_chosenEvaluation :
    betaPairs =
      FunctorToTypes.prod.lift betaRedex
        ((tensorToPointwise Bodies).inv ≫
          MonoidalClosed.uncurry bodyToChosen) ≫ sortedPairsIso.inv := by
  rw [chosenEvaluation_eq_exponentialEvaluation]
  exact betaPairs_use_exponentialEvaluation

end Mettapedia.OSLF.Binding.LambdaExponentialComparison
