import Mettapedia.CategoryTheory.ElementaryToposSliceFunctionSpace

/-!
# Transposition into the fibrewise function object

A supplied arrow on a source fibre is first classified as an actual
partial function, then transposed by the base exponential adjunction. Its
base equation proves membership in the function-space equalizer. The
complete partial-function readout and the base determine the transpose.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.ElementaryToposSliceFunctionSpace

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open ElementaryToposPartialMaps ElementaryToposStableEpimorphisms

universe u v
variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C]
variable [HasPullbacks C] [HasEqualizers C]
variable (classifier : Subobject.Classifier C)
variable {X Y B Z : C} (f : X ⟶ B) (g : Y ⟶ B)

abbrev sourceRelation (base : Z ⟶ B) : pullback f base ⟶ X ⊗ Z :=
  lift (pullback.fst _ _) (pullback.snd _ _)

instance sourceRelation_mono (base : Z ⟶ B) : Mono (sourceRelation f base) :=
  (graph_pullback (IsPullback.of_hasPullback f base).flip).mono_snd_of_mono

def parameterOfBody (base : Z ⟶ B) (body : pullback f base ⟶ Y) :
    Z ⟶ functionParameter classifier f g :=
  lift base (curry (classifyPartial classifier (sourceRelation f base) body))

theorem parameterOfBody_apply (base : Z ⟶ B) (body : pullback f base ⟶ Y) :
    X ◁ parameterOfBody classifier f g base body ≫ parameterApply classifier f g =
      classifyPartial classifier (sourceRelation f base) body := by
  dsimp [parameterApply, parameterOfBody]
  rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, lift_snd]
  exact whiskerLeft_curry_ihom_ev_app X _ _

theorem source_fibre_classification (base : Z ⟶ B) :
    classifyPartial classifier (sourceRelation f base) (pullback.fst f base ≫ f) =
      X ◁ base ≫ fibrePartial classifier f :=
  classifyPartial_substitution classifier (graph f) f
    (X ◁ base) (pullback.fst _ _) (sourceRelation f base)
    (graph_pullback (IsPullback.of_hasPullback f base).flip).flip

theorem parameterOfBody_condition (base : Z ⟶ B) (body : pullback f base ⟶ Y)
    (baseCondition : body ≫ g = pullback.fst f base ≫ f) :
    parameterOfBody classifier f g base body ≫ valueCondition classifier f g =
      parameterOfBody classifier f g base body ≫ domainCondition classifier f g := by
  apply uncurry_injective
  simp only [uncurry_natural_left, valueCondition, domainCondition, uncurry_curry]
  rw [← Category.assoc, parameterOfBody_apply,
    ← classifyPartial_postcomposition, baseCondition, source_fibre_classification]
  dsimp [parameterOfBody, parameterBase]
  rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, lift_fst]

def transpose (base : Z ⟶ B) (body : pullback f base ⟶ Y)
    (baseCondition : body ≫ g = pullback.fst f base ≫ f) : Z ⟶ functionSpace classifier f g :=
  equalizer.lift (parameterOfBody classifier f g base body)
    (parameterOfBody_condition classifier f g base body baseCondition)

@[reassoc (attr := simp)] theorem transpose_inclusion (base : Z ⟶ B)
    (body : pullback f base ⟶ Y) (baseCondition : body ≫ g = pullback.fst f base ≫ f) :
    transpose classifier f g base body baseCondition ≫ functionInclusion classifier f g =
      parameterOfBody classifier f g base body := equalizer.lift_ι _ _

@[reassoc (attr := simp)] theorem transpose_base (base : Z ⟶ B)
    (body : pullback f base ⟶ Y) (baseCondition : body ≫ g = pullback.fst f base ≫ f) :
    transpose classifier f g base body baseCondition ≫ functionBase classifier f g = base := by
  rw [functionBase, ← Category.assoc, transpose_inclusion]
  exact lift_fst _ _

theorem transpose_apply (base : Z ⟶ B) (body : pullback f base ⟶ Y)
    (baseCondition : body ≫ g = pullback.fst f base ≫ f) :
    X ◁ transpose classifier f g base body baseCondition ≫ functionApply classifier f g =
      classifyPartial classifier (sourceRelation f base) body := by
  rw [functionApply, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, transpose_inclusion]
  exact parameterOfBody_apply classifier f g base body

theorem functionApply_curry : curry (functionApply classifier f g) =
    functionInclusion classifier f g ≫ snd B ((ihom X).obj (partialObject classifier Y)) := by
  apply uncurry_injective
  rw [uncurry_curry, uncurry_eq]
  dsimp [functionApply, parameterApply]
  rw [MonoidalCategory.whiskerLeft_comp, Category.assoc]

theorem transpose_unique (base : Z ⟶ B) (body : pullback f base ⟶ Y)
    (baseCondition : body ≫ g = pullback.fst f base ≫ f)
    (other : Z ⟶ functionSpace classifier f g)
    (base_readout : other ≫ functionBase classifier f g = base)
    (function_readout : X ◁ other ≫ functionApply classifier f g =
      classifyPartial classifier (sourceRelation f base) body) :
    other = transpose classifier f g base body baseCondition := by
  apply (cancel_mono (functionInclusion classifier f g)).mp
  rw [transpose_inclusion]
  apply CartesianMonoidalCategory.hom_ext
  · simpa only [parameterOfBody, lift_fst, parameterBase, functionBase, Category.assoc] using base_readout
  · have curried := congrArg curry function_readout
    rw [curry_natural_left, functionApply_curry] at curried
    simpa only [parameterOfBody, lift_snd, Category.assoc] using curried

end Mettapedia.CategoryTheory.ElementaryToposSliceFunctionSpace
