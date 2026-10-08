import Mettapedia.CategoryTheory.ElementaryToposSliceTranspose

/-!
# Complete transposition and substitution of fibrewise functions

Evaluation and transposition have both round trips. Substitution uses the
actual two projections of the fibre pullback and retains the complete
partial-function classification. These proofs precede the construction of
the slice adjunction.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.ElementaryToposSliceFunctionSpace

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open ElementaryToposPartialMaps

universe u v
variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C]
variable [HasPullbacks C] [HasEqualizers C]
variable (classifier : Subobject.Classifier C)
variable {X Y B Z : C} (f : X ⟶ B) (g : Y ⟶ B)

theorem classifyPartial_value_injective {object parameter selected : C}
    (inclusion : selected ⟶ parameter) [Mono inclusion] (first second : selected ⟶ object)
    (same : classifyPartial classifier inclusion first = classifyPartial classifier inclusion second) :
    first = second := by
  have witnesses : partialWitness classifier inclusion first = partialWitness classifier inclusion second := by
    apply (cancel_mono (domain classifier object)).mp
    rw [partialWitness_domain, partialWitness_domain, same]
  have values := congrArg (fun arrow => arrow ≫ value classifier object) witnesses
  simpa only [partialWitness_value] using values

omit [MonoidalClosed C] [HasEqualizers C] in
theorem source_relation_square {next : C} (earlierBase : next ⟶ B) (laterBase : Z ⟶ B)
    (arrow : next ⟶ Z) (baseEquation : arrow ≫ laterBase = earlierBase)
    (fibreArrow : pullback f earlierBase ⟶ pullback f laterBase)
    (first_readout : fibreArrow ≫ pullback.fst f laterBase = pullback.fst f earlierBase)
    (second_readout : fibreArrow ≫ pullback.snd f laterBase = pullback.snd f earlierBase ≫ arrow) :
    IsPullback (sourceRelation f earlierBase) fibreArrow (X ◁ arrow) (sourceRelation f laterBase) := by
  have entire : IsPullback (fibreArrow ≫ pullback.fst f laterBase)
      (pullback.snd f earlierBase) f (arrow ≫ laterBase) := by
    simpa only [first_readout, baseEquation] using IsPullback.of_hasPullback f earlierBase
  have fibres := entire.of_right second_readout (IsPullback.of_hasPullback f laterBase)
  have fibres' : IsPullback fibreArrow (pullback.snd f earlierBase)
      (sourceRelation f laterBase ≫ snd X Z) arrow := by
    simpa only [sourceRelation, lift_snd] using fibres
  have relation := relation_pullback (sourceRelation f laterBase) arrow fibreArrow
    (pullback.snd f earlierBase) fibres'
  simpa only [sourceRelation, Category.assoc, lift_fst, ← Category.assoc, first_readout] using relation

def fibreMap (base : Z ⟶ B) (function : Z ⟶ functionSpace classifier f g)
    (baseEquation : function ≫ functionBase classifier f g = base) :
    pullback f base ⟶ functionFibre classifier f g :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ function) (by
    rw [Category.assoc, baseEquation]
    exact pullback.condition)

@[reassoc (attr := simp)] theorem fibreMap_first (base : Z ⟶ B)
    (function : Z ⟶ functionSpace classifier f g)
    (baseEquation : function ≫ functionBase classifier f g = base) :
    fibreMap classifier f g base function baseEquation ≫ pullback.fst _ _ = pullback.fst f base :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem fibreMap_second (base : Z ⟶ B)
    (function : Z ⟶ functionSpace classifier f g)
    (baseEquation : function ≫ functionBase classifier f g = base) :
    fibreMap classifier f g base function baseEquation ≫ pullback.snd _ _ = pullback.snd f base ≫ function :=
  pullback.lift_snd _ _ _

theorem fibreMap_isPullback (base : Z ⟶ B) (function : Z ⟶ functionSpace classifier f g)
    (baseEquation : function ≫ functionBase classifier f g = base) :
    IsPullback (sourceRelation f base) (fibreMap classifier f g base function baseEquation)
      (X ◁ function) (fibreInclusion classifier f g) :=
  source_relation_square f base (functionBase classifier f g) function baseEquation
    (fibreMap classifier f g base function baseEquation)
    (fibreMap_first classifier f g base function baseEquation)
    (fibreMap_second classifier f g base function baseEquation)

def untranspose (base : Z ⟶ B) (function : Z ⟶ functionSpace classifier f g)
    (baseEquation : function ≫ functionBase classifier f g = base) : pullback f base ⟶ Y :=
  fibreMap classifier f g base function baseEquation ≫ evaluation classifier f g

@[reassoc (attr := simp)] theorem untranspose_base (base : Z ⟶ B)
    (function : Z ⟶ functionSpace classifier f g)
    (baseEquation : function ≫ functionBase classifier f g = base) :
    untranspose classifier f g base function baseEquation ≫ g = pullback.fst f base ≫ f := by
  rw [untranspose, Category.assoc, evaluation_base]
  exact fibreMap_first_assoc classifier f g base function baseEquation f

theorem untranspose_classification (base : Z ⟶ B)
    (function : Z ⟶ functionSpace classifier f g)
    (baseEquation : function ≫ functionBase classifier f g = base) :
    classifyPartial classifier (sourceRelation f base)
      (untranspose classifier f g base function baseEquation) = X ◁ function ≫ functionApply classifier f g := by
  rw [untranspose, classifyPartial_substitution classifier (fibreInclusion classifier f g)
    (evaluation classifier f g) (X ◁ function)
    (fibreMap classifier f g base function baseEquation) (sourceRelation f base)
    (fibreMap_isPullback classifier f g base function baseEquation), evaluation_classification]

theorem untranspose_transpose (base : Z ⟶ B) (body : pullback f base ⟶ Y)
    (baseCondition : body ≫ g = pullback.fst f base ≫ f) :
    untranspose classifier f g base (transpose classifier f g base body baseCondition)
      (transpose_base classifier f g base body baseCondition) = body := by
  apply classifyPartial_value_injective classifier (sourceRelation f base)
  rw [untranspose_classification, transpose_apply]

theorem transpose_untranspose (base : Z ⟶ B) (function : Z ⟶ functionSpace classifier f g)
    (baseEquation : function ≫ functionBase classifier f g = base) :
    transpose classifier f g base (untranspose classifier f g base function baseEquation)
      (untranspose_base classifier f g base function baseEquation) = function := by
  exact (transpose_unique classifier f g base
    (untranspose classifier f g base function baseEquation)
    (untranspose_base classifier f g base function baseEquation) function baseEquation
    (untranspose_classification classifier f g base function baseEquation).symm).symm

theorem transpose_substitution {next : C} (earlierBase : next ⟶ B) (laterBase : Z ⟶ B)
    (arrow : next ⟶ Z) (baseEquation : arrow ≫ laterBase = earlierBase)
    (fibreArrow : pullback f earlierBase ⟶ pullback f laterBase)
    (first_readout : fibreArrow ≫ pullback.fst f laterBase = pullback.fst f earlierBase)
    (second_readout : fibreArrow ≫ pullback.snd f laterBase = pullback.snd f earlierBase ≫ arrow)
    (body : pullback f laterBase ⟶ Y) (bodyBase : body ≫ g = pullback.fst f laterBase ≫ f) :
    transpose classifier f g earlierBase (fibreArrow ≫ body) (by
      rw [Category.assoc, bodyBase, ← Category.assoc, first_readout]) =
      arrow ≫ transpose classifier f g laterBase body bodyBase := by
  apply Eq.symm
  apply transpose_unique classifier f g earlierBase (fibreArrow ≫ body)
  · rw [Category.assoc, transpose_base, baseEquation]
  · rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, transpose_apply]
    exact (classifyPartial_substitution classifier (sourceRelation f laterBase) body
      (X ◁ arrow) fibreArrow (sourceRelation f earlierBase)
      (source_relation_square f earlierBase laterBase arrow baseEquation
        fibreArrow first_readout second_readout)).symm

end Mettapedia.CategoryTheory.ElementaryToposSliceFunctionSpace
