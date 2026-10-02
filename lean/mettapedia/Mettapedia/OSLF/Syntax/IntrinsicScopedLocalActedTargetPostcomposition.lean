import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedEquivalence
import Mettapedia.OSLF.Syntax.CategoricalBindingTargetPreservationEquations
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Qualified postcomposition of operational interpretations

Finite products, the selected binding exponentials and event projection
pullbacks survive postcomposition through their categorical preservation
properties. The construction applies to all natural transformations.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)

universe u v u' v'

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable {D' : Type u'} [Category.{v'} D'] [CartesianMonoidalCategory D']
variable {S : Signature} {R : List (LocalRule S)}
variable {M' : List (MetaArity S)} {equations : List (EqAxiom S M')}
variable (H : D ⥤ D') [PreservesFiniteProducts H] [PreservesLimitsOfShape WalkingCospan H]
variable [ExponentialPreservation H]

namespace StructuredFunctor

/-- Postcomposition preserves the independently specified structure. -/
def postcompose (F : StructuredFunctor R equations (D := D)) :
    StructuredFunctor R equations (D := D') where
  carrier := F.carrier ⋙ H
  program := F.program.postcompose H
  pullback f j := (F.pullback f j).map H

@[simp] theorem postcompose_carrier (F : StructuredFunctor R equations (D := D)) :
    (F.postcompose H).carrier = F.carrier ⋙ H := rfl

/-- Recovery of the program model uses the actual mapped function objects. -/
theorem postcompose_programModel (F : StructuredFunctor R equations (D := D)) :
    (F.postcompose H).programModel = mapModel H F.programModel := rfl

omit [PreservesLimitsOfShape WalkingCospan H] in
/-- Mapping a recovered family product commutes with each projection. -/
theorem postcompose_famIso_projection (F : StructuredFunctor R equations (D := D))
    (L : List (MetaArity S)) (i : Fin L.length) :
    ((F.program.postcompose H).famIso L).hom ≫ (mapModel H F.programModel).familyProj L i =
      H.map ((F.program.famIso L).hom ≫ F.programModel.familyProj L i) := by
  rw [← familyComparison_proj H F.programModel L i, ← Category.assoc]
  have fam : ((F.program.postcompose H).famIso L).hom ≫
      (familyComparison H F.programModel.power L).hom = H.map ((F.program.famIso L).hom) :=
    F.program.toPreservingData.postcompose_famIso H L
  exact (congrArg (· ≫ H.map (F.programModel.familyProj L i)) fam).trans (H.map_comp _ _).symm

/-- The source endpoint is the image of the original source endpoint. -/
theorem postcompose_source (F : StructuredFunctor R equations (D := D))
    (Γ : Ctx S) (s : S.Srt) :
    (F.postcompose H).eventModel.objects.source Γ s = H.map (F.eventModel.objects.source Γ s) := by
  have comparison := F.postcompose_famIso_projection H [(Γ, s), (Γ, s)] ⟨0, by simp⟩
  exact (congrArg (H.map (F.carrier.map (toProgram R equations
    (eventObject R equations Γ s))) ≫ ·) comparison).trans
      (H.map_comp _ _).symm

/-- The target endpoint is the image of the original target endpoint. -/
theorem postcompose_target (F : StructuredFunctor R equations (D := D))
    (Γ : Ctx S) (s : S.Srt) :
    (F.postcompose H).eventModel.objects.target Γ s = H.map (F.eventModel.objects.target Γ s) := by
  have comparison := F.postcompose_famIso_projection H [(Γ, s), (Γ, s)] ⟨1, by simp⟩
  exact (congrArg (H.map (F.carrier.map (toProgram R equations
    (eventObject R equations Γ s))) ≫ ·) comparison).trans
      (H.map_comp _ _).symm

end StructuredFunctor

/-- Qualified change of target on structured classifier interpretations. -/
def postcomposeStructured :
    StructuredFunctor R equations (D := D) ⥤ StructuredFunctor R equations (D := D') where
  obj F := F.postcompose H
  map α := Functor.whiskerRight α H
  map_id F := by
    apply NatTrans.ext
    funext a
    exact H.map_id _
  map_comp α β := by
    apply NatTrans.ext
    funext a
    exact H.map_comp _ _

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels
