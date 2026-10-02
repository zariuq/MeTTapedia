import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedTargetTransport
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedTargetProgramMaps
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedTargetBinding

/-!
# The program part of operational target transport

Transport of an operational model retains the actual image of its program
interpretation, on objects and on every map. Forgetting events therefore
commutes with the existing binding target-change functor.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.CategoricalBindingQuotientEquivalence
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial

universe u v u' v'

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D] [HasPullbacks D]
variable {D' : Type u'} [Category.{v'} D'] [CartesianMonoidalCategory D']
variable {S : Signature} {R : List (LocalRule S)}
variable {schema : List (MetaArity S)} {equations : List (EqAxiom S schema)}
variable (H : D ⥤ D') [PreservesFiniteProducts H] [ExponentialPreservation H]
variable [PreservesLimitsOfShape WalkingCospan H]

/-- Each program map of a transported operational model is the actual
image of the original program map. -/
theorem transportModels_map_program {M N : CategoricalModel R equations (D := D)}
    (f : M ⟶ N) :
    ((transportModels H).map f).program =
      (mapSatisfyingInterpretations H (authoredEquationPresentation S equations)).map f.program := by
  change (M.targetModelIso H).hom.program ≫
    (StructuredFunctor.modelHom (F := M.structured.postcompose H) (G := N.structured.postcompose H)
      (Functor.whiskerRight (CategoricalModel.classifyingMap f) H)).program ≫
      (N.targetModelIso H).inv.program = _
  let B := mapSatisfyingInterpretations H (authoredEquationPresentation S equations)
  have start := M.targetModelIso_hom_program H
  have finish := N.targetModelIso_inv_program H
  have moved :
      (StructuredFunctor.modelHom (F := M.structured.postcompose H) (G := N.structured.postcompose H)
        (Functor.whiskerRight (CategoricalModel.classifyingMap f) H)).program =
        B.map (StructuredFunctor.modelHom (F := M.structured) (G := N.structured)
          (CategoricalModel.classifyingMap f)).program :=
    StructuredFunctor.programHom_postcompose H (F := M.structured) (G := N.structured)
      (CategoricalModel.classifyingMap f)
  have original : M.programUnit ≫
      (StructuredFunctor.modelHom (F := M.structured) (G := N.structured)
        (CategoricalModel.classifyingMap f)).program ≫ N.programUnitInv = f.program :=
    ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ N.programUnitInv) (CategoricalModel.programUnit_naturality f).symm)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (f.program ≫ ·) N.programUnit_inv).trans (Category.comp_id _)))
  have mapped : B.map M.programUnit ≫
      B.map (StructuredFunctor.modelHom (F := M.structured) (G := N.structured)
        (CategoricalModel.classifyingMap f)).program ≫ B.map N.programUnitInv = B.map f.program :=
    ((congrArg (B.map M.programUnit ≫ ·) (B.map_comp _ _).symm).trans
      (B.map_comp _ _).symm).trans (congrArg B.map original)
  exact (congrArg (fun k => k ≫ _ ≫ _) start).trans
    ((congrArg (fun k => (M.imageProgramIso H).hom ≫ _ ≫ k) finish).trans
      ((congrArg (fun k => (M.imageProgramIso H).hom ≫ k ≫ (N.imageProgramIso H).inv)
        moved).trans mapped))

/-- Forgetting events commutes with target change on the actual program
objects and all interpretation maps. -/
def transportForgetProgramsIso :
    transportModels (R := R) (equations := equations) H ⋙ forgetPrograms ≅
      forgetPrograms ⋙ mapSatisfyingInterpretations H (authoredEquationPresentation S equations) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {M N} f => by
    change ((transportModels H).map f).program ≫ 𝟙 _ =
      𝟙 _ ≫ (mapSatisfyingInterpretations H (authoredEquationPresentation S equations)).map f.program
    rw [Category.comp_id, Category.id_comp]
    exact transportModels_map_program H f)

variable [HasPullbacks D']

/-- The target-classification comparison restricts to the existing program
classification and the actual postcomposition of equation contexts. -/
def targetBindingClassificationIso :
    transportModels (R := R) (equations := equations) H ⋙ classifyFunctor ⋙ restrictionToPrograms ≅
      classifyFunctor ⋙ restrictionToPrograms ⋙
        postcomposeQuotientFunctors H (authoredEquationPresentation S equations) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (targetClassificationIso H) restrictionToPrograms ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft classifyFunctor (postcomposeRestrictionIso H)

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels
