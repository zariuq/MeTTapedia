import Mettapedia.CategoryTheory.RelativeClosedSyntaxTranslationInterpretation
import Mettapedia.CategoryTheory.RelativeClosedSyntaxTranslationClosed
import Mettapedia.CategoryTheory.RelativeClosedSyntaxClosedModels

/-!
# Model restriction along complete expression translations

An independently realized target model restricts along the actual generated
translation. The new primitive meanings are evaluated from the supplied
complete target expressions, and local declaration realization is earned.
Complete model cells restrict by actual precomposition and the independently
proved evaluator comparison. The comparison is natural on these whole cells.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.Translation

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open GeneratedCategory Interpretation SemanticModels

universe k w

variable {C D : Type k} [Category.{k} C] [Category.{k} D]
variable {symbols nextSymbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {next : Signature (C := D) (symbols := nextSymbols)}
variable {E : Type w} [Category.{k} E]
variable [CartesianMonoidalCategory E] [MonoidalClosed E] [HasFiniteLimits E]
variable (mapping : Translation signature next)

def precomposeModel (model : Model next E) : Model signature E :=
  ⟨mapping.precompose model.meanings model.realization,
    mapping.realization_precompose model.meanings model.realization⟩

def precomposeComparison (model : Model next E) :
    mapping.functor ⋙ model.diagram ≅ (mapping.precomposeModel model).diagram :=
  eqToIso (mapping.functor_precompose model.meanings model.realization)

def precomposeModels : Model next E ⥤ Model signature E where
  obj := mapping.precomposeModel
  map {first last} input :=
    show (mapping.precomposeModel first).diagram ⟶ (mapping.precomposeModel last).diagram from
      (mapping.precomposeComparison first).inv ≫
        Functor.whiskerLeft mapping.functor input ≫ (mapping.precomposeComparison last).hom
  map_id model := by
    change (mapping.precomposeComparison model).inv ≫
      Functor.whiskerLeft mapping.functor (𝟙 model.diagram) ≫
        (mapping.precomposeComparison model).hom = 𝟙 _
    simp only [Functor.whiskerLeft_id', Category.id_comp, Iso.inv_hom_id]
  map_comp {first middle last} before after := by
    change (mapping.precomposeComparison first).inv ≫
        Functor.whiskerLeft mapping.functor (before ≫ after) ≫
          (mapping.precomposeComparison last).hom =
      ((mapping.precomposeComparison first).inv ≫
        Functor.whiskerLeft mapping.functor before ≫ (mapping.precomposeComparison middle).hom) ≫
      ((mapping.precomposeComparison middle).inv ≫
        Functor.whiskerLeft mapping.functor after ≫ (mapping.precomposeComparison last).hom)
    simp only [Functor.whiskerLeft_comp, Category.assoc, Iso.hom_inv_id_assoc]

def precomposeDiagrams : ClosedModels.Diagram next E ⥤ ClosedModels.Diagram signature E where
  obj model :=
    ⟨mapping.functor ⋙ model.functor, comp_preservesFiniteLimits mapping.functor model.functor,
      CartesianClosedFunctorCoherence.closed_composition mapping.functor model.functor⟩
  map input := Functor.whiskerLeft mapping.functor input
  map_id _model := Functor.whiskerLeft_id' mapping.functor
  map_comp before after := Functor.whiskerLeft_comp mapping.functor before after

def precomposeInterpretation :
    ClosedModels.interpretation (signature := next) (D := E) ⋙ mapping.precomposeDiagrams ≅
      mapping.precomposeModels ⋙ ClosedModels.interpretation (signature := signature) (D := E) :=
  NatIso.ofComponents
    (fun model => ClosedModels.isoOfFunctor (mapping.precomposeComparison model)) (by
      intro first last input
      change Functor.whiskerLeft mapping.functor input ≫
          (mapping.precomposeComparison last).hom =
        (mapping.precomposeComparison first).hom ≫
          ((mapping.precomposeComparison first).inv ≫
            Functor.whiskerLeft mapping.functor input ≫ (mapping.precomposeComparison last).hom)
      simp only [Iso.hom_inv_id_assoc])

theorem complete_precompose_readout (model : Model next E)
    {source target : Object signature} (input : RawHom source target) :
    (mapping.precomposeModel model).meanings.evaluateArrow input.code =
      some ⟨model.diagram.obj (mapping.object source), model.diagram.obj (mapping.object target),
        model.diagram.map (mapping.functor.map (classOf input))⟩ :=
  (mapping.evaluateArrow_precompose model.meanings model.realization input.code).symm.trans
    (functor_complete_readout model.meanings model.realization (mapping.rawArrow input))

theorem complete_cell_readout {first last : Model next E} (input : first ⟶ last)
    (context : Object signature) :
    ((mapping.precomposeModels).map input).app context =
      (mapping.precomposeComparison first).inv.app context ≫
        input.app (mapping.object context) ≫ (mapping.precomposeComparison last).hom.app context := rfl

end Mettapedia.CategoryTheory.RelativeClosedSyntax.Translation
