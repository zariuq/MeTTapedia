import Mettapedia.OSLF.Syntax.BindingClosedGeneratedModel
import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorNormalizationCells

/-!
# Complete canonical schema readings for recovered binding models

The primitive sort component of the reconstructed parser comparison is its
actual equality transport. Composite schema domains retain their genuinely
constructed comparison. Conjugating a mapped schema arrow by these complete
comparisons recovers the independently recursive binding-family reading.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Binding.ClosedPresentation.GeneratedModel

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open Mettapedia.CategoryTheory.RelativeClosedSyntax GeneratedCategory Interpretation

universe k w

variable {binding : Mettapedia.OSLF.Binding.Signature}
variable {D : Type w} [Category.{k} D] [CartesianMonoidalCategory D]
variable [MonoidalClosed D] [HasFiniteLimits D]
variable (mapping : Object (signature.{k} binding) ⥤ D)
variable [PreservesFiniteLimits mapping] [MonoidalClosedFunctor mapping]

theorem comparison_sort (result : binding.Srt) :
    (comparison mapping).hom.app (sortObject binding result) =
      eqToHom ((operations mapping).sort_object_readout result).symm := by
  unfold comparison
  rw [Iso.trans_hom, NatTrans.comp_app]
  erw [FunctorNormalization.parserComparison_hom_name]
  simp only [eqToIso.hom, eqToHom_app, eqToHom_trans]

def sortComparison (result : binding.Srt) :
    mapping.obj (sortObject binding result) ≅ (operations mapping).sort result :=
  (comparison mapping).app (sortObject binding result) ≪≫
    eqToIso ((operations mapping).sort_object_readout result)

theorem sortComparison_hom (result : binding.Srt) :
    (sortComparison mapping result).hom = 𝟙 ((operations mapping).sort result) := by
  rw [sortComparison, Iso.trans_hom, Iso.app_hom]
  erw [comparison_sort]
  simp only [eqToIso.hom, eqToHom_refl]
  erw [Category.id_comp]
  rfl

theorem schema_object_readout {metavariables : List (MetaArity binding)} (context : Ctx binding) :
    (operations mapping).interpretation.functor.obj (SchemaExpressions.genericStage binding metavariables context) =
      (operations mapping).context context ⊗ (operations mapping).family metavariables :=
  objectValue_unique (operations mapping).assignment (operations mapping).realization _ _
    ((operations mapping).assignment.evaluate_product ((operations mapping).context_read context)
      ((operations mapping).family_read metavariables))

def schemaComparison (metavariables : List (MetaArity binding)) (context : Ctx binding) :
    mapping.obj (SchemaExpressions.genericStage binding metavariables context) ≅
      (operations mapping).context context ⊗ (operations mapping).family metavariables :=
  (comparison mapping).app (SchemaExpressions.genericStage binding metavariables context) ≪≫
    eqToIso (schema_object_readout mapping context)

omit [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D] in
private theorem normalized_arrow {source target nextSource nextTarget : D}
    (before : source ⟶ target) (after : nextSource ⟶ nextTarget)
    (sourceSame : source = nextSource) (targetSame : target = nextTarget)
    (complete : (⟨source,target,before⟩ : ArrowValue D) = ⟨nextSource,nextTarget,after⟩) :
    eqToHom sourceSame.symm ≫ before ≫ eqToHom targetSame = after := by
  cases sourceSame
  cases targetSame
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using
    ArrowValue.arrow_injective complete

theorem complete_schema_arrow {metavariables : List (MetaArity binding)} {context : Ctx binding}
    {result : binding.Srt} (term : Term (withMetas binding metavariables) context result) :
    (schemaComparison mapping metavariables context).inv ≫
        mapping.map (classOf (SchemaExpressions.expression binding term)) ≫
          (sortComparison mapping result).hom =
      (operations mapping).model.generic metavariables term := by
  have natural := NatIso.naturality_1 (comparison mapping)
    (classOf (SchemaExpressions.expression binding term))
  have read := normalized_arrow _ _ (schema_object_readout mapping context)
    ((operations mapping).sort_object_readout result) ((operations mapping).schema_complete_readout term)
  have whole := congrArg (fun arrow => eqToHom (schema_object_readout mapping context).symm ≫
    arrow ≫ eqToHom ((operations mapping).sort_object_readout result)) natural
  simpa only [schemaComparison, sortComparison, Iso.trans_inv, Iso.trans_hom,
    Iso.app_hom, Iso.app_inv, eqToIso.hom, eqToIso.inv, Category.assoc] using whole.trans read

end Mettapedia.OSLF.Binding.ClosedPresentation.GeneratedModel
