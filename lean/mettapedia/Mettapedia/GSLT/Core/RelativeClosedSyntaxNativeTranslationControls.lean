import Mettapedia.CategoryTheory.RelativeClosedSyntaxTranslationNativeExtension
import Mettapedia.GSLT.Core.RelativeClosedSyntaxTranslationBaseControls

/-!
# Complete data readouts of an actual coded weak native augmentation

The independently authored Boolean-order weak base map moves the false
scope to an inhabited scope. The generated coded augmentation preserves the
independent fresh Boolean data and actual negation arrow. Its full semantic
arrow is compared before reading either supplied value; replacing its
complete output by a constant is rejected.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedSyntaxNativeTranslationControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.SemilatticeInf
open scoped Mettapedia.CategoryTheory.PredicateDoctrine.HeytingClosed
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open GeneratedCategory Interpretation
open RelativeClosedWeakBaseControls RelativeClosedSyntaxTranslationBaseControls

private instance translated_base_lex : PreservesFiniteLimits translation.data.base := by
  change PreservesFiniteLimits weakBase
  infer_instance

private instance translated_base_closed : MonoidalClosedFunctor translation.data.base := by
  change MonoidalClosedFunctor weakBase
  infer_instance

def coded := Translation.NativeExtension.extended translation

def diagram : Object augmented ⥤ Type := coded.functor ⋙ completeInterpretation

theorem complete_base : baseFunctor augmented ⋙ diagram = weakBase ⋙ truthFunctor :=
  (congrArg (fun following : Bool ⥤ Object augmented => following ⋙ completeInterpretation)
    (Translation.NativeExtension.base_readback translation)).trans
      (congrArg (fun following : Bool ⥤ Type => weakBase ⋙ following) complete_weak_base)

theorem false_scope_inhabited : Nonempty (diagram.obj (baseObject augmented false)) := by
  have same : diagram.obj (baseObject augmented false) = truthFunctor.obj true :=
    congrArg (fun following : Bool ⥤ Type => following.obj false) complete_base
  exact ⟨same.symm ▸ trueValue⟩

theorem omitted_weak_base_rejected :
    diagram.obj (baseObject augmented false) ≠ completeInterpretation.obj (baseObject augmented false) := by
  intro same
  obtain ⟨value⟩ := false_scope_inhabited
  exact old_false_scope_remains_empty.false (same ▸ value)

theorem complete_old_diagram : (BaseExtension.originalMap signature).functor ⋙ diagram =
    translation.functor ⋙ Interpretation.functor meanings realized :=
  (congrArg (fun following : Object signature ⥤ Object augmented => following ⋙ completeInterpretation)
    (Translation.NativeExtension.original_readback translation)).trans
      (congrArg (fun following : Object signature ⥤ Type => translation.functor ⋙ following)
        complete_original_diagram)

theorem independent_data_retained : diagram.obj dataObject = ULift.{0} Bool :=
  objectValue_unique extended extended_realized (coded.object dataObject) (ULift Bool) rfl

theorem complete_negation_retained :
    (⟨diagram.obj dataObject, diagram.obj dataObject, diagram.map (classOf originalNegation)⟩ : ArrowValue Type) =
      ⟨ULift.{0} Bool, ULift.{0} Bool, negate⟩ :=
  Option.some.inj
    ((functor_complete_readout extended extended_realized (coded.rawArrow originalNegation)).symm.trans rfl)

private theorem reindex_loop {source target : Type} (first : source ⟶ source) (second : target ⟶ target)
    (same : source = target)
    (complete : (⟨source, source, first⟩ : ArrowValue Type) = ⟨target, target, second⟩) :
    eqToHom same.symm ≫ first ≫ eqToHom same = second := by
  cases same
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using ArrowValue.arrow_injective complete

def retainedNegation : ULift.{0} Bool ⟶ ULift.{0} Bool :=
  eqToHom independent_data_retained.symm ≫ diagram.map (classOf originalNegation) ≫
    eqToHom independent_data_retained

theorem retainedNegation_complete : retainedNegation = negate :=
  reindex_loop (diagram.map (classOf originalNegation)) negate independent_data_retained complete_negation_retained

theorem supplied_values_retained :
    (retainedNegation (ULift.up false)).down = true ∧
      (retainedNegation (ULift.up true)).down = false := by
  rw [retainedNegation_complete]
  exact ⟨rfl, rfl⟩

theorem constant_output_rejected :
    retainedNegation (ULift.up false) ≠ retainedNegation (ULift.up true) := by
  intro same
  have read := congrArg ULift.down same
  rw [supplied_values_retained.1, supplied_values_retained.2] at read
  exact Bool.false_ne_true read.symm

end Mettapedia.GSLT.Core.RelativeClosedSyntaxNativeTranslationControls
