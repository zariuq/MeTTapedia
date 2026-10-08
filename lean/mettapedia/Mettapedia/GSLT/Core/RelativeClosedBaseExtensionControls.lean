import Mettapedia.CategoryTheory.RelativeClosedSyntaxBaseExtensionInterpretation
import Mettapedia.GSLT.Core.RelativeClosedInterpretationControls

/-!
# Retained declarations after actual base augmentation

The arbitrary presentation is extended by the base comparison diagrams.
Its original identity and negation declarations remain distinct quotient
arrows: an independently realized native model still separates their full
values. The whole old interpretation and a two-valued function survive the
actual inclusion. Original and comparison origins are also kept separately.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedBaseExtensionControls

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open Mettapedia.CategoryTheory.RelativeClosedSyntax.GeneratedCategory
open Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation
open AuthoredClosedTheoryControls RelativeClosedInterpretationControls

def extendedSignature := BaseExtension.extend syntaxSignature

def inclusion : SignatureMap syntaxSignature extendedSignature :=
  BaseExtension.originalMap syntaxSignature

def nativeAssignment := BaseExtension.NativeExtension.assignment separatingAssignment

theorem nativeRealization : Realization extendedSignature nativeAssignment :=
  BaseExtension.NativeExtension.realization separatingAssignment rfl separatingRealization

def extendedDataObject : Object extendedSignature := inclusion.functor.obj Generated.dataObject

def extendedNamedArrow (name : Bool) : RawHom extendedDataObject extendedDataObject :=
  inclusion.rawArrow (namedArrow name)

def extendedArrow (name : Bool) : extendedDataObject ⟶ extendedDataObject :=
  classOf (extendedNamedArrow name)

theorem extended_name_image (name : Bool) :
    (functor nativeAssignment nativeRealization).map (extendedArrow name) =
      if name then negate else 𝟙 Bool :=
  rawArrowValue_unique nativeAssignment nativeRealization (extendedNamedArrow name) _
    ((BaseExtension.NativeExtension.original_arrow_read separatingAssignment syntaxSignature rfl
      (.name name)).trans rfl)

theorem supplied_values_remain_distinct :
    (functor nativeAssignment nativeRealization).map (extendedArrow true) false = true ∧
      (functor nativeAssignment nativeRealization).map (extendedArrow true) true = false := by
  rw [extended_name_image]
  exact ⟨rfl, rfl⟩

theorem augmentation_retains_distinct_quotient_arrows :
    extendedArrow false ≠ extendedArrow true := by
  intro same
  have images := congrArg (functor nativeAssignment nativeRealization).map same
  rw [extended_name_image, extended_name_image] at images
  have impossible : false = true := congrArg (fun arrow : Bool ⟶ Bool => arrow false) images
  exact Bool.false_ne_true impossible

theorem whole_original_interpretation_recovered :
    inclusion.functor ⋙ functor nativeAssignment nativeRealization =
      functor separatingAssignment separatingRealization :=
  BaseExtension.NativeExtension.original_diagram_readback separatingAssignment rfl separatingRealization

theorem original_nonidentity_base_map_recovered :
    (functor nativeAssignment nativeRealization).map
      (baseArrow (signature := extendedSignature) negate) = negate :=
  functor_base_arrow nativeAssignment nativeRealization negate

theorem independently_named_origins_differ :
    BaseExtension.originalArrows (C := Type) (symbols := syntaxSymbols) true ≠
      BaseExtension.comparisonArrows (C := Type) (symbols := syntaxSymbols)
        (.product Bool Bool) := by
  intro same
  cases same

def extendedFunction :
    RawHom extendedDataObject (inclusion.functor.obj
      (exponentialObject Generated.dataObject Generated.dataObject)) :=
  inclusion.rawArrow authoredFunction

theorem whole_function_readout :
    rawArrowValue nativeAssignment nativeRealization extendedFunction =
      abstraction (CartesianMonoidalCategory.snd Bool Bool) :=
  rawArrowValue_unique nativeAssignment nativeRealization extendedFunction _
    ((BaseExtension.NativeExtension.original_arrow_read separatingAssignment syntaxSignature rfl
      annotatedAbstraction).trans
        (separatingAssignment.evaluate_abstraction (CartesianMonoidalCategory.snd Bool Bool)
          rfl rfl rfl (separatingAssignment.evaluate_second rfl rfl)))

def retainedFunction (environment : Bool) : Bool ⟶ Bool :=
  rawArrowValue nativeAssignment nativeRealization extendedFunction environment

theorem function_retains_both_supplied_arguments :
    retainedFunction false false = false ∧ retainedFunction false true = true := by
  unfold retainedFunction
  rw [whole_function_readout]
  exact ⟨rfl, rfl⟩

theorem constant_argument_erasure_rejected :
    retainedFunction false false ≠ retainedFunction false true := by
  rw [function_retains_both_supplied_arguments.1, function_retains_both_supplied_arguments.2]
  exact Bool.false_ne_true

end Mettapedia.GSLT.Core.RelativeClosedBaseExtensionControls
