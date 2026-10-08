import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorReconstructionValues

/-!
# Annotated abstraction and authored equalizer reconstruction

The complete body is transported through the actual product comparison before
the independent evaluator constructs its abstraction. Authored equalizer lifts
retain their defining pair of arrows, candidate, and commutativity tree. The
mapped guard is derived from the genuine source equation and functoriality.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.FunctorNormalization

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open GeneratedCategory Interpretation

universe k w

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (mapping : Object signature ⥤ D) [PreservesFiniteLimits mapping]
variable [MonoidalClosedFunctor mapping] (headers : HeaderFormation signature)

theorem arrow_read_evaluation (argument result : Object signature)
    (argumentRead : ObjectRead mapping headers argument) (resultRead : ObjectRead mapping headers result) :
    ArrowRead mapping headers
      (⟨.evaluation argument.code result.code, ⟨.evaluation argument.formed.some result.formed.some⟩⟩ :
        RawHom (product (exponentialObject argument result) argument) result) := by
  apply arrow_read_transport mapping headers _ _
    ((normalized_product_object mapping (exponentialObject argument result) argument).trans
      (congrArg (fun value : D => value ⊗ (normalizedFunctor mapping).obj argument)
        (normalized_exponential_object mapping argument result))).symm rfl
    ((assignment mapping headers).evaluate_evaluation argumentRead resultRead)
  simpa only [GeneratedCategory.evaluation, eqToHom_refl, Category.comp_id] using
    normalized_evaluation mapping argument result

theorem arrow_read_abstraction (context argument result : Object signature)
    (body : RawHom (product context argument) result)
    (contextRead : ObjectRead mapping headers context) (argumentRead : ObjectRead mapping headers argument)
    (resultRead : ObjectRead mapping headers result) (bodyRead : ArrowRead mapping headers body) :
    ArrowRead mapping headers
      (⟨.curry context.code argument.code result.code body.code,
        ⟨.curry context.formed.some argument.formed.some result.formed.some body.admitted.some⟩⟩ :
          RawHom context (exponentialObject argument result)) := by
  have bodyNative := bodyRead.trans (congrArg some
    (ArrowValue.cast_source ((normalizedFunctor mapping).map (classOf body))
      (normalized_product_object mapping context argument)))
  apply arrow_read_transport mapping headers _ _ rfl
    (normalized_exponential_object mapping argument result).symm
    ((assignment mapping headers).evaluate_abstraction _ contextRead argumentRead resultRead bodyNative)
  have represented : GeneratedCategory.abstraction (classOf body) = classOf
      (⟨.curry context.code argument.code result.code body.code,
        ⟨.curry context.formed.some argument.formed.some result.formed.some body.admitted.some⟩⟩ :
          RawHom context (exponentialObject argument result)) := rfl
  simpa only [eqToHom_refl, Category.id_comp] using
    (congrArg (normalizedFunctor mapping).map represented.symm).trans
      (normalized_abstraction mapping (classOf body))

theorem arrow_read_equalizer_inclusion {source target : Object signature}
    (first second : RawHom source target)
    (sourceRead : ObjectRead mapping headers source) (targetRead : ObjectRead mapping headers target)
    (firstRead : ArrowRead mapping headers first) (secondRead : ArrowRead mapping headers second) :
    ArrowRead mapping headers
      (⟨.equalizerArrow source.code target.code first.code second.code,
        ⟨.equalizerArrow source.formed.some target.formed.some first.admitted.some second.admitted.some⟩⟩ :
          RawHom (PresentedEqualizer.object first second) source) := by
  apply arrow_read_transport mapping headers _ _ (normalized_equalizer_object mapping first second).symm rfl
    ((assignment mapping headers).evaluate_equalizer_arrow _ _ sourceRead targetRead firstRead secondRead)
  simpa only [PresentedEqualizer.inclusion, eqToHom_refl, Category.comp_id] using
    normalized_equalizer_inclusion mapping first second

theorem arrow_read_authoredLift {source target context : Object signature}
    (first second : RawHom source target) (candidate : RawHom context source)
    (commutes : Derivation signature (.equation context.code target.code
      (.compose candidate.code first.code) (.compose candidate.code second.code)))
    (sourceRead : ObjectRead mapping headers source) (targetRead : ObjectRead mapping headers target)
    (contextRead : ObjectRead mapping headers context)
    (firstRead : ArrowRead mapping headers first) (secondRead : ArrowRead mapping headers second)
    (candidateRead : ArrowRead mapping headers candidate) :
    ArrowRead mapping headers (authoredLift first second candidate commutes) := by
  have mapped := mapped_condition mapping first second (classOf candidate) (Quotient.sound ⟨commutes⟩)
  apply arrow_read_transport mapping headers _ _ rfl (normalized_equalizer_object mapping first second).symm
    ((assignment mapping headers).evaluate_equalizer_lift _ _ _ mapped
      sourceRead targetRead contextRead firstRead secondRead candidateRead)
  simpa only [eqToHom_refl, Category.id_comp] using
    normalized_authoredLift mapping first second candidate commutes

end Mettapedia.CategoryTheory.RelativeClosedSyntax.FunctorNormalization
