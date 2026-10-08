import Mettapedia.CategoryTheory.RelativeClosedSyntaxArrowExtension
import Mettapedia.CategoryTheory.RelativeClosedSyntaxSignatureMapInterpretation

/-!
# Exact admission and whole restriction of new primitive arrows

The new target operators are supplied independently as complete arrow
values. The original evaluator is recovered on every raw expression,
including unsuccessful reads. The extended declarations are realized
exactly when the original declarations are realized and the independently
supplied new endpoints match their authored domains and codomains.
Restriction recovers the whole original quotient interpretation functor.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.ArrowExtension

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open GeneratedCategory Interpretation

universe k w z

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable (signature : Signature (C := C) (symbols := symbols))
variable {Index : Type k} (declarations : Index → Declaration signature)
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]

def extendAssignment (meanings : Assignment C symbols D) (added : Index → ArrowValue D) :
    Assignment C (extendedSymbols symbols Index) D where
  base := meanings.base
  object := meanings.object
  arrow
    | .inl origin => meanings.arrow origin
    | .inr origin => added origin

omit [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D] in
theorem restricted_assignment (meanings : Assignment C symbols D) (added : Index → ArrowValue D) :
    (inclusion signature declarations).precompose (extendAssignment meanings added) = meanings := by
  cases meanings
  rfl

include signature declarations in
theorem evaluate_object_original (meanings : Assignment C symbols D) (added : Index → ArrowValue D)
    (code : ObjectCode C symbols) :
    (extendAssignment meanings added).evaluateObject (originalObject code) =
      meanings.evaluateObject code :=
  ((inclusion signature declarations).evaluateObject_precompose (extendAssignment meanings added) code).trans
    (congrArg (fun value : Assignment C symbols D => value.evaluateObject code)
      (restricted_assignment signature declarations meanings added))

include signature declarations in
theorem evaluate_arrow_original (meanings : Assignment C symbols D) (added : Index → ArrowValue D)
    (code : ArrowCode C symbols) :
    (extendAssignment meanings added).evaluateArrow (originalArrow code) =
      meanings.evaluateArrow code :=
  ((inclusion signature declarations).evaluateArrow_precompose (extendAssignment meanings added) code).trans
    (congrArg (fun value : Assignment C symbols D => value.evaluateArrow code)
      (restricted_assignment signature declarations meanings added))

structure AddedAdmission (meanings : Assignment C symbols D) (added : Index → ArrowValue D) : Prop where
  source (origin : Index) : meanings.evaluateObject (declarations origin).source.code = some (added origin).source
  target (origin : Index) : meanings.evaluateObject (declarations origin).target.code = some (added origin).target

theorem extended_realization (meanings : Assignment C symbols D) (added : Index → ArrowValue D)
    (realized : Realization signature meanings) (admitted : AddedAdmission signature declarations meanings added) :
    Realization (extend signature declarations) (extendAssignment meanings added) where
  source origin := by
    cases origin with
    | inl origin => exact (evaluate_object_original signature declarations meanings added _).trans (realized.source origin)
    | inr origin => exact (evaluate_object_original signature declarations meanings added _).trans (admitted.source origin)
  target origin := by
    cases origin with
    | inl origin => exact (evaluate_object_original signature declarations meanings added _).trans (realized.target origin)
    | inr origin => exact (evaluate_object_original signature declarations meanings added _).trans (admitted.target origin)
  equation origin := by
    obtain ⟨value, source, target, first, second⟩ := realized.equation origin
    exact ⟨value,
      (evaluate_object_original signature declarations meanings added _).trans source,
      (evaluate_object_original signature declarations meanings added _).trans target,
      (evaluate_arrow_original signature declarations meanings added _).trans first,
      (evaluate_arrow_original signature declarations meanings added _).trans second⟩

theorem necessary_original (meanings : Assignment C symbols D) (added : Index → ArrowValue D)
    (extended : Realization (extend signature declarations) (extendAssignment meanings added)) :
    Realization signature meanings := by
  have restricted := (inclusion signature declarations).realization_precompose (extendAssignment meanings added) extended
  simpa only [restricted_assignment] using restricted

theorem necessary_admission (meanings : Assignment C symbols D) (added : Index → ArrowValue D)
    (extended : Realization (extend signature declarations) (extendAssignment meanings added)) :
    AddedAdmission signature declarations meanings added where
  source origin := (evaluate_object_original signature declarations meanings added _).symm.trans
    (extended.source (Sum.inr origin))
  target origin := (evaluate_object_original signature declarations meanings added _).symm.trans
    (extended.target (Sum.inr origin))

theorem realization_iff (meanings : Assignment C symbols D) (added : Index → ArrowValue D) :
    Realization (extend signature declarations) (extendAssignment meanings added) ↔
      Realization signature meanings ∧ AddedAdmission signature declarations meanings added :=
  ⟨fun extended => ⟨necessary_original signature declarations meanings added extended,
    necessary_admission signature declarations meanings added extended⟩,
    fun admitted => extended_realization signature declarations meanings added admitted.1 admitted.2⟩

theorem complete_restriction (meanings : Assignment C symbols D) (added : Index → ArrowValue D)
    (realized : Realization signature meanings) (admitted : AddedAdmission signature declarations meanings added) :
    (inclusion signature declarations).functor ⋙
        Interpretation.functor (extendAssignment meanings added)
          (extended_realization signature declarations meanings added realized admitted) =
      Interpretation.functor meanings realized := by
  have result := (inclusion signature declarations).functor_precompose (extendAssignment meanings added)
    (extended_realization signature declarations meanings added realized admitted)
  simpa only [restricted_assignment] using result

theorem generator_complete_read (meanings : Assignment C symbols D) (added : Index → ArrowValue D)
    (realized : Realization signature meanings) (admitted : AddedAdmission signature declarations meanings added)
    (origin : Index) :
    (⟨(Interpretation.functor (extendAssignment meanings added)
        (extended_realization signature declarations meanings added realized admitted)).obj
          ((inclusion signature declarations).object (declarations origin).source),
      (Interpretation.functor (extendAssignment meanings added)
        (extended_realization signature declarations meanings added realized admitted)).obj
          ((inclusion signature declarations).object (declarations origin).target),
      (Interpretation.functor (extendAssignment meanings added)
        (extended_realization signature declarations meanings added realized admitted)).map
          (classOf (generator signature declarations origin))⟩ : ArrowValue D) = added origin := by
  have read := functor_complete_readout (extendAssignment meanings added)
    (extended_realization signature declarations meanings added realized admitted) (generator signature declarations origin)
  exact Option.some.inj read.symm

end Mettapedia.CategoryTheory.RelativeClosedSyntax.ArrowExtension
