import Mettapedia.CategoryTheory.RelativeClosedSyntaxEquationExtension
import Mettapedia.CategoryTheory.RelativeClosedSyntaxSignatureMapInterpretation

/-!
# Exact semantic admission of independently authored equations

Adding equation declarations does not add target primitive meanings. A
supplied interpretation extends exactly when its complete arrow values
satisfy each authored parallel pair. The two structural evaluators agree
on every old expression, including their rejected reads. Restriction
recovers the entire original interpretation functor.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.EquationExtension

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open GeneratedCategory Interpretation

universe k w z

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable (signature : Signature (C := C) (symbols := symbols))
variable {Index : Type k} (declarations : Index → Declaration signature)
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]

def extendAssignment (meanings : Assignment C symbols D) :
    Assignment C (extendedSymbols symbols Index) D where
  base := meanings.base
  object := meanings.object
  arrow := meanings.arrow

omit [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D] in
theorem restricted_assignment (meanings : Assignment C symbols D) :
    (inclusion signature declarations).precompose (extendAssignment (Index := Index) meanings) =
      meanings := by
  cases meanings
  rfl

include signature declarations in
theorem evaluate_object_original (meanings : Assignment C symbols D) (code : ObjectCode C symbols) :
    (extendAssignment (Index := Index) meanings).evaluateObject (originalObject code) =
      meanings.evaluateObject code :=
  ((inclusion signature declarations).evaluateObject_precompose (extendAssignment meanings) code).trans
    (congrArg (fun value : Assignment C symbols D => value.evaluateObject code)
      (restricted_assignment signature declarations meanings))

include signature declarations in
theorem evaluate_arrow_original (meanings : Assignment C symbols D) (code : ArrowCode C symbols) :
    (extendAssignment (Index := Index) meanings).evaluateArrow (originalArrow code) =
      meanings.evaluateArrow code :=
  ((inclusion signature declarations).evaluateArrow_precompose (extendAssignment meanings) code).trans
    (congrArg (fun value : Assignment C symbols D => value.evaluateArrow code)
      (restricted_assignment signature declarations meanings))

/-- Local satisfaction uses independently admitted complete parallel arrows. -/
def Satisfies (meanings : Assignment C symbols D) (realized : Realization signature meanings) : Prop :=
  ∀ origin, (Interpretation.functor meanings realized).map (classOf (declarations origin).left) =
    (Interpretation.functor meanings realized).map (classOf (declarations origin).right)

theorem extended_realization (meanings : Assignment C symbols D)
    (realized : Realization signature meanings)
    (satisfied : Satisfies signature declarations meanings realized) :
    Realization (extend signature declarations) (extendAssignment meanings) where
  source origin := (evaluate_object_original signature declarations meanings (signature.source origin)).trans
    (realized.source origin)
  target origin := (evaluate_object_original signature declarations meanings (signature.target origin)).trans
    (realized.target origin)
  equation origin := by
    cases origin with
    | inl origin =>
        obtain ⟨value, source, target, first, second⟩ := realized.equation origin
        exact ⟨value,
          (evaluate_object_original signature declarations meanings _).trans source,
          (evaluate_object_original signature declarations meanings _).trans target,
          (evaluate_arrow_original signature declarations meanings _).trans first,
          (evaluate_arrow_original signature declarations meanings _).trans second⟩
    | inr origin =>
        refine ⟨⟨objectValue meanings realized (declarations origin).source,
          objectValue meanings realized (declarations origin).target,
          rawArrowValue meanings realized (declarations origin).left⟩, ?_, ?_, ?_, ?_⟩
        · exact (evaluate_object_original signature declarations meanings _).trans
            (objectValue_readout meanings realized (declarations origin).source)
        · exact (evaluate_object_original signature declarations meanings _).trans
            (objectValue_readout meanings realized (declarations origin).target)
        · exact (evaluate_arrow_original signature declarations meanings _).trans
            (rawArrowValue_readout meanings realized (declarations origin).left)
        · have same : rawArrowValue meanings realized (declarations origin).right =
              rawArrowValue meanings realized (declarations origin).left := (satisfied origin).symm
          exact (evaluate_arrow_original signature declarations meanings _).trans
            ((rawArrowValue_readout meanings realized (declarations origin).right).trans
              (congrArg (fun arrow => some (⟨_, _, arrow⟩ : ArrowValue D)) same))

theorem necessary_satisfaction (meanings : Assignment C symbols D)
    (realized : Realization signature meanings)
    (extended : Realization (extend signature declarations) (extendAssignment meanings)) :
    Satisfies signature declarations meanings realized := by
  intro origin
  obtain ⟨value, _, _, first, second⟩ := extended.equation (Sum.inr origin)
  have originalFirst := (evaluate_arrow_original signature declarations meanings
    (declarations origin).left.code).symm.trans first
  have originalSecond := (evaluate_arrow_original signature declarations meanings
    (declarations origin).right.code).symm.trans second
  exact ArrowValue.arrow_injective (Option.some.inj
    ((rawArrowValue_readout meanings realized (declarations origin).left).symm.trans
      (originalFirst.trans (originalSecond.symm.trans
        (rawArrowValue_readout meanings realized (declarations origin).right)))))

theorem realization_iff_satisfaction (meanings : Assignment C symbols D)
    (realized : Realization signature meanings) :
    Realization (extend signature declarations) (extendAssignment meanings) ↔
      Satisfies signature declarations meanings realized :=
  ⟨necessary_satisfaction signature declarations meanings realized,
    extended_realization signature declarations meanings realized⟩

theorem complete_restriction (meanings : Assignment C symbols D)
    (realized : Realization signature meanings)
    (satisfied : Satisfies signature declarations meanings realized) :
    (inclusion signature declarations).functor ⋙
        Interpretation.functor (extendAssignment meanings)
          (extended_realization signature declarations meanings realized satisfied) =
      Interpretation.functor meanings realized := by
  have result := (inclusion signature declarations).functor_precompose (extendAssignment meanings)
    (extended_realization signature declarations meanings realized satisfied)
  simpa only [restricted_assignment] using result

end Mettapedia.CategoryTheory.RelativeClosedSyntax.EquationExtension
