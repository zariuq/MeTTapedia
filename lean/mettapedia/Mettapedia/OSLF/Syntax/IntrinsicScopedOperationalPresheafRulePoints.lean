import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafEquations
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalSubstitution

/-!
# Actual rule occurrences at operational presheaf points

A generalized rule occurrence specializes each original contextual body at
an ordinary assignment and an ambient stage point. All declared metavariables,
the selected occurrence address, and the closing environment are retained.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafRulePoints

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open IntrinsicScopedConditionalPresheaf (Base)
open IntrinsicScopedOperationalPresheafPrograms (target model)
open IntrinsicScopedOperationalPresheafReadback (read readEnv read_reindex)
open IntrinsicScopedLocalPolynomial (LocalRule Instance)

universe u
variable {S : Signature} {A : BindingCloneAlgebra.Algebra.{u} S}
variable (R : List (LocalRule S))

/-- The actual generalized ordinary context beside the ambient stage. -/
abbrev occurrenceStage {Z : target A} (occurrence : Instance R ((model A).stage Z)) : target A :=
  (model A).ctx occurrence.ambient ⊗ Z

/-- Capture the original ordinary variables in the stage parameter, leaving
precisely the declared dependency prefix as the selected function's input. -/
def capturedBody {Z : target A} (occurrence : Instance R ((model A).stage Z))
    (index : Fin (R.get occurrence.index).1.length) :
    (model A).ElemOver (occurrenceStage R occurrence)
      ((R.get occurrence.index).1.get index).1 ((R.get occurrence.index).1.get index).2 :=
  (model A).captureBody (occurrence.valuation index) (snd _ _)
    ((model A).genericEnv occurrence.ambient Z)

/-- Every presheaf point determines a real occurrence in the original local model. -/
def pointInstance {Z : target A} (occurrence : Instance R ((model A).stage Z))
    (X : Base A) (point : (occurrenceStage R occurrence).obj X) : Instance R A where
  index := occurrence.index
  ambient := X.unop.context
  valuation := fun index => read A (capturedBody R occurrence index) X point
  close := readEnv A
    (CategoricalBindingModel.Model.envValue occurrence.close _ (snd _ _)
      ((model A).genericEnv occurrence.ambient Z)) X point

/-- The selected declaration address is unchanged by the actual point interpretation. -/
theorem pointInstance_index {Z : target A} (occurrence : Instance R ((model A).stage Z))
    (X : Base A) (point : (occurrenceStage R occurrence).obj X) :
    (pointInstance R occurrence X point).index = occurrence.index := rfl

/-- Closing values are read from the original generalized environment. -/
theorem pointInstance_close {Z : target A} (occurrence : Instance R ((model A).stage Z))
    (X : Base A) (point : (occurrenceStage R occurrence).obj X)
    {s : S.Srt} (var : Var (R.get occurrence.index).2.conclusion.ctx s) :
    (pointInstance R occurrence X point).close s var =
      IntrinsicScopedConditionalPresheaf.programsAtEquiv A s X
        (((occurrence.close s var).value _ (snd _ _)
          ((model A).genericEnv occurrence.ambient Z)).app X point) := rfl

/-- Every retained declared body is natural under actual ambient clone substitutions. -/
theorem pointInstance_valuation_reindex {Z : target A}
    (occurrence : Instance R ((model A).stage Z)) {X Y : Base A} (f : X ⟶ Y)
    (point : (occurrenceStage R occurrence).obj X)
    (index : Fin (R.get occurrence.index).1.length) :
    (pointInstance R occurrence Y ((occurrenceStage R occurrence).map f point)).valuation index =
      A.substitution.substitute
        (A.substitution.liftEnvironment
          (BindingSubstitutionAlgebra.fromPositions X.unop.context f.unop)
          ((R.get occurrence.index).1.get index).1)
        ((pointInstance R occurrence X point).valuation index) := by
  have value := read_reindex A (capturedBody R occurrence index) f point
  exact value.trans (congrArg
    (fun env => A.substitution.substitute env ((pointInstance R occurrence X point).valuation index))
    (MultiBinderPresheaf.fromPositions_extendScope A ((R.get occurrence.index).1.get index).1 f.unop))

/-- Actual point interpretation commutes with the existing whole-occurrence substitution. -/
theorem pointInstance_reindex {Z : target A} (occurrence : Instance R ((model A).stage Z))
    {X Y : Base A} (f : X ⟶ Y) (point : (occurrenceStage R occurrence).obj X) :
    pointInstance R occurrence Y ((occurrenceStage R occurrence).map f point) =
      IntrinsicScopedLocalPolynomial.Instance.subst R (pointInstance R occurrence X point)
        (BindingSubstitutionAlgebra.fromPositions X.unop.context f.unop) := by
  have values :
      (pointInstance R occurrence Y ((occurrenceStage R occurrence).map f point)).valuation =
        (IntrinsicScopedLocalPolynomial.Instance.subst R (pointInstance R occurrence X point)
          (BindingSubstitutionAlgebra.fromPositions X.unop.context f.unop)).valuation := by
    funext index
    exact pointInstance_valuation_reindex R occurrence f point index
  have close :
      (pointInstance R occurrence Y ((occurrenceStage R occurrence).map f point)).close =
        (IntrinsicScopedLocalPolynomial.Instance.subst R (pointInstance R occurrence X point)
          (BindingSubstitutionAlgebra.fromPositions X.unop.context f.unop)).close := by
    exact IntrinsicScopedOperationalPresheafReadback.readEnv_reindex A
      (CategoricalBindingModel.Model.envValue occurrence.close _ (snd _ _)
        ((model A).genericEnv occurrence.ambient Z)) f point
  exact congrArg₂ (fun valuation close => (⟨occurrence.index, Y.unop.context, valuation, close⟩ : Instance R A))
    values close

/-- The generalized conclusion reads to the actual original rule conclusion at every point. -/
theorem pointInstance_conclusion {Z : target A}
    (occurrence : Instance R ((model A).stage Z)) (X : Base A)
    (point : (occurrenceStage R occurrence).obj X) :
    (⟨X.unop.context, (IntrinsicScopedLocalPolynomial.conclusionJudgment R ((model A).stage Z) occurrence).2.1,
      IntrinsicScopedConditionalPresheaf.programsAtEquiv A _ X
        (((IntrinsicScopedLocalPolynomial.conclusionJudgment R ((model A).stage Z) occurrence).2.2.1).value
          (occurrenceStage R occurrence) (snd _ _)
          ((model A).genericEnv occurrence.ambient Z) |>.app X point),
      IntrinsicScopedConditionalPresheaf.programsAtEquiv A _ X
        (((IntrinsicScopedLocalPolynomial.conclusionJudgment R ((model A).stage Z) occurrence).2.2.2).value
          (occurrenceStage R occurrence) (snd _ _)
          ((model A).genericEnv occurrence.ambient Z) |>.app X point)⟩ :
      AuthoredPositionedRulePolynomial.Judgment A) =
        IntrinsicScopedLocalPolynomial.conclusionJudgment R A (pointInstance R occurrence X point) := by
  have left := IntrinsicScopedOperationalPresheafEquations.contextual_stage_value_point A
    occurrence.valuation (fun _ var => ((model A).stage Z).substitution.injectVar var)
    occurrence.close (snd _ _) ((model A).genericEnv occurrence.ambient Z)
    (R.get occurrence.index).2.conclusion.lhs X point
  have right := IntrinsicScopedOperationalPresheafEquations.contextual_stage_value_point A
    occurrence.valuation (fun _ var => ((model A).stage Z).substitution.injectVar var)
    occurrence.close (snd _ _) ((model A).genericEnv occurrence.ambient Z)
    (R.get occurrence.index).2.conclusion.rhs X point
  exact congrArg (fun pair => (⟨X.unop.context, (R.get occurrence.index).2.conclusion.sort, pair⟩ :
    AuthoredPositionedRulePolynomial.Judgment A)) (Prod.ext left right)

end Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafRulePoints
