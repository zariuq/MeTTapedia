import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalClassifierSetSemantics
import Mettapedia.OSLF.Syntax.SecondOrderBindingAlgebraMap
import Mettapedia.OSLF.Syntax.IntrinsicLambdaFourRulePresentation

/-!
# Controls for combined contextual event interpretation

An authored program assignment can merge two different metavariable terms.
The two event-variable positions over those terms remain distinct after
base change, even though their endpoint judgments then agree.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedConditionalClassifierSetControls

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalFiniteContextChange
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial (Rule)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
open Mettapedia.OSLF.Binding.IndexedRuleFiniteListSkeleton
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalClassifierContext
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalClassifierSetSemantics

variable (S : Signature) (sort : S.Srt)

private abbrev oneMeta : Object S := ⟨[([], sort)]⟩
private abbrev twoMetas : Object S := ⟨[([], sort), ([], sort)]⟩

/-- Both target metavariables are instantiated by the one source generator. -/
private def mergeMetas : oneMeta S sort ⟶ twoMetas S sort := by
  intro i
  match i with
  | ⟨0, _⟩ => exact metaVar (M := (oneMeta S sort).arities) ⟨0, by simp⟩
  | ⟨1, _⟩ => exact metaVar (M := (oneMeta S sort).arities) ⟨0, by simp⟩
  | ⟨_ + 2, impossible⟩ => simp at impossible

private def firstTerm :
    Term (withMetas S (twoMetas S sort).arities) [] sort :=
  metaVar (M := (twoMetas S sort).arities) ⟨0, by simp⟩

private def secondTerm :
    Term (withMetas S (twoMetas S sort).arities) [] sort :=
  metaVar (M := (twoMetas S sort).arities) ⟨1, by simp⟩

private def firstJudgment : Judgment (termAlgebra (twoMetas S sort)) :=
  ⟨[], sort, firstTerm S sort, firstTerm S sort⟩

private def secondJudgment : Judgment (termAlgebra (twoMetas S sort)) :=
  ⟨[], sort, secondTerm S sort, secondTerm S sort⟩

/-- The two source event labels are genuinely different judgments. -/
theorem original_judgments_distinct :
    firstJudgment S sort ≠ secondJudgment S sort := by
  intro equal
  have termEqual : firstTerm S sort = secondTerm S sort := by
    exact congrArg Prod.fst
      (by simpa [firstJudgment, secondJudgment] using equal)
  exact distinct_nullary_generators S sort termEqual

/-- The noninjective assignment makes the two endpoint judgments agree. -/
theorem mapped_judgments_equal :
    mapJudgment (instIntoHom (mergeMetas S sort)) (firstJudgment S sort) =
      mapJudgment (instIntoHom (mergeMetas S sort)) (secondJudgment S sort) := by
  rfl

private def eventContext {M : List (MetaArity S)} (R : List (Rule S M)) :
    ListContext (IntrinsicScopedConditionalPolynomial.rules R
      (termAlgebra (twoMetas S sort))) where
  length := 2
  label := Fin.cases (firstJudgment S sort) (fun _ => secondJudgment S sort)

/-- Base change keeps the two event variables as different positions even
when their contextual judgments become equal. -/
theorem mapped_event_positions_distinct {M : List (MetaArity S)}
    (R : List (Rule S M)) :
    (⟨(0 : Fin 2), ⟨rfl⟩⟩ :
      (toContext (IntrinsicScopedConditionalPolynomial.rules R
        (termAlgebra (oneMeta S sort)))
        (pushContext R (instIntoHom (mergeMetas S sort))
          (eventContext S sort R))).slots
        (mapJudgment (instIntoHom (mergeMetas S sort))
          (firstJudgment S sort))) ≠
    (⟨(1 : Fin 2), ⟨(mapped_judgments_equal S sort).symm⟩⟩ :
      (toContext (IntrinsicScopedConditionalPolynomial.rules R
        (termAlgebra (oneMeta S sort)))
        (pushContext R (instIntoHom (mergeMetas S sort))
          (eventContext S sort R))).slots
        (mapJudgment (instIntoHom (mergeMetas S sort))
          (firstJudgment S sort))) := by
  intro equal
  have positions := congrArg Sigma.fst equal
  exact Fin.zero_ne_one positions

/-- An assignment into the premise context of lambda abstraction congruence
composes with its constructor according to the combined interpretation law.
The chosen rule index is the authored LamCong rule, whose premise is scoped
under one term binder. -/
theorem lambda_lamCong_mixed_composition
    (eqs : List (EqAxiom
      LambdaContextualRung.sig IntrinsicLambdaFourRulePresentation.metas))
    (target : SubstitutionOperationalModel
      IntrinsicLambdaFourRulePresentation.rules eqs)
    {X Y : EquationContexts
      (authoredEquationPresentation LambdaContextualRung.sig eqs)}
    {Γ : ListContext
      (IntrinsicScopedConditionalPolynomial.rules
        IntrinsicLambdaFourRulePresentation.rules
        (authoredEquationModelAt LambdaContextualRung.sig eqs X.as).algebra)}
    {judgment : Judgment
      (authoredEquationModelAt LambdaContextualRung.sig eqs Y.as).algebra}
    (shape : (IntrinsicScopedConditionalPolynomial.rules
      IntrinsicLambdaFourRulePresentation.rules
      (authoredEquationModelAt LambdaContextualRung.sig eqs Y.as).algebra).Shape
        PUnit.unit judgment)
    (_lamCong : shape.1.index.val = 3)
    (first : object IntrinsicLambdaFourRulePresentation.rules eqs X Γ ⟶
      object IntrinsicLambdaFourRulePresentation.rules eqs Y
        (arityList IntrinsicLambdaFourRulePresentation.rules
          (authoredEquationModelAt LambdaContextualRung.sig eqs Y.as).algebra
          shape))
    (value : Valuation IntrinsicLambdaFourRulePresentation.rules eqs
      target X Γ) :
    value.transport IntrinsicLambdaFourRulePresentation.rules eqs
        (first ≫ (constructor IntrinsicLambdaFourRulePresentation.rules
          eqs Y shape)) =
      (value.transport IntrinsicLambdaFourRulePresentation.rules eqs first).transport
        IntrinsicLambdaFourRulePresentation.rules eqs
        (constructor IntrinsicLambdaFourRulePresentation.rules eqs Y shape) := by
  exact (value.transport_comp IntrinsicLambdaFourRulePresentation.rules
    eqs first
    (constructor IntrinsicLambdaFourRulePresentation.rules eqs Y shape)).symm

end Mettapedia.OSLF.Binding.IntrinsicScopedConditionalClassifierSetControls
