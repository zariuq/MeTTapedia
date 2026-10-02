import Mettapedia.OSLF.Syntax.IntrinsicScopedAuthoredClassifiedInstance

/-!
# Authored process classes in the interpreted generic reduction

An ordinary term determines a section of the actual program presheaf at its
original clone context. The genuine cocontinuous extension has a reduction
section over two such programs exactly when the original local firing-tree
model has an individual witness between their equation classes.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedAuthoredClassifiedReduction

open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone (ContextObject)
open AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open IntrinsicScopedLocalPolynomial (LocalRule Tree)
open IntrinsicScopedAuthoredClassifiedInstance (algebra treeModel model)
open IntrinsicScopedOperationalPresheafPrograms (power)

variable {S : Signature} {schema : List (MetaArity S)}
variable (R : List (LocalRule S)) (equations : List (EqAxiom S schema))

/-- The original semantic substitution context, with its presheaf orientation. -/
def stage (Γ : Ctx S) : IntrinsicScopedConditionalPresheaf.Base (algebra equations) :=
  Opposite.op (ContextObject.ofList (algebra equations).substitution.toClone Γ)

/-- An authored term's equation class as a section of the actual program object. -/
def program {Γ : Ctx S} {s : S.Srt} (term : Term S Γ s) :
    (power (algebra equations) [] s).obj (stage equations Γ) :=
  (MultiBinderPresheaf.scopedBodyEquiv (algebra equations) (stage equations Γ).unop [] s).symm
    ((BindingEquationQuotientModel.projection equations).raw.map term)

/-- A section of the genuinely extended generic reduction over these authored programs. -/
def ExtendedReduction {Γ : Ctx S} {s : S.Srt} (source target : Term S Γ s) : Prop :=
  ∃ input : ((IntrinsicScopedLocalActedPresheaf.modelPresheafExtension.{0}
      (model R equations)).obj
        (IntrinsicScopedLocalActedPresheaf.genericReduction.{0} R equations [] s).toFunctor).obj
          (stage equations Γ),
    ((IntrinsicScopedOperationalPresheafInterpretation.extensionReductionComparison R
      (treeModel R (algebra equations)) equations
      (BindingEquationQuotientModel.algebra_satisfies equations) [] s).app
        (stage equations Γ) input).val = (program equations source, program equations target)

/-- Coverage is exactly the original retained local witnesses between equation classes. -/
theorem extension_iff_tree {Γ : Ctx S} {s : S.Srt} (source target : Term S Γ s) :
    ExtendedReduction R equations source target ↔
      Nonempty (Tree R (algebra equations)
        (mapJudgment (BindingEquationQuotientModel.projection equations)
          (⟨Γ, s, source, target⟩ : Judgment (BindingCloneAlgebra.terms S)))) := by
  have compared := IntrinsicScopedOperationalPresheafInterpretation.extension_section_iff R
      (treeModel R (algebra equations)) equations
      (BindingEquationQuotientModel.algebra_satisfies equations) [] s (stage equations Γ)
      (program equations source) (program equations target)
  have sourceEq : MultiBinderPresheaf.scopedBodyEquiv (algebra equations)
      (stage equations Γ).unop [] s (program equations source) =
        (BindingEquationQuotientModel.projection equations).raw.map source :=
    (MultiBinderPresheaf.scopedBodyEquiv (algebra equations)
      (stage equations Γ).unop [] s).apply_symm_apply _
  have targetEq : MultiBinderPresheaf.scopedBodyEquiv (algebra equations)
      (stage equations Γ).unop [] s (program equations target) =
        (BindingEquationQuotientModel.projection equations).raw.map target :=
    (MultiBinderPresheaf.scopedBodyEquiv (algebra equations)
      (stage equations Γ).unop [] s).apply_symm_apply _
  rw [sourceEq, targetEq] at compared
  simpa only [List.nil_append, ExtendedReduction, model, treeModel, stage,
    ContextObject.ofList, mapJudgment] using compared

end Mettapedia.OSLF.Binding.IntrinsicScopedAuthoredClassifiedReduction
