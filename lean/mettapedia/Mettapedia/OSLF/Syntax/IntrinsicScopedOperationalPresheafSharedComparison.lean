import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafBaseComparison
import Mettapedia.OSLF.Syntax.IntrinsicScopedSharedLocalPresheafComparison
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalModelPresheaf

/-!
# The actual shared operational presheaf through the unpruned local adapter

Every selected rule retains its complete original telescope. The existing
whole-history comparison preserves each assignment and substitution, so the
generic reduction extension covers precisely the existing shared model's
reduction sections. This statement does not apply to a pruned telescope
without a separately proved assignment-extension coverage hypothesis.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafSharedComparison

open _root_.CategoryTheory
open IntrinsicScopedSharedLocalPolynomialComparison (localRules)
open IntrinsicScopedSharedLocalPresheafComparison (localTreeModel sharedTreeModel retainedWitness_iff)
open IntrinsicScopedOperationalPresheafPrograms (target power)
open IntrinsicScopedOperationalPresheafEvents (binderExtension)
open IntrinsicScopedOperationalPresheafInterpretation (extensionReductionComparison)
open IntrinsicScopedOperationalPresheafCategoricalModel (categoricalModel)
open IntrinsicScopedConditionalPresheaf (Base states)

universe u
variable {S : Signature} {telescope schema : List (MetaArity S)}
variable (R : List (IntrinsicScopedConditionalPolynomial.Rule S telescope))
variable (A : BindingCloneAlgebra.Algebra.{u} S)
variable (equations : List (EqAxiom S schema))
variable (satisfies : BindingEquationInterpretation.Satisfies A equations)

/-- The existing complete shared-history model supplies the actual unpruned
rule-local categorical operational model in its original presheaf target. -/
def sharedCategoricalModel :
    IntrinsicScopedLocalActedCategoricalModels.CategoricalModel (localRules R) equations
      (D := target A) :=
  categoricalModel (localRules R) (localTreeModel R A) equations satisfies

/-- The canonical authored equation quotient has this genuine complete-history model. -/
def quotientSharedCategoricalModel :
    IntrinsicScopedLocalActedCategoricalModels.CategoricalModel (localRules R) equations
      (D := target (BindingEquationQuotientModel.algebra equations)) :=
  sharedCategoricalModel R (BindingEquationQuotientModel.algebra equations) equations
    (BindingEquationQuotientModel.algebra_satisfies equations)

/-- At every contextual power, the interpreted generic reduction covers
exactly the old shared model's reduction sections at the extended clone stage. -/
theorem extension_section_iff_shared_modelReduction (Γ : Ctx S) (s : S.Srt)
    (X : Base A) (first last : (power A Γ s).obj X) :
    (∃ input : ((IntrinsicScopedLocalActedPresheaf.modelPresheafExtension.{0}
        (sharedCategoricalModel R A equations satisfies)).obj
          (IntrinsicScopedLocalActedPresheaf.genericReduction.{u}
            (localRules R) equations Γ s).toFunctor).obj X,
      ((extensionReductionComparison (localRules R) (localTreeModel R A) equations satisfies Γ s).app X
        input).val = (first, last)) ↔
      ((⟨s, MultiBinderPresheaf.scopedBodyEquiv A X.unop Γ s first⟩,
        ⟨s, MultiBinderPresheaf.scopedBodyEquiv A X.unop Γ s last⟩) :
          (states A).obj ((binderExtension A Γ).obj X) ×
            (states A).obj ((binderExtension A Γ).obj X)) ∈
        (IntrinsicScopedConditionalModelPresheaf.modelReduction R (sharedTreeModel R A)).obj
          ((binderExtension A Γ).obj X) :=
  (IntrinsicScopedOperationalPresheafInterpretation.extension_section_iff
    (localRules R) (localTreeModel R A) equations satisfies Γ s X first last).trans
      ((retainedWitness_iff R A _).symm.trans
        (IntrinsicScopedConditionalModelPresheaf.mem_modelReduction_iff R (sharedTreeModel R A)
          ((binderExtension A Γ).obj X) s
          (MultiBinderPresheaf.scopedBodyEquiv A X.unop Γ s first)
          (MultiBinderPresheaf.scopedBodyEquiv A X.unop Γ s last)).symm)

/-- On the actual free shared model this is the established least
substitution-stable reduction subfunctor, through its existing proved equality. -/
theorem extension_section_iff_shared_reduction (Γ : Ctx S) (s : S.Srt)
    (X : Base A) (first last : (power A Γ s).obj X) :
    (∃ input : ((IntrinsicScopedLocalActedPresheaf.modelPresheafExtension.{0}
        (sharedCategoricalModel R A equations satisfies)).obj
          (IntrinsicScopedLocalActedPresheaf.genericReduction.{u}
            (localRules R) equations Γ s).toFunctor).obj X,
      ((extensionReductionComparison (localRules R) (localTreeModel R A) equations satisfies Γ s).app X
        input).val = (first, last)) ↔
      ((⟨s, MultiBinderPresheaf.scopedBodyEquiv A X.unop Γ s first⟩,
        ⟨s, MultiBinderPresheaf.scopedBodyEquiv A X.unop Γ s last⟩) :
          (states A).obj ((binderExtension A Γ).obj X) ×
            (states A).obj ((binderExtension A Γ).obj X)) ∈
        (IntrinsicScopedConditionalPresheaf.reduction R A).obj ((binderExtension A Γ).obj X) := by
  have compared := extension_section_iff_shared_modelReduction R A equations satisfies Γ s X first last
  rw [IntrinsicScopedConditionalModelPresheaf.free_modelReduction_eq] at compared
  exact compared

end Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafSharedComparison
