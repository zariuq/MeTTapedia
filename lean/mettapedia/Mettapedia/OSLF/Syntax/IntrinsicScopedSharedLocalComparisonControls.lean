import Mettapedia.OSLF.Syntax.IntrinsicScopedSharedLocalPresheafComparison
import Mettapedia.OSLF.Syntax.IntrinsicLambdaScopedConditionalExample

/-!
# A real binder-local firing through the unpruned shared-to-local adapter

The existing LamCong history contains the actual open beta firing below its
binder. Its local image retains that history and gives a genuine reduction
section. The child's target cannot be represented by weakening a closed term.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedSharedLocalComparisonControls

open IntrinsicScopedSharedLocalPolynomialComparison
open IntrinsicScopedSharedLocalTreeComparison
open IntrinsicScopedSharedLocalPresheafComparison
open IntrinsicScopedJudgmentActionPresheaf
open AuthoredPositionedRulePolynomial (Judgment)
open LambdaContextualRung (sig Srt)
open IntrinsicLambdaScopedConditionalExample (betaAndLamCong lamOccurrence lamTree)

abbrev termAlgebra := BindingCloneAlgebra.terms sig

abbrev lamJudgment : Judgment termAlgebra :=
  IntrinsicScopedConditionalPolynomial.conclusionJudgment betaAndLamCong termAlgebra lamOccurrence

/-- A real local history obtained from the existing two-node LamCong/beta tree. -/
noncomputable def localLamTree :
    IntrinsicScopedLocalPolynomial.Tree (localRules betaAndLamCong) termAlgebra lamJudgment :=
  toLocalTree betaAndLamCong termAlgebra lamJudgment lamTree

/-- The complete original history is recovered, including its open beta child. -/
theorem lam_history_recovered :
    toSharedTree betaAndLamCong termAlgebra lamJudgment localLamTree = lamTree :=
  IntrinsicScopedSharedLocalTreeComparison.toShared_toLocal
    betaAndLamCong termAlgebra lamJudgment lamTree

abbrev closedStage : IntrinsicScopedConditionalPresheaf.Base termAlgebra :=
  Opposite.op (Mettapedia.GSLT.LanguageDef.MultiSortedClone.ContextObject.ofList termAlgebra.substitution.toClone [])

/-- The local history supplies an actual retained reduction section. -/
theorem lam_reduction_section :
    ((⟨Srt.term, lamJudgment.2.2.1⟩, ⟨Srt.term, lamJudgment.2.2.2⟩) :
      (IntrinsicScopedConditionalPresheaf.states termAlgebra).obj closedStage ×
        (IntrinsicScopedConditionalPresheaf.states termAlgebra).obj closedStage) ∈
      (reduction (localTreeModel betaAndLamCong termAlgebra).toAction).obj closedStage :=
  (mem_reduction_iff (localTreeModel betaAndLamCong termAlgebra).toAction closedStage
    Srt.term lamJudgment.2.2.1 lamJudgment.2.2.2).mpr ⟨localLamTree⟩

/-- The converted premise still asks for the actual binder-extended child. -/
theorem lam_child_preserved :
    IntrinsicScopedLocalPolynomial.childJudgment (localRules betaAndLamCong) termAlgebra
      (toLocalInstance betaAndLamCong lamOccurrence)
      (toLocalPosition betaAndLamCong lamOccurrence ⟨0, by decide⟩) =
    (⟨[Srt.term], Srt.term, LambdaContextualRung.appT (LambdaContextualRung.lamT (.var .zero)) (.var .zero), Term.var Var.zero⟩ : Judgment termAlgebra) := by
  refine (toLocal_child betaAndLamCong lamOccurrence ⟨0, by decide⟩).trans ?_
  convert IntrinsicLambdaScopedConditionalExample.openBeta_child using 1
  · congr 1
  · rfl

private theorem lam_child_terms :
    (IntrinsicScopedLocalPolynomial.childJudgment (localRules betaAndLamCong) termAlgebra
      (toLocalInstance betaAndLamCong lamOccurrence)
      (toLocalPosition betaAndLamCong lamOccurrence ⟨0, by decide⟩)).2.2 =
    (LambdaContextualRung.appT (LambdaContextualRung.lamT (.var .zero)) (.var .zero),
      (Term.var Var.zero : Term sig [Srt.term] Srt.term)) := by
  have sorted := eq_of_heq (Sigma.mk.inj_iff.mp lam_child_preserved).2
  exact eq_of_heq (Sigma.mk.inj_iff.mp sorted).2

/-- A closed-only premise model cannot provide this bound-variable result. -/
theorem lam_child_result_not_closed :
    ¬ ∃ closed : Term sig [] Srt.term,
      weaken closed =
        (IntrinsicScopedLocalPolynomial.childJudgment (localRules betaAndLamCong) termAlgebra
          (toLocalInstance betaAndLamCong lamOccurrence)
          (toLocalPosition betaAndLamCong lamOccurrence ⟨0, by decide⟩)).2.2.2 := by
  rw [congrArg Prod.snd lam_child_terms]
  exact LambdaContextualRung.bound_result_not_closed

/-- The retained premise is a term-changing beta firing under the binder. -/
theorem lam_child_changes_term :
    (IntrinsicScopedLocalPolynomial.childJudgment (localRules betaAndLamCong) termAlgebra
      (toLocalInstance betaAndLamCong lamOccurrence)
      (toLocalPosition betaAndLamCong lamOccurrence ⟨0, by decide⟩)).2.2.1 ≠
    (IntrinsicScopedLocalPolynomial.childJudgment (localRules betaAndLamCong) termAlgebra
      (toLocalInstance betaAndLamCong lamOccurrence)
      (toLocalPosition betaAndLamCong lamOccurrence ⟨0, by decide⟩)).2.2.2 := by
  rw [congrArg Prod.fst lam_child_terms, congrArg Prod.snd lam_child_terms]
  exact LambdaContextualRung.open_beta_changes_term

end Mettapedia.OSLF.Binding.IntrinsicScopedSharedLocalComparisonControls
