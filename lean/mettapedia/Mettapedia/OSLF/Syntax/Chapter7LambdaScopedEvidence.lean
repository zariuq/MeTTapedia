import Mettapedia.OSLF.Syntax.ScopedOperationalEvidenceExponential
import Mettapedia.OSLF.Syntax.ScopedPremiseEvidenceComparison
import Mettapedia.OSLF.Syntax.IntrinsicLambdaScopedConditionalExample
import Mettapedia.OSLF.Syntax.Chapter7ClosedBindingControl

/-!
# A genuine beta firing as a contextual premise value

The child of lambda congruence is a beta firing in the binder-extended
context. Here that retained firing, with its distinct endpoints, becomes a
contextual function. Its value is still the actual constructor tree; no
endpoint-existence predicate or program equation replaces it.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.Chapter7LambdaScopedEvidence

open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open Mettapedia.OSLF.Binding.Chapter7ClosedBindingControl
open Mettapedia.OSLF.Binding.IntrinsicLambdaScopedConditionalExample
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalModelPresheaf
open Mettapedia.OSLF.Binding.ScopedOperationalEvidenceExponential
open Mettapedia.OSLF.Binding.ScopedPremiseEvidenceComparison
open Mettapedia.OSLF.Binding.MultiBinderPresheaf
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf

private abbrev A := BindingCloneAlgebra.terms LambdaContextualRung.sig
private noncomputable abbrev Y := SubstitutionModel.free betaAndLamCong A
private abbrev emptyContext := ContextObject.ofList A.substitution.toClone []

/-- The open beta constructor is individual evidence at the child judgment
requested by the actual LamCong occurrence. -/
def localBetaEvent : ModelEvent betaAndLamCong Y [.term] :=
  ⟨.term, (openRedex, .var .zero), by
    change (IntrinsicScopedConditionalPolynomial.rules betaAndLamCong A).Fix ()
      (IntrinsicScopedConditionalPolynomial.conclusionJudgment
        betaAndLamCong A betaOccurrence)
    exact betaTree⟩

/-- One binder-local beta event, represented as a function of the bound
variable in the ambient empty context. -/
noncomputable def localBetaFunction :
    ((binders A [.term]).functorHom (modelEvents betaAndLamCong Y)).obj
      (Opposite.op emptyContext) :=
  (modelScopedEventEquiv betaAndLamCong A Y emptyContext [.term]).symm
    localBetaEvent

/-- Reading the function at the generic binder variable recovers the exact
open beta firing constructor, including its rule identity. -/
theorem localBetaFunction_event :
    modelScopedEventEquiv betaAndLamCong A Y emptyContext [.term]
      localBetaFunction = localBetaEvent :=
  Equiv.apply_symm_apply _ _

/-- Its source endpoint is the open redex, with the bound variable present
in the argument position. -/
theorem localBetaFunction_source :
    (modelSource betaAndLamCong Y).app
      (Opposite.op (ContextObject.ofList A.substitution.toClone [.term]))
      (modelScopedEventEquiv betaAndLamCong A Y emptyContext [.term]
        localBetaFunction) = ⟨.term, openRedex⟩ := by
  rw [localBetaFunction_event]
  rfl

/-- Its target endpoint is the bound variable itself. The two endpoints
remain distinct syntax even though a firing connects them. -/
theorem localBetaFunction_target :
    (modelTarget betaAndLamCong Y).app
      (Opposite.op (ContextObject.ofList A.substitution.toClone [.term]))
      (modelScopedEventEquiv betaAndLamCong A Y emptyContext [.term]
        localBetaFunction) = ⟨.term, (Term.var Var.zero)⟩ := by
  rw [localBetaFunction_event]
  rfl

theorem localBetaFunction_endpoints_distinct :
    (modelSource betaAndLamCong Y).app
        (Opposite.op (ContextObject.ofList A.substitution.toClone [.term]))
        localBetaEvent ≠
      (modelTarget betaAndLamCong Y).app
        (Opposite.op (ContextObject.ofList A.substitution.toClone [.term]))
        localBetaEvent := by
  intro same
  change (⟨.term, openRedex⟩ :
      Σ s : LambdaContextualRung.Srt,
        Term LambdaContextualRung.sig
          [LambdaContextualRung.Srt.term] s) =
    ⟨LambdaContextualRung.Srt.term,
      (Term.var Var.zero : Term LambdaContextualRung.sig
        [LambdaContextualRung.Srt.term]
        LambdaContextualRung.Srt.term)⟩ at same
  cases same

/-- The actual LamCong rule receives the beta firing as its one contextual
premise, with the binder available to that child. -/
private def lamCongChildren :
    ∀ position : Fin (betaAndLamCong.get lamOccurrence.index).premises.length,
      Y.evidence.carrier ()
        (IntrinsicScopedConditionalPolynomial.childJudgment
          betaAndLamCong A lamOccurrence position) := by
  intro position
  change Fin 1 at position
  have positionEq : position = 0 := Fin.eq_zero position
  subst position
  change Y.evidence.carrier ()
    (IntrinsicScopedConditionalPolynomial.childJudgment
      betaAndLamCong A lamOccurrence ⟨0, by decide⟩)
  rw [← beta_concludes_lam_child]
  exact betaTree

noncomputable def lamCongScopedInputs :
    ScopedRuleInputs betaAndLamCong Y lamOccurrence :=
  ruleInputsEquiv betaAndLamCong Y lamOccurrence lamCongChildren

/-- Converting the genuine child to a contextual function and back before
applying LamCong produces the very same two-level firing tree. -/
theorem lamCongScopedAction_eq_tree :
    scopedRuleAction betaAndLamCong Y lamOccurrence
      lamCongScopedInputs = lamTree := by
  unfold lamCongScopedInputs
  rw [scopedRuleAction_ofChildren]
  rfl

#print axioms localBetaEvent
#print axioms localBetaFunction_event
#print axioms localBetaFunction_source
#print axioms localBetaFunction_target
#print axioms localBetaFunction_endpoints_distinct
#print axioms lamCongScopedAction_eq_tree

end Mettapedia.OSLF.Binding.Chapter7LambdaScopedEvidence
