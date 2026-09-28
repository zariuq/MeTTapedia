import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalPolynomial
import Mettapedia.OSLF.Syntax.LambdaContextualRung
import Mettapedia.OSLF.Syntax.PositionEnumeration
import Mettapedia.OSLF.Syntax.LambdaAuthoredLamCongExecutionComparison

/-!
# A binder-local lambda rule in the intrinsic conditional presentation

The abstraction congruence schema uses two contextual metavariables, each
allowed to depend on the lambda-bound variable. Its unique recursive premise
is a step in the context extended by that binder. The concrete open beta
instance retains that variable in the requested child judgment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicLambdaScopedConditionalExample

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
open Mettapedia.OSLF.Binding.SemanticContextualMetavariables
open Mettapedia.OSLF.Binding.SemanticScopedPremiseInterpretation
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)
open Mettapedia.OSLF.Binding.LambdaScopedAuthoringComparison (encodeTerm)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution (rewriteAt)
open Mettapedia.GSLT.Examples.ScopedLamCongExecution (language)

abbrev metas : List (MetaArity sig) :=
  [([Srt.term], Srt.term), ([Srt.term], Srt.term)]

abbrev schemaSig : Signature := withMetas sig metas

/-- A body metavariable explicitly applied to the locally bound variable. -/
def bodyLeft : Term schemaSig [Srt.term] Srt.term :=
  .op (Sum.inr (MetaOp.mk (M := metas) 0))
    (.cons (.var .zero) .nil)

def bodyRight : Term schemaSig [Srt.term] Srt.term :=
  .op (Sum.inr (MetaOp.mk (M := metas) 1))
    (.cons (.var .zero) .nil)

def lamLeft : Term schemaSig [] Srt.term :=
  .op (Sum.inl Op.lam) (.cons bodyLeft .nil)

def lamRight : Term schemaSig [] Srt.term :=
  .op (Sum.inl Op.lam) (.cons bodyRight .nil)

/-- The premise's context is the actual one-binder extension. -/
def lamCong : Rule sig metas where
  conclusion := {
    ctx := []
    sort := Srt.term
    lhs := lamLeft
    rhs := lamRight
    position := rootPosition lamLeft }
  premises := [{
    binders := [Srt.term]
    sort := Srt.term
    source := bodyLeft
    target := bodyRight }]

abbrev rules : List (Rule sig metas) := [lamCong]

/-- An occurrence of the abstraction rule at any ambient context. -/
def occurrence (A : BindingCloneAlgebra.Algebra.{0} sig)
    (Γ : Ctx sig) (valuation : Valuation (M := metas) A Γ) :
    Instance rules A where
  index := 0
  ambient := Γ
  valuation := valuation
  close := fun _ var => nomatch var

/-- Any two intrinsic bodies give a semantic LamCong occurrence in the free
term model, including bodies that use ambient variables beyond the binder. -/
def pairValuation (Γ : Ctx sig)
    (left right : Term sig (Srt.term :: Γ) Srt.term) :
    Valuation (M := metas) (BindingCloneAlgebra.terms sig) Γ
  | ⟨0, _⟩ => left
  | ⟨1, _⟩ => right
  | ⟨_ + 2, impossible⟩ => by simp [metas] at impossible

private def oneEnvironment (Γ : Ctx sig) :
    Sub sig (Srt.term :: Γ) (Srt.term :: Γ) :=
  SemanticContextualMetavariables.joinEnvironment
    (fun _ var => match var with
      | .zero => Term.var Var.zero
      | .succ old => nomatch old : Sub sig [Srt.term] (Srt.term :: Γ))
    (fun _ var => Term.var (.succ var) : Sub sig Γ (Srt.term :: Γ))

private theorem oneEnvironment_id (Γ : Ctx sig) :
    oneEnvironment Γ = (fun _ var => Term.var var) := by
  funext sort var
  cases var with
  | zero => rfl
  | succ _ => rfl

theorem pair_child (Γ : Ctx sig)
    (left right : Term sig (Srt.term :: Γ) Srt.term) :
    childJudgment rules (BindingCloneAlgebra.terms sig)
      (occurrence (BindingCloneAlgebra.terms sig) Γ
        (pairValuation Γ left right))
      ⟨0, by simp [occurrence, rules, lamCong]⟩ =
      (⟨Srt.term :: Γ, Srt.term, left, right⟩ :
        Judgment (BindingCloneAlgebra.terms sig)) := by
  change (⟨Srt.term :: Γ, Srt.term,
      bind (oneEnvironment Γ) left,
      bind (oneEnvironment Γ) right⟩ :
        Judgment (BindingCloneAlgebra.terms sig)) = _
  rw [oneEnvironment_id]
  exact congrArg₂ (fun l r =>
    (⟨Srt.term :: Γ, Srt.term, l, r⟩ :
      Judgment (BindingCloneAlgebra.terms sig)))
    (bind_id left) (bind_id right)

/-- The sole recursive position requests a step below the lambda binder. -/
theorem lamCong_premise_context
    (A : BindingCloneAlgebra.Algebra.{0} sig)
    (Γ : Ctx sig) (valuation : Valuation (M := metas) A Γ) :
    (childJudgment rules A (occurrence A Γ valuation)
      ⟨0, by simp [occurrence, rules, lamCong]⟩).1 =
      Srt.term :: Γ := rfl

/-- The constructor's result is abstraction of precisely the two endpoints
requested from its binder-local child. -/
theorem lamCong_conclusion_from_child
    (A : BindingCloneAlgebra.Algebra.{0} sig)
    (Γ : Ctx sig) (valuation : Valuation (M := metas) A Γ) :
    let child := childJudgment rules A (occurrence A Γ valuation)
      ⟨0, by simp [occurrence, rules, lamCong]⟩
    conclusionJudgment rules A (occurrence A Γ valuation) =
      (⟨Γ, Srt.term,
        A.operation Op.lam (.cons child.2.2.1 .nil),
        A.operation Op.lam (.cons child.2.2.2 .nil)⟩ : Judgment A) := by
  rfl

/-- The same arbitrary contextual bodies appear under the enclosing binder
at the constructor's conclusion; no ambient variable is captured. -/
theorem pair_conclusion (Γ : Ctx sig)
    (left right : Term sig (Srt.term :: Γ) Srt.term) :
    conclusionJudgment rules (BindingCloneAlgebra.terms sig)
      (occurrence (BindingCloneAlgebra.terms sig) Γ
        (pairValuation Γ left right)) =
      (⟨Γ, Srt.term, lamT left, lamT right⟩ :
        Judgment (BindingCloneAlgebra.terms sig)) := by
  change (⟨Γ, Srt.term,
      lamT (bind (oneEnvironment Γ) left),
      lamT (bind (oneEnvironment Γ) right)⟩ :
        Judgment (BindingCloneAlgebra.terms sig)) = _
  rw [oneEnvironment_id]
  exact congrArg₂ (fun l r =>
    (⟨Γ, Srt.term, lamT l, lamT r⟩ :
      Judgment (BindingCloneAlgebra.terms sig)))
    (bind_id left) (bind_id right)

/-- Every actual child step at the requested binder-local judgment yields
the enclosing LamCong step, for arbitrary ambient context and body terms. -/
theorem pair_conditional_sound (Γ : Ctx sig)
    (left right : Term sig (Srt.term :: Γ) Srt.term)
    (child : LambdaContextualRung.Step (Srt.term :: Γ) left right) :
    LambdaContextualRung.Step Γ
      (conclusionJudgment rules (BindingCloneAlgebra.terms sig)
        (occurrence (BindingCloneAlgebra.terms sig) Γ
          (pairValuation Γ left right))).2.2.1
      (conclusionJudgment rules (BindingCloneAlgebra.terms sig)
        (occurrence (BindingCloneAlgebra.terms sig) Γ
          (pairValuation Γ left right))).2.2.2 := by
  change LambdaContextualRung.Step Γ
    (lamT (bind (oneEnvironment Γ) left))
    (lamT (bind (oneEnvironment Γ) right))
  rw [oneEnvironment_id]
  have sourceEq :
      lamT (bind (fun _ var => Term.var var) left) = lamT left :=
    congrArg lamT (bind_id left)
  have targetEq :
      lamT (bind (fun _ var => Term.var var) right) = lamT right :=
    congrArg lamT (bind_id right)
  rw [sourceEq, targetEq]
  exact LambdaContextualRung.Step.lamCong child

private def openBeta : Term sig [Srt.term] Srt.term :=
  appT (lamT (.var .zero)) (.var .zero)

/-- A concrete open beta firing, used to test the free conditional-rule
algebra rather than merely its endpoint projection. -/
def openBetaRule : Rule sig metas where
  conclusion := {
    ctx := [Srt.term]
    sort := Srt.term
    lhs := embed (M := metas) openBeta
    rhs := embed (M := metas) (Term.var Var.zero)
    position := rootPosition (embed (M := metas) openBeta) }
  premises := []

abbrev betaAndLamCong : List (Rule sig metas) := [openBetaRule, lamCong]

/-- The two contextual bodies for the open-beta LamCong example. -/
def openBetaValuation :
    Valuation (M := metas) (BindingCloneAlgebra.terms sig) []
  | ⟨0, _⟩ => openBeta
  | ⟨1, _⟩ => .var .zero
  | ⟨_ + 2, impossible⟩ => by simp [metas] at impossible

private def openBetaRuleValuation :
    Valuation (M := metas) (BindingCloneAlgebra.terms sig) [Srt.term] :=
  fun
  | ⟨0, _⟩ => Term.var Var.zero
  | ⟨1, _⟩ => Term.var Var.zero
  | ⟨_ + 2, impossible⟩ => by simp [metas] at impossible

def betaOccurrence : Instance betaAndLamCong (BindingCloneAlgebra.terms sig) where
  index := 0
  ambient := [Srt.term]
  valuation := openBetaRuleValuation
  close := fun _ var => Term.var var

def lamOccurrence : Instance betaAndLamCong (BindingCloneAlgebra.terms sig) where
  index := 1
  ambient := []
  valuation := openBetaValuation
  close := fun _ var => nomatch var

/-- The beta constructor concludes at the exact child judgment requested
by the enclosing LamCong constructor. -/
theorem beta_concludes_lam_child :
    conclusionJudgment betaAndLamCong (BindingCloneAlgebra.terms sig)
        betaOccurrence =
      childJudgment betaAndLamCong (BindingCloneAlgebra.terms sig)
        lamOccurrence ⟨0, by decide⟩ := by
  rfl

private abbrev concretePolynomial :=
  IntrinsicScopedConditionalPolynomial.rules betaAndLamCong
    (BindingCloneAlgebra.terms sig)

/-- The open beta firing is a leaf of the same freely generated conditional
rule tree that contains LamCong. -/
def betaTree : concretePolynomial.Fix ()
    (conclusionJudgment betaAndLamCong (BindingCloneAlgebra.terms sig)
      betaOccurrence) :=
  .roll ⟨betaOccurrence, rfl⟩ (fun position => Fin.elim0 position)

/-- A real two-level tree: LamCong requests its child below one binder,
and that child is the beta leaf rather than an assumed relation fact. -/
def lamTree : concretePolynomial.Fix ()
    (conclusionJudgment betaAndLamCong (BindingCloneAlgebra.terms sig)
      lamOccurrence) :=
  .roll ⟨lamOccurrence, rfl⟩ (by
    intro position
    change Fin 1 at position
    have positionEq : position = 0 := Fin.eq_zero position
    subst position
    change concretePolynomial.Fix ()
      (childJudgment betaAndLamCong (BindingCloneAlgebra.terms sig)
        lamOccurrence ⟨0, by decide⟩)
    rw [← beta_concludes_lam_child]
    exact betaTree)

theorem lamTree_has_beta_child :
    Nonempty (concretePolynomial.Fix ()
      (childJudgment betaAndLamCong (BindingCloneAlgebra.terms sig)
        lamOccurrence ⟨0, by decide⟩)) := by
  rw [← beta_concludes_lam_child]
  exact ⟨betaTree⟩

theorem openBeta_child :
    childJudgment rules (BindingCloneAlgebra.terms sig)
        (occurrence (BindingCloneAlgebra.terms sig) [] openBetaValuation)
        ⟨0, by simp [occurrence, rules, lamCong]⟩ =
      (⟨[Srt.term], Srt.term, openBeta, Term.var Var.zero⟩ :
        Judgment (BindingCloneAlgebra.terms sig)) := by
  rfl

/-- This requested child is the actual open beta step of the contextual
lambda relation, rather than merely an endpoint pair of the right shape. -/
theorem openBeta_child_fires :
    LambdaContextualRung.Step [Srt.term]
      (childJudgment rules (BindingCloneAlgebra.terms sig)
        (occurrence (BindingCloneAlgebra.terms sig) [] openBetaValuation)
        ⟨0, by simp [occurrence, rules, lamCong]⟩).2.2.1
      (childJudgment rules (BindingCloneAlgebra.terms sig)
        (occurrence (BindingCloneAlgebra.terms sig) [] openBetaValuation)
        ⟨0, by simp [occurrence, rules, lamCong]⟩).2.2.2 := by
  change LambdaContextualRung.Step [Srt.term] openBeta (Term.var Var.zero)
  exact LambdaContextualRung.open_beta_uses_bound_variable

/-- Discharging the child through LamCong produces exactly the closed
abstraction step in the source's four-rule contextual reduction. -/
theorem openBeta_conclusion_fires :
    LambdaContextualRung.Step []
      (conclusionJudgment rules (BindingCloneAlgebra.terms sig)
        (occurrence (BindingCloneAlgebra.terms sig) [] openBetaValuation)).2.2.1
      (conclusionJudgment rules (BindingCloneAlgebra.terms sig)
        (occurrence (BindingCloneAlgebra.terms sig) [] openBetaValuation)).2.2.2 := by
  change LambdaContextualRung.Step [] (lamT openBeta) (lamT (Term.var Var.zero))
  exact LambdaContextualRung.closed_step_from_open_body

/-- The child result uses the bound variable and cannot be recovered from a
closed root result by weakening. This excludes a binder-free premise model. -/
theorem openBeta_child_result_not_closed :
    ¬ ∃ closed : Term sig [] Srt.term,
      weaken closed =
        (childJudgment rules (BindingCloneAlgebra.terms sig)
          (occurrence (BindingCloneAlgebra.terms sig) [] openBetaValuation)
          ⟨0, by simp [occurrence, rules, lamCong]⟩).2.2.2 := by
  change ¬ ∃ closed : Term sig [] Srt.term,
    weaken closed = (Term.var Var.zero : Term sig [Srt.term] Srt.term)
  exact LambdaContextualRung.bound_result_not_closed

/-- The premise is a genuine reduction, not an equality dressed as a
recursive child. -/
theorem openBeta_child_changes_term :
    (childJudgment rules (BindingCloneAlgebra.terms sig)
      (occurrence (BindingCloneAlgebra.terms sig) [] openBetaValuation)
      ⟨0, by simp [occurrence, rules, lamCong]⟩).2.2.1 ≠
    (childJudgment rules (BindingCloneAlgebra.terms sig)
      (occurrence (BindingCloneAlgebra.terms sig) [] openBetaValuation)
      ⟨0, by simp [occurrence, rules, lamCong]⟩).2.2.2 := by
  change openBeta ≠ (Term.var Var.zero : Term sig [Srt.term] Srt.term)
  exact LambdaContextualRung.open_beta_changes_term

/-- The canonical authored executor realizes this same concrete conditional
instance and retains both the inner beta and outer LamCong occurrences. -/
theorem openBeta_authored_execution :
    (.fire 1 [.step 0 0 (.fire 0 [])],
      encodeTerm
        (conclusionJudgment rules (BindingCloneAlgebra.terms sig)
          (occurrence (BindingCloneAlgebra.terms sig) [] openBetaValuation)).2.2.2) ∈
      rewriteAt RelationEnv.empty language 2 0
        (encodeTerm
          (conclusionJudgment rules (BindingCloneAlgebra.terms sig)
            (occurrence (BindingCloneAlgebra.terms sig) [] openBetaValuation)).2.2.1) := by
  change (.fire 1 [.step 0 0 (.fire 0 [])],
      encodeTerm (lamT (Term.var Var.zero))) ∈
    rewriteAt RelationEnv.empty language 2 0 (encodeTerm (lamT openBeta))
  exact Mettapedia.OSLF.Binding.LambdaAuthoredLamCongExecutionComparison.authored_nested_beta_under_lam
    (Γ := []) (inner := Term.var Var.zero) (argument := Term.var Var.zero)

#print axioms lamCong_premise_context
#print axioms lamCong_conclusion_from_child
#print axioms pair_child
#print axioms pair_conclusion
#print axioms pair_conditional_sound
#print axioms beta_concludes_lam_child
#print axioms lamTree
#print axioms openBeta_child
#print axioms openBeta_child_fires
#print axioms openBeta_conclusion_fires
#print axioms openBeta_child_result_not_closed
#print axioms openBeta_child_changes_term
#print axioms openBeta_authored_execution

end Mettapedia.OSLF.Binding.IntrinsicLambdaScopedConditionalExample
