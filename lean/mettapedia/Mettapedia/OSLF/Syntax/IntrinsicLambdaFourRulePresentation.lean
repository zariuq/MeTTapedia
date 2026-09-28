import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalSubstitutionModels
import Mettapedia.OSLF.Syntax.LambdaContextualRung
import Mettapedia.OSLF.Syntax.PositionEnumeration
import Mettapedia.OSLF.Syntax.LambdaAuthoredCanonicalFreeComparison
import Mettapedia.OSLF.Syntax.LambdaSemanticRulePolynomial

/-!
# One intrinsic presentation of the four contextual lambda rules

The rule list shares contextual metavariables among Beta, both application
congruence rules, and abstraction congruence. A LamCong child lives under its
own bound term variable. This presentation is interpreted by the general
substitution-operational model, rather than by four separate rule algebras.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicLambdaFourRulePresentation

open CategoryTheory.Limits
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
open Mettapedia.OSLF.Binding.SemanticContextualMetavariables
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)

/-- Two binder-dependent bodies and three ordinary term arguments suffice
for every one of the four Chapter 7 lambda rules. -/
abbrev metas : List (MetaArity sig) :=
  [([Srt.term], Srt.term), ([Srt.term], Srt.term),
   ([], Srt.term), ([], Srt.term), ([], Srt.term)]

abbrev schemaSig : Signature := withMetas sig metas

/-- Supply arbitrary contextual lambda bodies and ordinary arguments to one
shared metavariable context. Rule instances may ignore unused assignments. -/
def valuationOf (Γ : Ctx sig)
    (left right : Term sig (Srt.term :: Γ) Srt.term)
    (firstTerm secondTerm sharedTerm : Term sig Γ Srt.term) :
    Valuation (M := metas) (BindingCloneAlgebra.terms sig) Γ
  | ⟨0, _⟩ => left
  | ⟨1, _⟩ => right
  | ⟨2, _⟩ => firstTerm
  | ⟨3, _⟩ => secondTerm
  | ⟨4, _⟩ => sharedTerm
  | ⟨_ + 5, impossible⟩ => by simp [metas] at impossible

private def bodyLeft {Γ : Ctx schemaSig}
    (arg : Term schemaSig Γ Srt.term) : Term schemaSig Γ Srt.term :=
  .op (Sum.inr (MetaOp.mk (M := metas) 0)) (.cons arg .nil)

private def bodyRight {Γ : Ctx schemaSig}
    (arg : Term schemaSig Γ Srt.term) : Term schemaSig Γ Srt.term :=
  .op (Sum.inr (MetaOp.mk (M := metas) 1)) (.cons arg .nil)

private def first {Γ : Ctx schemaSig} : Term schemaSig Γ Srt.term :=
  .op (Sum.inr (MetaOp.mk (M := metas) 2)) .nil

private def second {Γ : Ctx schemaSig} : Term schemaSig Γ Srt.term :=
  .op (Sum.inr (MetaOp.mk (M := metas) 3)) .nil

private def shared {Γ : Ctx schemaSig} : Term schemaSig Γ Srt.term :=
  .op (Sum.inr (MetaOp.mk (M := metas) 4)) .nil

private def schemaApp {Γ : Ctx schemaSig}
    (function argument : Term schemaSig Γ Srt.term) :
    Term schemaSig Γ Srt.term :=
  .op (Sum.inl Op.app) (.cons function (.cons argument .nil))

private def schemaLam {Γ : Ctx schemaSig}
    (body : Term schemaSig (Srt.term :: Γ) Srt.term) :
    Term schemaSig Γ Srt.term :=
  .op (Sum.inl Op.lam) (.cons body .nil)

private def betaLeft : Term schemaSig [] Srt.term :=
  schemaApp (schemaLam (bodyLeft (.var .zero))) first

private def betaRight : Term schemaSig [] Srt.term :=
  bodyLeft first

/-- The unrestricted contextual Beta schema. -/
def beta : Rule sig metas where
  conclusion := {
    ctx := []
    sort := Srt.term
    lhs := betaLeft
    rhs := betaRight
    position := rootPosition betaLeft }
  premises := []

private def appCongLLeft : Term schemaSig [] Srt.term :=
  schemaApp first shared

private def appCongLRight : Term schemaSig [] Srt.term :=
  schemaApp second shared

/-- One step in function position, with the argument unchanged. -/
def appCongL : Rule sig metas where
  conclusion := {
    ctx := []
    sort := Srt.term
    lhs := appCongLLeft
    rhs := appCongLRight
    position := rootPosition appCongLLeft }
  premises := [{
    binders := []
    sort := Srt.term
    source := first
    target := second }]

private def appCongRLeft : Term schemaSig [] Srt.term :=
  schemaApp shared first

private def appCongRRight : Term schemaSig [] Srt.term :=
  schemaApp shared second

/-- One step in argument position, with the function unchanged. -/
def appCongR : Rule sig metas where
  conclusion := {
    ctx := []
    sort := Srt.term
    lhs := appCongRLeft
    rhs := appCongRRight
    position := rootPosition appCongRLeft }
  premises := [{
    binders := []
    sort := Srt.term
    source := first
    target := second }]

private def lamCongLeft : Term schemaSig [] Srt.term :=
  schemaLam (bodyLeft (.var .zero))

private def lamCongRight : Term schemaSig [] Srt.term :=
  schemaLam (bodyRight (.var .zero))

/-- Its child reduction is checked with the abstraction variable in scope. -/
def lamCong : Rule sig metas where
  conclusion := {
    ctx := []
    sort := Srt.term
    lhs := lamCongLeft
    rhs := lamCongRight
    position := rootPosition lamCongLeft }
  premises := [{
    binders := [Srt.term]
    sort := Srt.term
    source := bodyLeft (.var .zero)
    target := bodyRight (.var .zero) }]

/-- One ordered rule presentation: Beta, left, right, then abstraction. -/
def rules : List (Rule sig metas) :=
  [beta, appCongL, appCongR, lamCong]

theorem rule_inventory :
    rules.length = 4 ∧
      (rules.get ⟨0, by decide⟩).premises.length = 0 ∧
      (rules.get ⟨1, by decide⟩).premises.length = 1 ∧
      (rules.get ⟨2, by decide⟩).premises.length = 1 ∧
      (rules.get ⟨3, by decide⟩).premises.length = 1 ∧
      ((rules.get ⟨3, by decide⟩).premises.get ⟨0, by decide⟩).binders =
        [Srt.term] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The first constructor is available for every contextual assignment of
its body and argument, including genuinely open terms. -/
def betaOccurrence (Γ : Ctx sig)
    (valuation : Valuation (M := metas) (BindingCloneAlgebra.terms sig) Γ) :
    Instance rules (BindingCloneAlgebra.terms sig) where
  index := ⟨0, by decide⟩
  ambient := Γ
  valuation := valuation
  close := fun _ var => nomatch var

/-- The recursive position of abstraction congruence is under exactly one
term binder, even when the ambient context is nonempty. -/
def lamCongOccurrence (Γ : Ctx sig)
    (valuation : Valuation (M := metas) (BindingCloneAlgebra.terms sig) Γ) :
    Instance rules (BindingCloneAlgebra.terms sig) where
  index := ⟨3, by decide⟩
  ambient := Γ
  valuation := valuation
  close := fun _ var => nomatch var

/-- Left-application congruence can act in any ambient context. -/
def appCongLOccurrence (Γ : Ctx sig)
    (valuation : Valuation (M := metas) (BindingCloneAlgebra.terms sig) Γ) :
    Instance rules (BindingCloneAlgebra.terms sig) where
  index := ⟨1, by decide⟩
  ambient := Γ
  valuation := valuation
  close := fun _ var => nomatch var

/-- Right-application congruence uses the same ordered step premise. -/
def appCongROccurrence (Γ : Ctx sig)
    (valuation : Valuation (M := metas) (BindingCloneAlgebra.terms sig) Γ) :
    Instance rules (BindingCloneAlgebra.terms sig) where
  index := ⟨2, by decide⟩
  ambient := Γ
  valuation := valuation
  close := fun _ var => nomatch var

theorem lamCongChildContext (Γ : Ctx sig)
    (valuation : Valuation (M := metas) (BindingCloneAlgebra.terms sig) Γ) :
    (childJudgment rules (BindingCloneAlgebra.terms sig)
      (lamCongOccurrence Γ valuation)
        ⟨0, by simp [lamCongOccurrence, rules, lamCong]⟩).1 =
      Srt.term :: Γ := rfl

private def binderIdentityEnvironment (Γ : Ctx sig) :
    Sub sig (Srt.term :: Γ) (Srt.term :: Γ) :=
  SemanticContextualMetavariables.joinEnvironment
    (fun _ var => match var with
      | .zero => Term.var Var.zero
      | .succ old => nomatch old : Sub sig [Srt.term] (Srt.term :: Γ))
    (fun _ var => Term.var (.succ var) : Sub sig Γ (Srt.term :: Γ))

private theorem binderIdentityEnvironment_eq (Γ : Ctx sig) :
    binderIdentityEnvironment Γ = (fun _ var => Term.var var) := by
  funext sort var
  cases var with
  | zero => rfl
  | succ _ => rfl

private theorem binderIdentity_bind (Γ : Ctx sig)
    (body : Term sig (Srt.term :: Γ) Srt.term) :
    bind (binderIdentityEnvironment Γ) body = body := by
  have mid := congrArg (fun env => bind env body)
    (binderIdentityEnvironment_eq Γ)
  exact mid.trans (bind_id body)

private theorem betaLhsShape (Γ : Ctx sig)
    (valuation : Valuation (M := metas) (BindingCloneAlgebra.terms sig) Γ) :
    interpretSchema (BindingCloneAlgebra.terms sig) valuation
        (fun _ var => Term.var var)
        ((fun _ var => nomatch var) : Sub sig [] Γ) betaLeft =
      appT (lamT (bind (binderIdentityEnvironment Γ) (valuation 0)))
        (bind (fun _ var => Term.var var) (valuation 2)) := by
  rfl

private theorem weakenEmptyIdentity (Γ : Ctx sig) :
    weakenEnvironment (BindingCloneAlgebra.terms sig) []
      (fun _ var => Term.var var : Sub sig Γ Γ) =
      (fun _ var => Term.var var) := by
  funext sort var
  rfl

private def emptyClose (Γ : Ctx sig) : Sub sig [] Γ :=
  fun _ var => nomatch var

private theorem firstInterpret (Γ : Ctx sig)
    (valuation : Valuation (M := metas) (BindingCloneAlgebra.terms sig) Γ) :
    interpretSchema (BindingCloneAlgebra.terms sig) valuation
      (fun _ var => Term.var var) (emptyClose Γ) first = valuation 2 := by
  change bind (fun _ var => Term.var var) (valuation 2) = _
  exact bind_id (valuation 2)

private theorem secondInterpret (Γ : Ctx sig)
    (valuation : Valuation (M := metas) (BindingCloneAlgebra.terms sig) Γ) :
    interpretSchema (BindingCloneAlgebra.terms sig) valuation
      (fun _ var => Term.var var) (emptyClose Γ) second = valuation 3 := by
  change bind (fun _ var => Term.var var) (valuation 3) = _
  exact bind_id (valuation 3)

private theorem sharedInterpret (Γ : Ctx sig)
    (valuation : Valuation (M := metas) (BindingCloneAlgebra.terms sig) Γ) :
    interpretSchema (BindingCloneAlgebra.terms sig) valuation
      (fun _ var => Term.var var) (emptyClose Γ) shared = valuation 4 := by
  change bind (fun _ var => Term.var var) (valuation 4) = _
  exact bind_id (valuation 4)

private theorem appInterpret (Γ : Ctx sig)
    (valuation : Valuation (M := metas) (BindingCloneAlgebra.terms sig) Γ)
    (function argument : Term schemaSig [] Srt.term) :
    interpretSchema (BindingCloneAlgebra.terms sig) valuation
        (fun _ var => Term.var var) (emptyClose Γ)
        (schemaApp function argument) =
      appT
        (interpretSchema (BindingCloneAlgebra.terms sig) valuation
          (fun _ var => Term.var var) (emptyClose Γ) function)
        (interpretSchema (BindingCloneAlgebra.terms sig) valuation
          (fun _ var => Term.var var) (emptyClose Γ) argument) := by
  rfl

private theorem betaRhsShape (Γ : Ctx sig)
    (valuation : Valuation (M := metas) (BindingCloneAlgebra.terms sig) Γ) :
    interpretSchema (BindingCloneAlgebra.terms sig) valuation
        (fun _ var => Term.var var)
        ((fun _ var => nomatch var) : Sub sig [] Γ) betaRight =
      bind (extend (bind (fun _ var => Term.var var) (valuation 2)))
        (valuation 0) := by
  change bind
    (joinEnvironment
      ((fun _ var => match var with
        | .zero => bind
            (weakenEnvironment (BindingCloneAlgebra.terms sig) []
              (fun _ var => Term.var var : Sub sig Γ Γ)) (valuation 2)
        | .succ old => nomatch old) : Sub sig [Srt.term] Γ)
      (fun _ var => Term.var var)) (valuation 0) = _
  have envEq :
      joinEnvironment
        ((fun _ var => match var with
          | .zero => bind
              (weakenEnvironment (BindingCloneAlgebra.terms sig) []
                (fun _ var => Term.var var : Sub sig Γ Γ)) (valuation 2)
          | .succ old => nomatch old) : Sub sig [Srt.term] Γ)
        (fun _ var => Term.var var) =
      extend (bind (fun _ var => Term.var var) (valuation 2)) := by
    funext sort var
    cases var with
    | zero =>
        exact congrArg
          (fun env => bind env (valuation 2))
          (weakenEmptyIdentity Γ)
    | succ _ => rfl
  exact congrArg (fun env => bind env (valuation 0)) envEq

theorem betaConclusion (Γ : Ctx sig)
    (valuation : Valuation (M := metas) (BindingCloneAlgebra.terms sig) Γ) :
    conclusionJudgment rules (BindingCloneAlgebra.terms sig)
        (betaOccurrence Γ valuation) =
      (⟨Γ, Srt.term,
        appT (lamT (valuation 0)) (valuation 2),
        inst (valuation 0) (valuation 2)⟩ :
        Judgment (BindingCloneAlgebra.terms sig)) := by
  change (⟨Γ, Srt.term,
    interpretSchema (BindingCloneAlgebra.terms sig) valuation
      (fun _ var => Term.var var)
      ((fun _ var => nomatch var) : Sub sig [] Γ) betaLeft,
    interpretSchema (BindingCloneAlgebra.terms sig) valuation
      (fun _ var => Term.var var)
      ((fun _ var => nomatch var) : Sub sig [] Γ) betaRight⟩ :
      Judgment (BindingCloneAlgebra.terms sig)) = _
  have bodyEq :
      bind (binderIdentityEnvironment Γ) (valuation 0) = valuation 0 := by
    have mid : bind (binderIdentityEnvironment Γ) (valuation 0) =
        bind (fun _ var => Term.var var) (valuation 0) :=
      congrArg (fun env => bind env (valuation 0))
        (binderIdentityEnvironment_eq Γ)
    exact mid.trans (bind_id (valuation 0))
  have argEq :
      bind (fun _ var => Term.var var) (valuation 2) = valuation 2 :=
    bind_id (valuation 2)
  have lhsEq :
      appT (lamT (bind (binderIdentityEnvironment Γ) (valuation 0)))
          (bind (fun _ var => Term.var var) (valuation 2)) =
        appT (lamT (valuation 0)) (valuation 2) :=
    congrArg₂ appT (congrArg lamT bodyEq) argEq
  have rhsEq :
      bind (extend (bind (fun _ var => Term.var var) (valuation 2)))
          (valuation 0) = inst (valuation 0) (valuation 2) := by
    change bind (extend (bind (fun _ var => Term.var var) (valuation 2)))
      (valuation 0) = bind (extend (valuation 2)) (valuation 0)
    exact congrArg (fun t => bind (extend t) (valuation 0)) argEq
  exact congrArg₂ (fun l r =>
    (⟨Γ, Srt.term, l, r⟩ : Judgment (BindingCloneAlgebra.terms sig)))
      ((betaLhsShape Γ valuation).trans lhsEq)
      ((betaRhsShape Γ valuation).trans rhsEq)

/-- The recursive LamCong judgment contains the original arbitrary bodies,
without discarding their dependencies on the enclosing ambient context. -/
theorem lamCongChild (Γ : Ctx sig)
    (valuation : Valuation (M := metas) (BindingCloneAlgebra.terms sig) Γ) :
    childJudgment rules (BindingCloneAlgebra.terms sig)
      (lamCongOccurrence Γ valuation)
        ⟨0, by simp [lamCongOccurrence, rules, lamCong]⟩ =
      (⟨Srt.term :: Γ, Srt.term, valuation 0, valuation 1⟩ :
        Judgment (BindingCloneAlgebra.terms sig)) := by
  change (⟨Srt.term :: Γ, Srt.term,
      bind (binderIdentityEnvironment Γ) (valuation 0),
      bind (binderIdentityEnvironment Γ) (valuation 1)⟩ :
        Judgment (BindingCloneAlgebra.terms sig)) = _
  exact congrArg₂ (fun l r =>
    (⟨Srt.term :: Γ, Srt.term, l, r⟩ :
      Judgment (BindingCloneAlgebra.terms sig)))
    (binderIdentity_bind Γ (valuation 0))
    (binderIdentity_bind Γ (valuation 1))

/-- The LamCong root wraps precisely its binder-local child endpoints. -/
theorem lamCongConclusion (Γ : Ctx sig)
    (valuation : Valuation (M := metas) (BindingCloneAlgebra.terms sig) Γ) :
    conclusionJudgment rules (BindingCloneAlgebra.terms sig)
        (lamCongOccurrence Γ valuation) =
      (⟨Γ, Srt.term, lamT (valuation 0), lamT (valuation 1)⟩ :
        Judgment (BindingCloneAlgebra.terms sig)) := by
  change (⟨Γ, Srt.term,
      lamT (bind (binderIdentityEnvironment Γ) (valuation 0)),
      lamT (bind (binderIdentityEnvironment Γ) (valuation 1))⟩ :
        Judgment (BindingCloneAlgebra.terms sig)) = _
  exact congrArg₂ (fun l r =>
    (⟨Γ, Srt.term, lamT l, lamT r⟩ :
      Judgment (BindingCloneAlgebra.terms sig)))
    (binderIdentity_bind Γ (valuation 0))
    (binderIdentity_bind Γ (valuation 1))

/-- Both application congruence rules ask for exactly the same root-local
child judgment; their enclosing function/argument positions differ. -/
theorem appCongLChild (Γ : Ctx sig)
    (valuation : Valuation (M := metas) (BindingCloneAlgebra.terms sig) Γ) :
    childJudgment rules (BindingCloneAlgebra.terms sig)
      (appCongLOccurrence Γ valuation)
        ⟨0, by simp [appCongLOccurrence, rules, appCongL]⟩ =
      (⟨Γ, Srt.term, valuation 2, valuation 3⟩ :
        Judgment (BindingCloneAlgebra.terms sig)) := by
  change (⟨Γ, Srt.term,
    interpretSchema (BindingCloneAlgebra.terms sig) valuation
      (fun _ var => Term.var var) (emptyClose Γ) first,
    interpretSchema (BindingCloneAlgebra.terms sig) valuation
      (fun _ var => Term.var var) (emptyClose Γ) second⟩ :
      Judgment (BindingCloneAlgebra.terms sig)) = _
  exact congrArg₂ (fun l r =>
    (⟨Γ, Srt.term, l, r⟩ : Judgment (BindingCloneAlgebra.terms sig)))
    (firstInterpret Γ valuation) (secondInterpret Γ valuation)

theorem appCongRChild (Γ : Ctx sig)
    (valuation : Valuation (M := metas) (BindingCloneAlgebra.terms sig) Γ) :
    childJudgment rules (BindingCloneAlgebra.terms sig)
      (appCongROccurrence Γ valuation)
        ⟨0, by simp [appCongROccurrence, rules, appCongR]⟩ =
      (⟨Γ, Srt.term, valuation 2, valuation 3⟩ :
        Judgment (BindingCloneAlgebra.terms sig)) := by
  change (⟨Γ, Srt.term,
    interpretSchema (BindingCloneAlgebra.terms sig) valuation
      (fun _ var => Term.var var) (emptyClose Γ) first,
    interpretSchema (BindingCloneAlgebra.terms sig) valuation
      (fun _ var => Term.var var) (emptyClose Γ) second⟩ :
      Judgment (BindingCloneAlgebra.terms sig)) = _
  exact congrArg₂ (fun l r =>
    (⟨Γ, Srt.term, l, r⟩ : Judgment (BindingCloneAlgebra.terms sig)))
    (firstInterpret Γ valuation) (secondInterpret Γ valuation)

theorem appCongLConclusion (Γ : Ctx sig)
    (valuation : Valuation (M := metas) (BindingCloneAlgebra.terms sig) Γ) :
    conclusionJudgment rules (BindingCloneAlgebra.terms sig)
        (appCongLOccurrence Γ valuation) =
      (⟨Γ, Srt.term,
        appT (valuation 2) (valuation 4),
        appT (valuation 3) (valuation 4)⟩ :
        Judgment (BindingCloneAlgebra.terms sig)) := by
  change (⟨Γ, Srt.term,
    interpretSchema (BindingCloneAlgebra.terms sig) valuation
      (fun _ var => Term.var var) (emptyClose Γ) appCongLLeft,
    interpretSchema (BindingCloneAlgebra.terms sig) valuation
      (fun _ var => Term.var var) (emptyClose Γ) appCongLRight⟩ :
      Judgment (BindingCloneAlgebra.terms sig)) = _
  have leftEq := (appInterpret Γ valuation first shared).trans
    (congrArg₂ appT (firstInterpret Γ valuation)
      (sharedInterpret Γ valuation))
  have rightEq := (appInterpret Γ valuation second shared).trans
    (congrArg₂ appT (secondInterpret Γ valuation)
      (sharedInterpret Γ valuation))
  exact congrArg₂ (fun l r =>
    (⟨Γ, Srt.term, l, r⟩ : Judgment (BindingCloneAlgebra.terms sig)))
    leftEq rightEq

theorem appCongRConclusion (Γ : Ctx sig)
    (valuation : Valuation (M := metas) (BindingCloneAlgebra.terms sig) Γ) :
    conclusionJudgment rules (BindingCloneAlgebra.terms sig)
        (appCongROccurrence Γ valuation) =
      (⟨Γ, Srt.term,
        appT (valuation 4) (valuation 2),
        appT (valuation 4) (valuation 3)⟩ :
        Judgment (BindingCloneAlgebra.terms sig)) := by
  change (⟨Γ, Srt.term,
    interpretSchema (BindingCloneAlgebra.terms sig) valuation
      (fun _ var => Term.var var) (emptyClose Γ) appCongRLeft,
    interpretSchema (BindingCloneAlgebra.terms sig) valuation
      (fun _ var => Term.var var) (emptyClose Γ) appCongRRight⟩ :
      Judgment (BindingCloneAlgebra.terms sig)) = _
  have leftEq := (appInterpret Γ valuation shared first).trans
    (congrArg₂ appT (sharedInterpret Γ valuation)
      (firstInterpret Γ valuation))
  have rightEq := (appInterpret Γ valuation shared second).trans
    (congrArg₂ appT (sharedInterpret Γ valuation)
      (secondInterpret Γ valuation))
  exact congrArg₂ (fun l r =>
    (⟨Γ, Srt.term, l, r⟩ : Judgment (BindingCloneAlgebra.terms sig)))
    leftEq rightEq

/-- Every constructor of the shared presentation is one of the four
explicitly interpreted contextual lambda rules. -/
theorem occurrence_cases
    (occurrence : Instance rules (BindingCloneAlgebra.terms sig)) :
    occurrence = betaOccurrence occurrence.ambient occurrence.valuation ∨
    occurrence = appCongLOccurrence occurrence.ambient occurrence.valuation ∨
    occurrence = appCongROccurrence occurrence.ambient occurrence.valuation ∨
    occurrence = lamCongOccurrence occurrence.ambient occurrence.valuation := by
  rcases occurrence with ⟨index, Γ, valuation, close⟩
  rcases index with ⟨index, bound⟩
  have small : index < 4 := by
    simpa [rules] using bound
  interval_cases index
  · left
    have hclose : close = emptyClose Γ := by
      funext sort var
      nomatch var
    cases hclose
    have hindex : (⟨0, bound⟩ : Fin rules.length) = ⟨0, by decide⟩ :=
      Fin.ext rfl
    cases hindex
    congr 1
    funext sort var
    nomatch var

  · right; left
    have hclose : close = emptyClose Γ := by
      funext sort var
      nomatch var
    cases hclose
    have hindex : (⟨1, bound⟩ : Fin rules.length) = ⟨1, by decide⟩ :=
      Fin.ext rfl
    cases hindex
    congr 1
    funext sort var
    nomatch var
  · right; right; left
    have hclose : close = emptyClose Γ := by
      funext sort var
      nomatch var
    cases hclose
    have hindex : (⟨2, bound⟩ : Fin rules.length) = ⟨2, by decide⟩ :=
      Fin.ext rfl
    cases hindex
    congr 1
    funext sort var
    nomatch var
  · right; right; right
    have hclose : close = emptyClose Γ := by
      funext sort var
      nomatch var
    cases hclose
    have hindex : (⟨3, bound⟩ : Fin rules.length) = ⟨3, by decide⟩ :=
      Fin.ext rfl
    cases hindex
    congr 1
    funext sort var
    nomatch var

/-- The intrinsic rule image is tested against the existing least contextual
lambda reduction, with the ambient context retained in each judgment. -/
def sourceStep : Judgment (BindingCloneAlgebra.terms sig) → Prop
  | ⟨Γ, Srt.term, source, target⟩ =>
      LambdaContextualRung.Step Γ source target

theorem sourceStep_ruleClosed :
    RuleClosed rules sourceStep := by
  intro occurrence children
  rcases occurrence_cases occurrence with h | h | h | h
  · rw [h] at children ⊢
    have step : sourceStep
        (⟨occurrence.ambient, Srt.term,
          appT (lamT (occurrence.valuation 0)) (occurrence.valuation 2),
          inst (occurrence.valuation 0) (occurrence.valuation 2)⟩ :
          Judgment (BindingCloneAlgebra.terms sig)) :=
      LambdaContextualRung.Step.beta _ _
    exact (congrArg sourceStep
      (betaConclusion occurrence.ambient occurrence.valuation)).symm ▸ step
  · rw [h] at children ⊢
    have premise : LambdaContextualRung.Step occurrence.ambient
        (occurrence.valuation 2) (occurrence.valuation 3) :=
      (congrArg sourceStep
        (appCongLChild occurrence.ambient occurrence.valuation)).mp
          (children ⟨0, by simp [appCongLOccurrence, rules, appCongL]⟩)
    have step : sourceStep
        (⟨occurrence.ambient, Srt.term,
          appT (occurrence.valuation 2) (occurrence.valuation 4),
          appT (occurrence.valuation 3) (occurrence.valuation 4)⟩ :
          Judgment (BindingCloneAlgebra.terms sig)) :=
      .appCongL (occurrence.valuation 4) premise
    exact (congrArg sourceStep
      (appCongLConclusion occurrence.ambient occurrence.valuation)).symm ▸ step
  · rw [h] at children ⊢
    have premise : LambdaContextualRung.Step occurrence.ambient
        (occurrence.valuation 2) (occurrence.valuation 3) :=
      (congrArg sourceStep
        (appCongRChild occurrence.ambient occurrence.valuation)).mp
          (children ⟨0, by simp [appCongROccurrence, rules, appCongR]⟩)
    have step : sourceStep
        (⟨occurrence.ambient, Srt.term,
          appT (occurrence.valuation 4) (occurrence.valuation 2),
          appT (occurrence.valuation 4) (occurrence.valuation 3)⟩ :
          Judgment (BindingCloneAlgebra.terms sig)) :=
      .appCongR (occurrence.valuation 4) premise
    exact (congrArg sourceStep
      (appCongRConclusion occurrence.ambient occurrence.valuation)).symm ▸ step
  · rw [h] at children ⊢
    have premise : LambdaContextualRung.Step (Srt.term :: occurrence.ambient)
        (occurrence.valuation 0) (occurrence.valuation 1) :=
      (congrArg sourceStep
        (lamCongChild occurrence.ambient occurrence.valuation)).mp
          (children ⟨0, by simp [lamCongOccurrence, rules, lamCong]⟩)
    have step : sourceStep
        (⟨occurrence.ambient, Srt.term,
          lamT (occurrence.valuation 0),
          lamT (occurrence.valuation 1)⟩ :
          Judgment (BindingCloneAlgebra.terms sig)) :=
      .lamCong premise
    exact (congrArg sourceStep
      (lamCongConclusion occurrence.ambient occurrence.valuation)).symm ▸ step

/-- Every firing tree of the one authored four-rule presentation denotes an
actual step of the context-indexed lambda calculus. -/
theorem reduces_to_sourceStep {Γ : Ctx sig}
    {source target : Term sig Γ Srt.term}
    (step : Reduces rules
      (⟨Γ, Srt.term, source, target⟩ :
        Judgment (BindingCloneAlgebra.terms sig))) :
    LambdaContextualRung.Step Γ source target :=
  reduces_least rules sourceStep sourceStep_ruleClosed _ step

private def defaultTerm (Γ : Ctx sig) : Term sig Γ Srt.term :=
  lamT (.var .zero)

/-- Any open beta redex is a firing of the first intrinsic constructor. -/
theorem betaReduces (Γ : Ctx sig)
    (body : Term sig (Srt.term :: Γ) Srt.term)
    (argument : Term sig Γ Srt.term) :
    Reduces rules
      (⟨Γ, Srt.term,
        appT (lamT body) argument, inst body argument⟩ :
        Judgment (BindingCloneAlgebra.terms sig)) := by
  let valuation := valuationOf Γ body body argument argument argument
  have base : Reduces rules
      (conclusionJudgment rules (BindingCloneAlgebra.terms sig)
        (betaOccurrence Γ valuation)) :=
    reduces_ruleClosed rules (betaOccurrence Γ valuation)
      (by intro position; nomatch position)
  exact (congrArg (Reduces rules) (betaConclusion Γ valuation)).mp base

theorem appCongLReduces (Γ : Ctx sig)
    (source target argument : Term sig Γ Srt.term)
    (child : Reduces rules
      (⟨Γ, Srt.term, source, target⟩ :
        Judgment (BindingCloneAlgebra.terms sig))) :
    Reduces rules
      (⟨Γ, Srt.term, appT source argument,
        appT target argument⟩ :
        Judgment (BindingCloneAlgebra.terms sig)) := by
  let valuation := valuationOf Γ (.var .zero) (.var .zero)
    source target argument
  have children :
      ∀ position : Fin
          (rules.get (appCongLOccurrence Γ valuation).index).premises.length,
        Reduces rules (childJudgment rules (BindingCloneAlgebra.terms sig)
          (appCongLOccurrence Γ valuation) position) := by
    intro position
    have atZero : position =
        ⟨0, by simp [appCongLOccurrence, rules, appCongL]⟩ := by
      apply Fin.ext
      change position.val = 0
      have bounded : position.val < 1 := by
        simpa [appCongLOccurrence, rules, appCongL] using position.isLt
      omega
    subst position
    exact (congrArg (Reduces rules)
      (appCongLChild Γ valuation)).mpr child
  have base := reduces_ruleClosed rules (appCongLOccurrence Γ valuation) children
  exact (congrArg (Reduces rules)
    (appCongLConclusion Γ valuation)).mp base

theorem appCongRReduces (Γ : Ctx sig)
    (function source target : Term sig Γ Srt.term)
    (child : Reduces rules
      (⟨Γ, Srt.term, source, target⟩ :
        Judgment (BindingCloneAlgebra.terms sig))) :
    Reduces rules
      (⟨Γ, Srt.term, appT function source,
        appT function target⟩ :
        Judgment (BindingCloneAlgebra.terms sig)) := by
  let valuation := valuationOf Γ (.var .zero) (.var .zero)
    source target function
  have children :
      ∀ position : Fin
          (rules.get (appCongROccurrence Γ valuation).index).premises.length,
        Reduces rules (childJudgment rules (BindingCloneAlgebra.terms sig)
          (appCongROccurrence Γ valuation) position) := by
    intro position
    have atZero : position =
        ⟨0, by simp [appCongROccurrence, rules, appCongR]⟩ := by
      apply Fin.ext
      change position.val = 0
      have bounded : position.val < 1 := by
        simpa [appCongROccurrence, rules, appCongR] using position.isLt
      omega
    subst position
    exact (congrArg (Reduces rules)
      (appCongRChild Γ valuation)).mpr child
  have base := reduces_ruleClosed rules (appCongROccurrence Γ valuation) children
  exact (congrArg (Reduces rules)
    (appCongRConclusion Γ valuation)).mp base

theorem lamCongReduces (Γ : Ctx sig)
    (source target : Term sig (Srt.term :: Γ) Srt.term)
    (child : Reduces rules
      (⟨Srt.term :: Γ, Srt.term, source, target⟩ :
        Judgment (BindingCloneAlgebra.terms sig))) :
    Reduces rules
      (⟨Γ, Srt.term, lamT source, lamT target⟩ :
        Judgment (BindingCloneAlgebra.terms sig)) := by
  let dummy := defaultTerm Γ
  let valuation := valuationOf Γ source target dummy dummy dummy
  have children :
      ∀ position : Fin
          (rules.get (lamCongOccurrence Γ valuation).index).premises.length,
        Reduces rules (childJudgment rules (BindingCloneAlgebra.terms sig)
          (lamCongOccurrence Γ valuation) position) := by
    intro position
    have atZero : position =
        ⟨0, by simp [lamCongOccurrence, rules, lamCong]⟩ := by
      apply Fin.ext
      change position.val = 0
      have bounded : position.val < 1 := by
        simpa [lamCongOccurrence, rules, lamCong] using position.isLt
      omega
    subst position
    exact (congrArg (Reduces rules)
      (lamCongChild Γ valuation)).mpr child
  have base := reduces_ruleClosed rules (lamCongOccurrence Γ valuation) children
  exact (congrArg (Reduces rules)
    (lamCongConclusion Γ valuation)).mp base

/-- Conversely, each contextual lambda step has a firing tree in the single
intrinsic rule presentation. The induction follows the four actual rules. -/
theorem sourceStep_to_reduces {Γ : Ctx sig}
    {source target : Term sig Γ Srt.term}
    (step : LambdaContextualRung.Step Γ source target) :
    Reduces rules
      (⟨Γ, Srt.term, source, target⟩ :
        Judgment (BindingCloneAlgebra.terms sig)) := by
  induction step with
  | beta body argument =>
      exact betaReduces _ body argument
  | appCongL argument _step ih =>
      exact appCongLReduces _ _ _ argument ih
  | appCongR function _step ih =>
      exact appCongRReduces _ function _ _ ih
  | lamCong _step ih =>
      exact lamCongReduces _ _ _ ih

/-- The event image of one shared, substitution-compatible rule algebra is
exactly the Chapter 7 least four-rule contextual lambda relation. -/
theorem sourceStep_iff_reduces {Γ : Ctx sig}
    {source target : Term sig Γ Srt.term} :
    LambdaContextualRung.Step Γ source target ↔
      Reduces rules
        (⟨Γ, Srt.term, source, target⟩ :
          Judgment (BindingCloneAlgebra.terms sig)) :=
  ⟨sourceStep_to_reduces, reduces_to_sourceStep⟩

/-- The finite authored list and the earlier semantic four-shape polynomial
have the same event-image relation over the free binding clone. -/
theorem intrinsic_iff_semanticRuleTree {Γ : Ctx sig}
    {source target : Term sig Γ Srt.term} :
    Reduces rules
        (⟨Γ, Srt.term, source, target⟩ :
          Judgment (BindingCloneAlgebra.terms sig)) ↔
      Nonempty
        ((Mettapedia.OSLF.Binding.LambdaSemanticRulePolynomial.rules
          (BindingCloneAlgebra.terms sig)).Fix ()
          (Mettapedia.OSLF.Binding.LambdaSemanticRulePolynomial.judgment
            (BindingCloneAlgebra.terms sig) source target)) :=
  sourceStep_iff_reduces.symm.trans
    Mettapedia.OSLF.Binding.LambdaSemanticRulePolynomial.sourceStep_iff_semanticTree

/-- A bare variable cannot fire in the four-rule presentation. The negative
control excludes an accidental reflexive or unrestricted rewrite rule. -/
theorem variable_has_no_intrinsic_firing {Γ : Ctx sig}
    (x : Var Γ Srt.term) {target : Term sig Γ Srt.term} :
    ¬ Reduces rules
      (⟨Γ, Srt.term, Term.var x, target⟩ :
        Judgment (BindingCloneAlgebra.terms sig)) := by
  intro firing
  exact Mettapedia.OSLF.Binding.LambdaSemanticRulePolynomial.variable_has_no_semantic_tree
    x ((intrinsic_iff_semanticRuleTree).mp firing)


/-- The full authored profile retains the earlier LamCong declaration, and
its one-rule application uses the same scoped-premise semantics. -/
private theorem fullLamCongApplication_eq_twoRule
    (oracle : Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.StepOracle
      Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.RuleHistory)
    (ambient : Nat) (input : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.applyRuleWithOracle
      oracle Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty
      Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.language ambient
      Mettapedia.GSLT.Examples.ScopedLamCongExecution.lamCongRule input =
    Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.applyRuleWithOracle
      oracle Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty
      Mettapedia.GSLT.Examples.ScopedLamCongExecution.language ambient
      Mettapedia.GSLT.Examples.ScopedLamCongExecution.lamCongRule input := by
  rfl

/-- The full four-rule authored executor really performs a beta step beneath
LamCong, retaining the selected inner firing in its history. -/
theorem fullLamCong_runtime {Γ : Ctx sig}
    (inner : Term sig (Srt.term :: Srt.term :: Γ) Srt.term)
    (argument : Term sig (Srt.term :: Γ) Srt.term) :
    (Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.RuleHistory.fire 1
        [.step 0 0 (.fire 0 [])],
      Mettapedia.OSLF.Binding.LambdaScopedAuthoringComparison.encodeTerm
        (lamT (inst inner argument))) ∈
      Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.rewriteAt
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty
        Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.language
        2 Γ.length
        (Mettapedia.OSLF.Binding.LambdaScopedAuthoringComparison.encodeTerm
          (lamT (appT (lamT inner) argument))) := by
  have oracleResult :=
    Mettapedia.OSLF.Binding.LambdaAuthoredAppCongExecutionComparison.full_beta_one_step
      inner argument
  have oracleResult' :
      Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.rewriteAt
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty
        Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.language
        1 (1 + Γ.length)
        (Mettapedia.OSLF.Binding.LambdaScopedAuthoringComparison.encodeTerm
          (appT (lamT inner) argument)) =
      [(.fire 0 [],
        Mettapedia.OSLF.Binding.LambdaScopedAuthoringComparison.encodeTerm
          (inst inner argument))] := by
    change Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.rewriteAt
      Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty
      Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.language
      1 (Γ.length + 1)
      (Mettapedia.OSLF.Binding.LambdaScopedAuthoringComparison.encodeTerm
        (appT (lamT inner) argument)) =
      [(.fire 0 [],
        Mettapedia.OSLF.Binding.LambdaScopedAuthoringComparison.encodeTerm
          (inst inner argument))] at oracleResult
    simpa only [Nat.add_comm] using oracleResult
  have firesTwo :=
    Mettapedia.OSLF.Binding.LambdaAuthoredLamCongExecutionComparison.authored_lamCong_executes_intrinsic
      (Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.rewriteAt
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty
        Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.language 1)
      (appT (lamT inner) argument) (inst inner argument)
      (.fire 0 []) oracleResult'
  have firesFull :=
    (fullLamCongApplication_eq_twoRule
      (Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.rewriteAt
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty
        Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.language 1)
      Γ.length
      (Mettapedia.OSLF.Binding.LambdaScopedAuthoringComparison.encodeTerm
        (lamT (appT (lamT inner) argument)))).trans firesTwo
  apply (Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.mem_rewriteAt_succ_iff
    Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty
    Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.language
    1 Γ.length _ _ _).2
  refine ⟨Mettapedia.GSLT.Examples.ScopedLamCongExecution.lamCongRule,
    1, ?_, ?_⟩
  · simp [Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.language]
  · simp [firesFull]

/-- An arbitrary authored beta firing and its intrinsic event have the same
open endpoints, with the actual executor retaining its rule index. -/
theorem authoredBeta_matches_intrinsic {Γ : Ctx sig}
    (body : Term sig (Srt.term :: Γ) Srt.term)
    (argument : Term sig Γ Srt.term) :
    ((.fire 0 [],
      Mettapedia.OSLF.Binding.LambdaScopedAuthoringComparison.encodeTerm
        (inst body argument)) ∈
      Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.rewriteAt
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty
        Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.language
        1 Γ.length
        (Mettapedia.OSLF.Binding.LambdaScopedAuthoringComparison.encodeTerm
          (appT (lamT body) argument))) ∧
      Reduces rules
        (⟨Γ, Srt.term, appT (lamT body) argument,
          inst body argument⟩ :
          Judgment (BindingCloneAlgebra.terms sig)) := by
  constructor
  · rw [Mettapedia.OSLF.Binding.LambdaAuthoredAppCongExecutionComparison.full_beta_one_step
      body argument]
    exact List.mem_singleton.mpr rfl
  · exact betaReduces Γ body argument

/-- The authored left-application history and the intrinsic congruence tree
select the same beta child, at every ambient context. -/
theorem authoredAppCongL_matches_intrinsic {Γ : Ctx sig}
    (body : Term sig (Srt.term :: Γ) Srt.term)
    (argument outer : Term sig Γ Srt.term) :
    ((.fire 2 [.step 0 0 (.fire 0 [])],
      Mettapedia.OSLF.Binding.LambdaScopedAuthoringComparison.encodeTerm
        (appT (inst body argument) outer)) ∈
      Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.rewriteAt
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty
        Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.language
        2 Γ.length
        (Mettapedia.OSLF.Binding.LambdaScopedAuthoringComparison.encodeTerm
          (appT (appT (lamT body) argument) outer))) ∧
      Reduces rules
        (⟨Γ, Srt.term,
          appT (appT (lamT body) argument) outer,
          appT (inst body argument) outer⟩ :
          Judgment (BindingCloneAlgebra.terms sig)) := by
  exact ⟨Mettapedia.OSLF.Binding.LambdaAuthoredAppCongExecutionComparison.beta_under_appL
      body argument outer,
    appCongLReduces Γ _ _ outer (betaReduces Γ body argument)⟩

/-- The right-application history uses a different authored rule index and a
different intrinsic constructor from left congruence. -/
theorem authoredAppCongR_matches_intrinsic {Γ : Ctx sig}
    (body : Term sig (Srt.term :: Γ) Srt.term)
    (argument outer : Term sig Γ Srt.term) :
    ((.fire 3 [.step 0 0 (.fire 0 [])],
      Mettapedia.OSLF.Binding.LambdaScopedAuthoringComparison.encodeTerm
        (appT outer (inst body argument))) ∈
      Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.rewriteAt
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty
        Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.language
        2 Γ.length
        (Mettapedia.OSLF.Binding.LambdaScopedAuthoringComparison.encodeTerm
          (appT outer (appT (lamT body) argument)))) ∧
      Reduces rules
        (⟨Γ, Srt.term,
          appT outer (appT (lamT body) argument),
          appT outer (inst body argument)⟩ :
          Judgment (BindingCloneAlgebra.terms sig)) := by
  exact ⟨Mettapedia.OSLF.Binding.LambdaAuthoredAppCongExecutionComparison.beta_under_appR
      body argument outer,
    appCongRReduces Γ outer _ _ (betaReduces Γ body argument)⟩

/-- The full authored four-rule language executes a binder-local LamCong
premise whose endpoints have the intrinsic firing tree. -/
theorem authoredLamCong_matches_intrinsic {Γ : Ctx sig}
    (inner : Term sig (Srt.term :: Srt.term :: Γ) Srt.term)
    (argument : Term sig (Srt.term :: Γ) Srt.term) :
    ((.fire 1 [.step 0 0 (.fire 0 [])],
      Mettapedia.OSLF.Binding.LambdaScopedAuthoringComparison.encodeTerm
        (lamT (inst inner argument))) ∈
      Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.rewriteAt
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty
        Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.language
        2 Γ.length
        (Mettapedia.OSLF.Binding.LambdaScopedAuthoringComparison.encodeTerm
          (lamT (appT (lamT inner) argument)))) ∧
      Reduces rules
        (⟨Γ, Srt.term,
          lamT (appT (lamT inner) argument),
          lamT (inst inner argument)⟩ :
          Judgment (BindingCloneAlgebra.terms sig)) := by
  exact ⟨fullLamCong_runtime inner argument,
    lamCongReduces Γ _ _ (betaReduces _ inner argument)⟩
/-- The combined equation-free lambda theory and all four proof-relevant
rule actions have the general initial substitution-operational model. -/
noncomputable def initial :
    IsInitial (SubstitutionOperationalModel.presented rules
      ([] : List (EqAxiom sig metas))) :=
  SubstitutionOperationalModel.presentedIsInitial rules []

#print axioms rule_inventory
#print axioms sourceStep_iff_reduces
#print axioms intrinsic_iff_semanticRuleTree
#print axioms variable_has_no_intrinsic_firing
#print axioms fullLamCong_runtime
#print axioms authoredBeta_matches_intrinsic
#print axioms authoredAppCongL_matches_intrinsic
#print axioms authoredAppCongR_matches_intrinsic
#print axioms authoredLamCong_matches_intrinsic
#print axioms initial

end Mettapedia.OSLF.Binding.IntrinsicLambdaFourRulePresentation
