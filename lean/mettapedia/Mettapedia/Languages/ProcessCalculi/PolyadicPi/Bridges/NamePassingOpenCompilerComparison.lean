import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOpenSubstitution
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambda
import Mettapedia.OSLF.Syntax.SignatureMorphism

/-!
# Comparison with the executable reference-only compiler

The independently formed open interpretation restricts to the existing five
compiler clauses. The comparison permits any supplied program-variable
bodies: the reference-only expression fragment never reads those bodies.
Both sort positions and all fresh and received names are retained.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOpenInterpretation

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi

/-- The ordinary term sort is sent to the target process sort only for this
comparison of variable positions; its general continuation interpretation
remains a name-indexed process value. -/
def positionSort : NamePassing.Presentation.Srt → Srt
  | .nm => .nm
  | .tm => .pr

def compilerExpression : {Γ : Ctx NamePassing.Presentation.signature} →
    NamePassing.Expr NamePassing.Presentation.Srt.nm Γ →
      NamePassingLambda.Expr (Γ.map positionSort)
  | _, .var name => .var (mapVar positionSort _ name)
  | _, .lam body => .lam (compilerExpression body)
  | _, .app function argument => .app (compilerExpression function) (mapVar positionSort _ argument)
  | _, .defn value body => .defn (compilerExpression value) (compilerExpression body)
  | _, .carrier name value body =>
      .carrier (mapVar positionSort _ name) (compilerExpression value) (compilerExpression body)

/-- Primitive name assignments suffice for the comparison. No equality of
complete translations or operational behavior is assumed. -/
theorem embedded_compiler {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (term : NamePassing.Expr NamePassing.Presentation.Srt.nm Γ)
    (environment : Environment Γ Δ) (names : Ren sig (Γ.map positionSort) Δ)
    (result : Var Δ .nm)
    (compatible : ∀ name, environment.name name = .var (names _ (mapVar positionSort _ name))) :
    interpret (NamePassing.Presentation.embed term) environment (.var result) =
      NamePassingLambda.compile (compilerExpression term) names result := by
  induction term generalizing Δ with
  | var name =>
      simp only [NamePassing.Presentation.embed, NamePassing.Presentation.reference, interpret,
        interpretName, NamePassing.Presentation.nameVariable, compilerExpression, NamePassingLambda.compile]
      rw [compatible]
  | lam body inductionHypothesis =>
      simp only [NamePassing.Presentation.embed, NamePassing.Presentation.abstraction,
        interpret, compilerExpression, NamePassingLambda.compile]
      apply congrArg (inp2 (.var result))
      apply inductionHypothesis
      intro name
      cases name with
      | zero => rfl
      | succ name =>
          change weaken (Mettapedia.OSLF.Binding.bind weakening (environment.name name)) =
            .var (.succ (.succ (names _ (mapVar positionSort _ name))))
          rw [compatible]
          rfl
  | app function argument inductionHypothesis =>
      simp only [NamePassing.Presentation.embed, NamePassing.Presentation.application,
        interpret, compilerExpression, NamePassingLambda.compile]
      have shifted : ∀ name, (environment.substitute weakening).name name =
          .var (NamePassingLambda.push names _ (mapVar positionSort _ name)) := by
        intro name
        change Mettapedia.OSLF.Binding.bind weakening (environment.name name) = _
        rw [compatible]
        rfl
      rw [inductionHypothesis _ _ _ shifted]
      change nu (par _ (out2 (.var .zero) (weaken (environment.name argument)) _)) = _
      rw [compatible]
      rfl
  | defn value body valueHypothesis bodyHypothesis =>
      simp only [NamePassing.Presentation.embed, NamePassing.Presentation.definition,
        interpret, compilerExpression, NamePassingLambda.compile]
      have lifted : ∀ name, environment.lift.name name =
          .var (liftRen names [.nm] _ (mapVar positionSort _ name)) := by
        intro name
        cases name with
        | zero => rfl
        | succ name =>
            change weaken (environment.name name) = .var (.succ (names _ (mapVar positionSort _ name)))
            rw [compatible]
            rfl
      have shifted : ∀ name, ((environment.substitute weakening).substitute weakening).name name =
          .var (NamePassingLambda.push (NamePassingLambda.push names) _ (mapVar positionSort _ name)) := by
        intro name
        change Mettapedia.OSLF.Binding.bind weakening
          (Mettapedia.OSLF.Binding.bind weakening (environment.name name)) = _
        rw [compatible]
        rfl
      exact congrArg nu (congrArg₂ par
        (bodyHypothesis environment.lift (liftRen names [.nm]) (.succ result) lifted)
        (congrArg rep (congrArg (inp1 (.var .zero))
          (valueHypothesis ((environment.substitute weakening).substitute weakening)
            (NamePassingLambda.push (NamePassingLambda.push names)) .zero shifted))))
  | carrier name value body valueHypothesis bodyHypothesis =>
      simp only [NamePassing.Presentation.embed, NamePassing.Presentation.carrier,
        interpret, compilerExpression, NamePassingLambda.compile]
      have shifted : ∀ name, (environment.substitute weakening).name name =
          .var (NamePassingLambda.push names _ (mapVar positionSort _ name)) := by
        intro name
        change Mettapedia.OSLF.Binding.bind weakening (environment.name name) = _
        rw [compatible]
        rfl
      rw [bodyHypothesis environment names result compatible, valueHypothesis _ _ _ shifted]
      change par _ (inp1 (environment.name name) _) = _
      rw [compatible]

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOpenInterpretation
