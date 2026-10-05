import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBinaryReadback
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingUnaryReadback
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentEquations

/-!
# Full active compiler-image readback for name-passing lambda

Every actual equation-saturated target communication from the entire compiler
image has a genuine source beta or fetch event. Its supplied endpoint is the
compiled source successor modulo the authored equations. The source authority
is the independently authored environment calculus and application scope laws.
Injective reference renaming prevents distinct source references from becoming
the same target channel. No target execution or static representative is
restricted to a canonical scheduler or a selected forward implementation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCompilerReadback

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open NamePassingLambda ScopedCommunicationInversion ActiveHeaderInvariant

private theorem communication_arity {Γ : Ctx sig} {redex reduct : Proc Γ}
    (selected : Communication redex reduct) :
    inputHeader selected = .input1 ∨ inputHeader selected = .input2 := by
  cases selected
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Both primitive communication arities consume the independently given
target firing and preserve its exact endpoint modulo the static equations. -/
theorem modulo_step_readback {Γ Δ : Ctx sig} (source : Expr Γ)
    (environment : Ren sig Γ Δ) (faithful : Function.Injective (environment .nm))
    (result : Var Δ .nm) {target : Proc Δ}
    (firing : StepModulo (compile source environment result) target) :
    ∃ (action : Mettapedia.Languages.LambdaCalculus.NamePassing.Environment.Action)
      (successor : Expr Γ),
      Mettapedia.Languages.LambdaCalculus.NamePassing.Environment.StepModulo action source successor ∧
        StructuralEq target (compile successor environment result) := by
  obtain ⟨actual⟩ := modulo_step_exposes firing
  have arity := communication_arity actual.selected
  rcases arity with unary | binary
  · obtain ⟨action, successor, _, step, endpoint⟩ :=
      NamePassingUnaryReadback.unary_readback source environment faithful result actual unary
    exact ⟨action, successor, step, endpoint⟩
  · obtain ⟨successor, step, endpoint⟩ :=
      NamePassingBinaryReadback.binary_readback source environment result actual binary
    exact ⟨.beta, successor, step, endpoint⟩

/-- Every representative of an emitted static class has the same actual
source-step readback; the supplied target remains unchanged. -/
theorem class_step_readback {Γ Δ : Ctx sig} (source : Expr Γ)
    (environment : Ren sig Γ Δ) (faithful : Function.Injective (environment .nm))
    (result : Var Δ .nm) {current target : Proc Δ}
    (related : StructuralEq current (compile source environment result))
    (firing : StepModulo current target) :
    ∃ (action : Mettapedia.Languages.LambdaCalculus.NamePassing.Environment.Action)
      (successor : Expr Γ),
      Mettapedia.Languages.LambdaCalculus.NamePassing.Environment.StepModulo action source successor ∧
        StructuralEq target (compile successor environment result) := by
  apply modulo_step_readback source environment faithful result
  exact NamePassingEnvironment.modulo_congr related.symm firing (.refl target)

/-- A source is blocked exactly when its emitted process has no actual
communication modulo the authored equations. This does not equate blocking
with returning a lambda value. -/
theorem enabled_iff {Γ Δ : Ctx sig} (source : Expr Γ)
    (environment : Ren sig Γ Δ) (faithful : Function.Injective (environment .nm))
    (result : Var Δ .nm) :
    (∃ action successor,
      Mettapedia.Languages.LambdaCalculus.NamePassing.Environment.StepModulo action source successor) ↔
      ∃ target, StepModulo (compile source environment result) target := by
  constructor
  · rintro ⟨action, successor, step⟩
    exact ⟨_, NamePassingEnvironmentEquations.modulo_step_preserved step environment result⟩
  · rintro ⟨target, firing⟩
    obtain ⟨action, successor, step, _⟩ := modulo_step_readback source environment faithful result firing
    exact ⟨action, successor, step⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCompilerReadback
