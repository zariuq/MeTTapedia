import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentEquations
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentNative

/-!
# Native interpretation of source application and scope equations

The independently authored blue-calculus application laws extend the directed
environment fragment. Its existing transitions are taken modulo those laws,
and the already checked compiler interprets that extension in the existing
scoped polyadic operational theory. The directed fragment embeds into it.

The comparison retains source and target execution endpoints and uses the
existing path/account interfaces. It is forward native-predicate transport;
arbitrary target execution reflection remains an additional obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentEquationsNative

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypes (operationalTheory)
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambda (Expr compile)

/-- The corrected source interpretation uses the published static laws and
the independently defined environment communication events. -/
def sourceTheory (Γ : Ctx sig) : GSLT where
  Term := Expr Γ
  equations := ⟨NamePassing.Environment.StructuralEq,
    ⟨NamePassing.Environment.StructuralEq.refl,
      NamePassing.Environment.StructuralEq.symm,
      NamePassing.Environment.StructuralEq.trans⟩⟩
  rewrites := fun source target =>
    ∃ action, NamePassing.Environment.StepModulo action source target
  rewrites_resp_left := by
    intro source source' target equal step
    obtain ⟨action, redex, contractum, before, firing, after⟩ := step
    exact ⟨target, ⟨action, redex, contractum,
      .trans (.symm equal) before, firing, after⟩, .refl target⟩
  rewrites_resp_right := by
    intro source target target' step equal
    obtain ⟨action, redex, contractum, before, firing, after⟩ := step
    exact ⟨action, redex, contractum, before, firing, .trans after equal⟩

/-- The earlier directed interpretation is a genuine subfragment. -/
def directedInclusion (Γ : Ctx sig) :
    OperationalTranslation (NamePassingEnvironmentNative.environmentTheory Γ) (sourceTheory Γ) where
  mapTerm term := term
  mapEquiv := by
    rintro first second rfl
    exact .refl _
  mapStep := by
    rintro first second ⟨action, step⟩
    exact ⟨action, step.toModulo⟩

/-- Both new static laws and source computation use the existing compiler,
not a semantic definition of the source in terms of compiled behavior. -/
def compiler {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (result : Var Δ .nm) :
    OperationalTranslation (sourceTheory Γ) (operationalTheory Δ) where
  mapTerm term := compile term environment result
  mapEquiv := by
    intro first second equal
    exact NamePassingEnvironmentEquations.compile_structural equal environment result
  mapStep := by
    rintro first second ⟨action, step⟩
    exact NamePassingEnvironmentEquations.modulo_step_preserved step environment result

def realization {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (result : Var Δ .nm) :
    OperationalRealization (sourceTheory Γ) (operationalTheory Δ) :=
  .ofTranslation (compiler environment result)

/-- Extending the static source theory does not change the compiler's
emitted program on the directed fragment. -/
theorem directed_compiler_agreement {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) (term : Expr Γ) :
    (compiler environment result).mapTerm ((directedInclusion Γ).mapTerm term) =
      (NamePassingEnvironmentNative.compiler environment result).mapTerm term := rfl

def compiledAccount {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (result : Var Δ .nm) :
    Mettapedia.Effects.RunAccount (ExecutionObject (sourceTheory Γ)) (Multiplicative Nat) :=
  (transitionAccount (operationalTheory Δ)).comap (compiler environment result).pathFunctor

/-- Static scope administration adds no communications: each source event
still contributes precisely one actual polyadic communication. -/
theorem compiledAccount_exact {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) {source target : (sourceTheory Γ).Term}
    (path : ExecutionPath (sourceTheory Γ) source target) :
    (compiledAccount environment result).of path = Multiplicative.ofAdd path.length := by
  change Multiplicative.ofAdd ((compiler environment result).mapRoute path).length = _
  rw [OperationalTranslation.mapRoute_length]

def compiledPredicate {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) (predicate : EquationPredicate (operationalTheory Δ)) :
    EquationPredicate (sourceTheory Γ) :=
  ⟨fun term => predicate.1 (compile term environment result),
    fun _ _ equal => predicate.2 ((compiler environment result).mapEquiv equal)⟩

theorem step_nativeDiamond {Γ Δ : Ctx sig} {action : NamePassing.Environment.Action}
    {source target : Expr Γ} (step : NamePassing.Environment.StepModulo action source target)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm)
    (predicate : EquationPredicate (operationalTheory Δ))
    (holds : predicate.1 (compile target environment result)) :
    (semanticDiamond (operationalTheory Δ) predicate).1 (compile source environment result) :=
  (NativeTypes.nativeDiamond_iff predicate _).2
    ⟨_, NamePassingEnvironmentEquations.modulo_step_preserved step environment result, holds⟩

/-- The generated source diamond is carried into the target native diamond
for every target equation-saturated observation read along this compiler. -/
theorem compiledDiamond_le {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) (predicate : EquationPredicate (operationalTheory Δ)) :
    (semanticDiamond (sourceTheory Γ) (compiledPredicate environment result predicate)).1 ≤
      fun source => (semanticDiamond (operationalTheory Δ) predicate).1
        (compile source environment result) := by
  intro source possible
  obtain ⟨target, ⟨action, step⟩, holds⟩ :=
    (gsltDiamond_spec (sourceTheory Γ) _ source).1 possible
  exact step_nativeDiamond step environment result predicate holds

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentEquationsNative
