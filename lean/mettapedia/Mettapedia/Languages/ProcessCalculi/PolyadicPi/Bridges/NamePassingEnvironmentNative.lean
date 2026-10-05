import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironment
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypes
import Mettapedia.GSLT.Core.OperationalRealizationOSLF
import Mettapedia.GSLT.Core.OperationalRealizationAccounts

/-!
# Native execution and accounts of persistent name-passing environments

The extended source uses its independent environment dynamics. The actual
compiler is a forward operational translation into the scoped unary/binary
interpretation. Its existing free execution functor retains intermediate
states and the supplied endpoint, while the existing run account records
one communication per source firing. Scope rearrangement and replication
unfolding are static equations, not counted communications.

This is an execution and native-predicate comparison. It does not reflect
arbitrary target schedules, claim a call-by-need cache, identify the canonical
LanguageDef static engine, or transport all dependent type formers.
-/

set_option autoImplicit false

open CategoryTheory

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentNative

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypes
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambda
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironment

/-- The nonrecursive environment fragment, with no extra static identifications. -/
def environmentTheory (Γ : Ctx sig) : GSLT where
  Term := Expr Γ
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target => ∃ action, NamePassing.Environment.Step action source target
  rewrites_resp_left := by
    intro source source' target equal step
    cases equal
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    cases equal
    exact step

/-- The actual compiler and its checked environment comparison share one
operational translation; path and logical consumers reuse that translation. -/
def compiler {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (result : Var Δ .nm) :
    OperationalTranslation (environmentTheory Γ) (operationalTheory Δ) where
  mapTerm term := compile term environment result
  mapEquiv := by
    intro first second equal
    change first = second at equal
    cases equal
    exact .refl _
  mapStep := by
    rintro source target ⟨kind, step⟩
    exact step_preserved step environment result

/-- The compiler's path-valued reading uses the existing realization interface. -/
def realization {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (result : Var Δ .nm) :
    OperationalRealization (environmentTheory Γ) (operationalTheory Δ) :=
  .ofTranslation (compiler environment result)

/-- Source accounting is the actual target account read along the compiler's
existing path functor, rather than a separately specified cost authority. -/
def compiledAccount {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) :
    Mettapedia.Effects.RunAccount (ExecutionObject (environmentTheory Γ))
      (Multiplicative Nat) :=
  (transitionAccount (operationalTheory Δ)).comap (compiler environment result).pathFunctor

/-- Every independently authored source firing contributes exactly one target
communication; the complete path, including loops, obeys this equality. -/
theorem compiledAccount_exact {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) {source target : (environmentTheory Γ).Term}
    (path : ExecutionPath (environmentTheory Γ) source target) :
    (compiledAccount environment result).of path = Multiplicative.ofAdd path.length := by
  change Multiplicative.ofAdd ((compiler environment result).mapRoute path).length = _
  rw [OperationalTranslation.mapRoute_length]

def compiledPredicate {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) (predicate : EquationPredicate (operationalTheory Δ)) :
    EquationPredicate (environmentTheory Γ) :=
  ⟨fun term => predicate.1 (compile term environment result),
    by intro first second equal; change first = second at equal; cases equal; rfl⟩

/-- A particular source environment event carries its endpoint certificate
into the target's generated native diamond. -/
theorem step_nativeDiamond {Γ Δ : Ctx sig} {kind : NamePassing.Environment.Action}
    {source target : Expr Γ} (step : NamePassing.Environment.Step kind source target)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm)
    (predicate : EquationPredicate (operationalTheory Δ))
    (holds : predicate.1 (compile target environment result)) :
    (semanticDiamond (operationalTheory Δ) predicate).1
      (compile source environment result) :=
  (nativeDiamond_iff predicate _).2
    ⟨_, step_preserved step environment result, holds⟩

theorem compiledDiamond_le {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) (predicate : EquationPredicate (operationalTheory Δ)) :
    (semanticDiamond (environmentTheory Γ)
      (compiledPredicate environment result predicate)).1 ≤
      fun source => (semanticDiamond (operationalTheory Δ) predicate).1
        (compile source environment result) := by
  intro source possible
  obtain ⟨target, ⟨kind, step⟩, holds⟩ :=
    (gsltDiamond_spec (environmentTheory Γ) _ source).1 possible
  exact step_nativeDiamond step environment result predicate holds

/-- Later lowering stages compose using their actual selected target blocks.
The intermediate path is retained before accounting or native observation. -/
theorem staged_path {Γ Δ : Ctx sig} {targetTheory : GSLT}
    (environment : Ren sig Γ Δ) (result : Var Δ .nm)
    (later : OperationalRealization (operationalTheory Δ) targetTheory)
    {source target : (environmentTheory Γ).Term}
    (path : ExecutionPath (environmentTheory Γ) source target) :
    ((realization environment result).comp later).mapRoute path =
      later.mapRoute ((compiler environment result).mapRoute path) := by
  rw [OperationalRealization.mapRoute_comp]
  change later.mapRoute
      ((OperationalRealization.ofTranslation (compiler environment result)).mapRoute path) = _
  rw [OperationalRealization.mapRoute_ofTranslation]
  rfl

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentNative
