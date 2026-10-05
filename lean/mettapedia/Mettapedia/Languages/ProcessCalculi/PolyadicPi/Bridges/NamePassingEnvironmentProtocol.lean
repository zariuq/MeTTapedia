import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentEquationsNative
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRealization

/-!
# The corrected environment source through the existing unary protocol

The source application/scope laws are interpreted by the existing polyadic
compiler and its existing one-or-four-communication protocol. Static source
equations introduce no additional communications. The supplied source path
and literal lowered endpoint are retained in the composed execution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentProtocol

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentEquationsNative
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypes (classPredicate)

/-- The corrected source uses the same emitted code and unary protocol. -/
noncomputable def realization {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (result : Var Δ .nm) :
    OperationalRealization (sourceTheory Γ) (NativeTypes.operationalTheory Δ) :=
  (NamePassingEnvironmentEquationsNative.realization environment result).comp
    (MonadicProtocol.realization Δ)

@[simp] theorem emitted_code {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) (term : NamePassingLambda.Expr Γ) :
    (realization environment result).mapTerm term =
      MonadicProtocol.lower (NamePassingLambda.compile term environment result) := rfl

theorem path_stages {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (result : Var Δ .nm)
    {source target : (sourceTheory Γ).Term} (path : ExecutionPath (sourceTheory Γ) source target) :
    (realization environment result).mapRoute path =
      (MonadicProtocol.realization Δ).mapRoute ((compiler environment result).mapRoute path) := by
  unfold NamePassingEnvironmentProtocol.realization
  rw [OperationalRealization.mapRoute_comp]
  exact congrArg (MonadicProtocol.realization Δ).mapRoute
    (OperationalRealization.mapRoute_ofTranslation (compiler environment result) path)

/-- The repaired static theory preserves the existing exact communication
account rather than charging new costs for changes of representative. -/
theorem path_bounds {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (result : Var Δ .nm)
    {source target : (sourceTheory Γ).Term} (path : ExecutionPath (sourceTheory Γ) source target) :
    path.length ≤ ((realization environment result).mapRoute path).length ∧
      ((realization environment result).mapRoute path).length ≤ 4 * path.length := by
  rw [path_stages]
  have bounds := MonadicProtocol.realization_path_bounds ((compiler environment result).mapRoute path)
  have length := OperationalTranslation.mapRoute_length (compiler environment result) path
  exact ⟨length ▸ bounds.1, length ▸ bounds.2⟩

theorem path_unary {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (result : Var Δ .nm)
    {source target : (sourceTheory Γ).Term} (path : ExecutionPath (sourceTheory Γ) source target) :
    MonadicProtocol.executionPathUnary ((realization environment result).mapRoute path) := by
  rw [path_stages]
  exact MonadicProtocol.realization_path_unary ((compiler environment result).mapRoute path)

noncomputable def account {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (result : Var Δ .nm) :
    Mettapedia.Effects.RunAccount (ExecutionObject (sourceTheory Γ)) (Multiplicative Nat) :=
  (realization environment result).blockAccount

theorem account_exact {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (result : Var Δ .nm)
    {source target : (sourceTheory Γ).Term} (path : ExecutionPath (sourceTheory Γ) source target) :
    (account environment result).of path =
      Multiplicative.ofAdd ((realization environment result).mapRoute path).length := rfl

/-- The primitive source event becomes an actual finite target execution.
This is the generated reachability diamond, with its block scale explicit. -/
theorem step_native_reachability {Γ Δ : Ctx sig} {action : NamePassing.Environment.Action}
    {source target : NamePassingLambda.Expr Γ}
    (step : NamePassing.Environment.StepModulo action source target)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) :
    (semanticDiamond (NativeTypes.operationalTheory Δ).closure
      (classPredicate ((realization environment result).mapTerm target))).1
      ((realization environment result).mapTerm source) := by
  apply (gsltDiamond_spec (NativeTypes.operationalTheory Δ).closure _ _).2
  exact ⟨_, (realization environment result).toClosureTranslation.mapStep ⟨action, step⟩,
    .refl _⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentProtocol
