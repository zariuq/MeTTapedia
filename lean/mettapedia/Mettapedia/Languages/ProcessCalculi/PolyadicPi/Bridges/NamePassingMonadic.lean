import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRealization
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentOrigins
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingChannelRoles

/-!
# Persistent name-passing programs through the actual unary protocol

The source environment compiler and the private-session lowering compose in
the existing execution category. Every source path reaches its supplied unary
endpoint, with between one and four actual communications per source firing.
Source occurrence histories can be carried alongside that execution: their
declaration owners and reference positions are retained before accounting.

The resulting forward comparison is for the independently scoped operational
interpretations. Arbitrary target schedules, channel-role discipline, the
canonical classifying presentation and the later rho realization require
separate comparisons.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingMonadic

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Causality.OccurrenceHistory
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypes
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambda
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentNative

/-- The actual two-stage compiler, not a new primitive evaluator. -/
def compileUnary {Γ Δ : Ctx sig} (term : Expr Γ) (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) : Proc Δ :=
  MonadicProtocol.lower (compile term environment result)

theorem compileUnary_unary {Γ Δ : Ctx sig} (term : Expr Γ)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) :
    MonadicProtocol.Unary (compileUnary term environment result) :=
  MonadicProtocol.lower_unary _

/-- Channel roles are derived from the real compiler. In particular a fresh
call/result channel cannot also be a source reference channel. -/
theorem polyadic_image_roles {Γ : Ctx sig} (term : Expr Γ) :
    NamePassingChannelRoles.Typed (NamePassingChannelRoles.canonicalRoles Γ)
      (compile term (fun _ name => .succ name) .zero) :=
  NamePassingChannelRoles.fresh_result_compile_typed term

/-- The compiler-derived roles persist through every supplied scoped
polyadic execution, rather than only at the two compiled boundary terms. -/
theorem polyadic_execution_roles {Γ : Ctx sig} (term : Expr Γ)
    {target : Proc (.nm :: Γ)}
    (path : ExecutionPath (operationalTheory (.nm :: Γ))
      (compile term (fun _ name => .succ name) .zero) target) :
    NamePassingChannelRoles.Typed (NamePassingChannelRoles.canonicalRoles Γ) target :=
  NamePassingChannelRoles.fresh_result_compilation_execution_roles term path

/-- Both stages use the previously checked operational realizations. -/
noncomputable def realization {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) :
    OperationalRealization (environmentTheory Γ) (operationalTheory Δ) :=
  (NamePassingEnvironmentNative.realization environment result).comp
    (MonadicProtocol.realization Δ)

/-- All source intermediate states and every unary administrative state
remain in the expanded path, with the literal compiled final expression. -/
noncomputable def compilePath {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) {source target : (environmentTheory Γ).Term}
    (path : ExecutionPath (environmentTheory Γ) source target) :
    ExecutionPath (operationalTheory Δ)
      (compileUnary source environment result) (compileUnary target environment result) :=
  (realization environment result).mapRoute path

/-- The complete actual execution, including protocol intermediates, remains
inside the unary subset. This follows from a general execution invariant. -/
theorem compilePath_unary {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) {source target : (environmentTheory Γ).Term}
    (path : ExecutionPath (environmentTheory Γ) source target) :
    MonadicProtocol.executionPathUnary (compilePath environment result path) :=
  MonadicProtocol.lowered_executionPath_unary (compile source environment result) _

theorem compilePath_stages {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) {source target : (environmentTheory Γ).Term}
    (path : ExecutionPath (environmentTheory Γ) source target) :
    compilePath environment result path =
      (MonadicProtocol.realization Δ).mapRoute ((compiler environment result).mapRoute path) :=
  staged_path environment result (MonadicProtocol.realization Δ) path

theorem compilePath_bounds {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) {source target : (environmentTheory Γ).Term}
    (path : ExecutionPath (environmentTheory Γ) source target) :
    path.length ≤ (compilePath environment result path).length ∧
      (compilePath environment result path).length ≤ 4 * path.length := by
  have bounds := MonadicProtocol.realization_path_bounds
    ((compiler environment result).mapRoute path)
  have intermediate := OperationalTranslation.mapRoute_length
    (compiler environment result) path
  have stages := congrArg (fun run => run.length)
    (compilePath_stages environment result path)
  constructor
  · calc
      path.length = ((compiler environment result).mapRoute path).length := intermediate.symm
      _ ≤ ((MonadicProtocol.realization Δ).mapRoute
          ((compiler environment result).mapRoute path)).length := bounds.1
      _ = (compilePath environment result path).length := stages.symm
  · calc
      (compilePath environment result path).length = _ := stages
      _ ≤ 4 * ((compiler environment result).mapRoute path).length := bounds.2
      _ = 4 * path.length := congrArg (fun count => 4 * count) intermediate

/-- Read the final target account through the composed compiler. -/
noncomputable def account {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) :
    Mettapedia.Effects.RunAccount (ExecutionObject (environmentTheory Γ))
      (Multiplicative Nat) := (realization environment result).blockAccount

theorem account_exact {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) {source target : (environmentTheory Γ).Term}
    (path : ExecutionPath (environmentTheory Γ) source target) :
    (account environment result).of path =
      Multiplicative.ofAdd (compilePath environment result path).length := rfl

/-- Erasing origin labels is explicit; the supplied source history remains
available to consumers together with its actual compiled execution. -/
noncomputable def compileHistory {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) {source target : (environmentTheory Γ).Term}
    (history : OccurrencePath (NamePassingEnvironmentOrigins.events Γ) source target) :
    ExecutionPath (operationalTheory Δ)
      (compileUnary source environment result) (compileUnary target environment result) :=
  (MonadicProtocol.realization Δ).mapRoute
    (NamePassingEnvironmentOrigins.compileHistory environment result history)

theorem compileHistory_bounds {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) {source target : (environmentTheory Γ).Term}
    (history : OccurrencePath (NamePassingEnvironmentOrigins.events Γ) source target) :
    history.sites.length ≤ (compileHistory environment result history).length ∧
      (compileHistory environment result history).length ≤ 4 * history.sites.length := by
  have bounds := NamePassingEnvironmentOrigins.staged_history_bounds environment result
    (MonadicProtocol.realization Δ) 1 4
    (fun step => MonadicProtocol.realization_step_bounds step) history
  have lower : history.sites.length ≤
      ((MonadicProtocol.realization Δ).mapRoute
        (NamePassingEnvironmentOrigins.compileHistory environment result history)).length :=
    calc
      history.sites.length = 1 * history.sites.length := (Nat.one_mul _).symm
      _ ≤ _ := bounds.1
  exact ⟨lower, bounds.2⟩

/-- The compiled native observation is finite reachability. It does not
identify one source firing with one primitive unary communication. -/
theorem step_reaches_native {Γ Δ : Ctx sig} {source target : Expr Γ}
    {kind : NamePassing.Environment.Action}
    (step : NamePassing.Environment.Step kind source target)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) :
    (semanticDiamond (operationalTheory Δ).closure
      (classPredicate (compileUnary target environment result))).1
      (compileUnary source environment result) := by
  apply (gsltDiamond_spec (operationalTheory Δ).closure _ _).2
  exact ⟨_, (realization environment result).toClosureTranslation.mapStep ⟨kind, step⟩,
    .refl _⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingMonadic
