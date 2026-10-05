import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentEquations
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingChannelRoles

/-!
# Application scope laws discriminate the old and corrected source dynamics

The earlier directed source relation cannot call a lambda below a floating
carrier or definition. Its faithful, role-correct compiler image nevertheless
communicates at the private call channel. The independent published scope
equations authorize precisely that beta event while retaining its declaration.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingScopeControls

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambda
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentEquations
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingChannelRoles

theorem old_carrier_wrapped_call_is_stuck {Γ : Ctx sig} (name : Var Γ .nm)
    (value : Expr Γ) (body : Expr (.nm :: Γ)) (argument : Var Γ .nm)
    {action : NamePassing.Environment.Action} {target : Expr Γ} :
    ¬ NamePassing.Environment.Step action (.app (.carrier name value (.lam body)) argument) target := by
  intro step
  cases step with
  | app argument functionStep =>
      cases functionStep with
      | carrierFetch name value fetch => cases fetch
      | carrier name value nested => cases nested

theorem old_definition_wrapped_call_is_stuck {Γ : Ctx sig} (value : Expr Γ)
    (body : Expr (.nm :: .nm :: Γ)) (argument : Var Γ .nm)
    {action : NamePassing.Environment.Action} {target : Expr Γ} :
    ¬ NamePassing.Environment.Step action (.app (.defn value (.lam body)) argument) target := by
  intro step
  cases step with
  | app argument functionStep =>
      cases functionStep with
      | environmentFetch value fetch => cases fetch
      | defn value nested => cases nested

def source : Expr [Srt.nm, Srt.nm] :=
  .app (.carrier .zero (.lam (.var .zero)) (.lam (.var .zero))) (.succ .zero)

def target : Expr [Srt.nm, Srt.nm] :=
  .carrier .zero (.lam (.var .zero)) (.var (.succ .zero))

def names : Ren sig [Srt.nm, Srt.nm] [Srt.nm, Srt.nm, Srt.nm] :=
  fun _ name => .succ name

def result : Var [Srt.nm, Srt.nm, Srt.nm] .nm := .zero

theorem source_is_stuck {action : NamePassing.Environment.Action}
    {endpoint : Expr [Srt.nm, Srt.nm]} : ¬ NamePassing.Environment.Step action source endpoint :=
  old_carrier_wrapped_call_is_stuck _ _ _ _

theorem corrected_source_beta : NamePassing.Environment.StepModulo .beta source target :=
  NamePassing.Environment.carrier_wrapped_beta _ _ _ _

theorem compiler_really_communicates :
    StepModulo (compile source names result) (compile target names result) :=
  modulo_step_preserved corrected_source_beta names result

theorem compiler_roles_hold :
    Typed (canonicalRoles [Srt.nm, Srt.nm]) (compile source names result) :=
  fresh_result_compile_typed source

theorem names_are_injective : Function.Injective (names Srt.nm) := by
  intro first second same
  exact Var.succ.inj same

/-- Name faithfulness and the channel-role discipline cannot compensate for
missing independently justified source scope equations. -/
theorem directed_source_global_reflection_is_false :
    ¬ (∀ term : Expr [Srt.nm, Srt.nm], ∀ endpoint : Proc [Srt.nm, Srt.nm, Srt.nm],
      StepModulo (compile term names result) endpoint →
        ∃ action next, NamePassing.Environment.Step action term next ∧
          StructuralEq endpoint (compile next names result)) := by
  intro reflects
  obtain ⟨action, next, step, _⟩ := reflects source _ compiler_really_communicates
  exact source_is_stuck step

theorem definition_scope_supplies_beta {Γ Δ : Ctx sig} (value : Expr Γ)
    (body : Expr (.nm :: .nm :: Γ)) (argument : Var Γ .nm)
    (environment : Ren sig Γ Δ) (returned : Var Δ .nm) :
    StepModulo (compile (.app (.defn value (.lam body)) argument) environment returned)
      (compile (.defn value (NamePassing.instantiate body (.succ argument))) environment returned) :=
  modulo_step_preserved (NamePassing.Environment.definition_wrapped_beta value body argument)
    environment returned

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingScopeControls
