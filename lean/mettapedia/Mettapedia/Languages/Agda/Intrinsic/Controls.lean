import Mettapedia.Languages.Agda.Intrinsic.Execution

/-!
# Structural execution controls

The examples cover every operational constructor family, local binder
contexts, coincident endpoints with distinct firing histories, and the
difference between a depth bound and irreducibility. They concern computation
and scope, not a claim of complete Agda typing or declaration admission.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Intrinsic.Controls

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.MeTTaIL.Engine
open Rendering (encode)
open Execution (run)

def identity {Γ : Ctx sig} : Tm Γ := lam (.var .zero)
def redex {Γ : Ctx sig} : Tm Γ := app identity zero

def closed (term : Tm []) : Pattern := encode term

def targets {Γ : Ctx sig} (fuel : Nat) (source : Tm Γ) : List Pattern :=
  (run fuel source).map Prod.snd

def roots {Γ : Ctx sig} (fuel : Nat) (source : Tm Γ) : List Nat :=
  (run fuel source).map fun entry => match entry.1 with
    | .fire rule _ => rule

def underBinder : Tm [] := lam (app identity (.var .zero))
def capturedSource : Tm [.term] := app (lam (lam (.var (.succ .zero)))) (.var .zero)

/-- A generated binder congruence performs the premise in the extended
context, where the outer lambda variable is still in scope. -/
theorem binder_step : targets 2 underBinder = [encode (identity : Tm [])] := by
  decide +kernel

theorem binder_fuel_insufficient : targets 1 underBinder = [] := by decide +kernel

/-- The preceding empty bounded result is not evidence that the source is
irreducible: the independent relation has this exact step. -/
theorem binder_reference_step : Step underBinder identity :=
  .congr .lam (.head .nil (.root (.beta (.var .zero) (.var .zero))))

theorem ambient_not_captured :
    targets 1 capturedSource = [encode (lam (.var (.succ .zero)) : Tm [.term])] := by
  decide +kernel

theorem wrong_captured_result_absent :
    encode (identity : Tm [.term]) ∉ targets 1 capturedSource := by decide +kernel

/-- Root beta and argument congruence coincide at their endpoint here. -/
def overlap : Tm [] := app identity redex

theorem two_firings_same_endpoint : targets 2 overlap = [closed redex, closed redex] := by
  decide +kernel

/-- Their selected rule positions remain different in the execution result. -/
theorem two_firings_distinct_roots : roots 2 overlap = [0, 11] := by decide +kernel

theorem first_projection : targets 1 (fst (pair zero star) : Tm []) = [closed zero] := by
  decide +kernel

theorem second_projection : targets 1 (snd (pair zero star) : Tm []) = [closed star] := by
  decide +kernel

theorem annotation_erasure : targets 1 (ann zero nat : Tm []) = [closed zero] := by
  decide +kernel

theorem successor_application :
    targets 1 (app natSuc zero : Tm []) = [closed (suc zero)] := by decide +kernel

theorem recursion_zero :
    targets 1 (natrec (univ 0) identity zero identity zero : Tm []) = [closed zero] := by
  decide +kernel

theorem recursion_successor :
    targets 1 (natrec (univ 0) identity zero identity (suc zero) : Tm []) =
      [closed (app (app identity zero) (natrec (univ 0) identity zero identity zero))] := by
  decide +kernel

theorem product_domain_step :
    targets 2 (pi redex (.var .zero) : Tm []) = [closed (pi zero (.var .zero))] := by
  decide +kernel

theorem product_body_step :
    targets 2 (pi nat (app identity (.var .zero)) : Tm []) =
      [closed (pi nat (.var .zero))] := by decide +kernel

theorem sum_body_step :
    targets 2 (sigma nat (app identity (.var .zero)) : Tm []) =
      [closed (sigma nat (.var .zero))] := by decide +kernel

theorem zero_is_inert : targets 3 (zero : Tm []) = [] := by decide +kernel

theorem variable_not_erased_by_eta : targets 3 (.var .zero : Tm [.term]) = [] := by
  decide +kernel

/-- Ill-scoped raw syntax cannot enter through the beta matcher. -/
theorem escaping_body_refused :
    (rewriteAt RelationEnv.empty Execution.language 1 0
      (.apply "App" [.apply "Lam" [.lambda none (.bvar 4)], encode (zero : Tm [])])).isEmpty =
      true := by decide +kernel

/-- Scope discipline alone is not typing or termination. -/
def diagonal : Tm [] := lam (app (.var .zero) (.var .zero))
def omegaTerm : Tm [] := app diagonal diagonal

theorem untyped_self_step : Step omegaTerm omegaTerm :=
  .root (.beta (app (.var .zero) (.var .zero)) diagonal)

theorem untyped_self_step_executes : targets 1 omegaTerm = [closed omegaTerm] := by
  decide +kernel

theorem untyped_self_step_observable :
    Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltDiamond
      (Semantics.theory []) (Semantics.predicate (fun t => t = omegaTerm))
      (Semantics.state omegaTerm) :=
  (Semantics.diamond_iff _ _).mpr ⟨omegaTerm, untyped_self_step, rfl⟩

private def firstValuation : Authored.Val [] :=
  Authored.valuation (.var .zero) (.var .zero) zero star star star star zero

private def secondValuation : Authored.Val [] :=
  Authored.valuation (.var .zero) (.var .zero) zero star star star star star

/-- The common metavariable telescope retains assignments even when a rule
does not use them. Consequently endpoint adequacy is not a bijection of
firing instances. A future proof-object comparison must account for this. -/
theorem unused_assignment_changes_instance_only :
    Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial.conclusionJudgment
      Authored.rules Authored.algebra
      (Authored.occurrence ⟨0, by decide⟩ firstValuation) =
    Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial.conclusionJudgment
      Authored.rules Authored.algebra
      (Authored.occurrence ⟨0, by decide⟩ secondValuation) ∧
    Authored.occurrence ⟨0, by decide⟩ firstValuation ≠
      Authored.occurrence ⟨0, by decide⟩ secondValuation := by
  constructor
  · rw [Authored.beta_conclusion, Authored.beta_conclusion]
    rfl
  · intro same
    have values := congrArg (fun occurrence =>
      (⟨occurrence.ambient, occurrence.valuation 7⟩ : Σ Γ : Ctx sig, Tm Γ)) same
    change (⟨[], zero⟩ : Σ Γ : Ctx sig, Tm Γ) = ⟨[], star⟩ at values
    have impossible : (zero : Tm []) = star := eq_of_heq (Sigma.mk.inj_iff.mp values).2
    cases impossible

end Mettapedia.Languages.Agda.Intrinsic.Controls
