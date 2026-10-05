import Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredClassified

/-!
# Scoped presentation and active-profile controls

A private channel communicates through the actual binder-local authored
profile and its classifying interpretation. Input guards remain suspended
even after arbitrary static rearrangement. The closed-root contextual
adapter has a distinct carrier boundary: this signature has no closed name,
so a closed root occurrence cannot represent the private communication.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredPresentationControls

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredEquations
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredOperationalProfile
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredClassified

/-- Existence of an output outside input guards. Scope and replication
retain the observation; the suspended continuation of an input does not. -/
def activeOutput : {Γ : Ctx sig} → Proc Γ → Bool
  | _, .var _ => false
  | _, .op .nil .nil => false
  | _, .op .par (.cons first (.cons second .nil)) =>
      activeOutput first || activeOutput second
  | _, .op .inp1 (.cons _ (.cons _ .nil)) => false
  | _, .op .inp2 (.cons _ (.cons _ .nil)) => false
  | _, .op .out1 (.cons _ (.cons _ .nil)) => true
  | _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))) => true
  | _, .op .nu (.cons body .nil) => activeOutput body
  | _, .op .rep (.cons body .nil) => activeOutput body
termination_by _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem activeOutput_rename : ∀ {Γ Δ : Ctx sig} (ρ : Ren sig Γ Δ) (process : Proc Γ),
    activeOutput (rename ρ process) = activeOutput process
  | _, _, _, .var _ => by simp only [rename, activeOutput]
  | _, _, _, .op .nil .nil => by simp only [rename, renameArgs, activeOutput]
  | _, _, ρ, .op .par (.cons first (.cons second .nil)) => by
      simp only [rename, renameArgs, activeOutput, liftRen]
      rw [activeOutput_rename ρ first, activeOutput_rename ρ second]
  | _, _, _, .op .inp1 (.cons _ (.cons _ .nil)) => by simp only [rename, renameArgs, activeOutput]
  | _, _, _, .op .inp2 (.cons _ (.cons _ .nil)) => by simp only [rename, renameArgs, activeOutput]
  | _, _, _, .op .out1 (.cons _ (.cons _ .nil)) => by simp only [rename, renameArgs, activeOutput]
  | _, _, _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))) => by simp only [rename, renameArgs, activeOutput]
  | _, _, ρ, .op .nu (.cons body .nil) => by
      simp only [rename, renameArgs, activeOutput]
      exact activeOutput_rename (liftRen ρ [.nm]) body
  | _, _, ρ, .op .rep (.cons body .nil) => by
      simp only [rename, renameArgs, activeOutput]
      exact activeOutput_rename ρ body
termination_by _ _ _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

/-- Every declared static equation preserves the guard boundary. -/
theorem activeOutput_structural {Γ : Ctx sig} {first second : Proc Γ}
    (equal : StructuralEq first second) : activeOutput first = activeOutput second := by
  induction equal with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ firstIH secondIH => exact firstIH.trans secondIH
  | parComm first second => simpa only [par, activeOutput] using Bool.or_comm (activeOutput first) (activeOutput second)
  | parAssoc first second third => simpa only [par, activeOutput] using Bool.or_assoc (activeOutput first) (activeOutput second) (activeOutput third)
  | parUnit process => simp only [par, nil, activeOutput, Bool.or_false]
  | nuUnused process => simpa only [nu, activeOutput, weaken] using activeOutput_rename (fun _ name => .succ name) process
  | nuPar process frame =>
      simp only [par, nu, activeOutput, weaken]
      rw [activeOutput_rename]
  | nuSwap process => simpa only [nu, activeOutput] using (activeOutput_rename swapRen process).symm
  | repUnfold process => simp only [rep, par, activeOutput, Bool.or_self]
  | par _ _ firstIH secondIH => simpa only [par, activeOutput] using congrArg₂ Bool.or firstIH secondIH
  | nu _ ih => simpa only [nu, activeOutput] using ih
  | inp1 => simp only [inp1, activeOutput]
  | inp2 => simp only [inp2, activeOutput]
  | rep _ ih => simpa only [rep, activeOutput] using ih

theorem actual_step_has_active_output {Γ : Ctx sig} {source target : Proc Γ}
    (step : Step source target) : activeOutput source = true := by
  induction step with
  | comm1 => simp only [par, out1, inp1, activeOutput, Bool.true_or]
  | comm2 => simp only [par, out2, inp2, activeOutput, Bool.true_or]
  | parL frame _ ih =>
      simp only [par, activeOutput]
      rw [ih]
      rfl
  | parR frame _ ih =>
      simp only [par, activeOutput]
      rw [ih]
      exact Bool.or_true _
  | nu _ ih => simpa only [nu, activeOutput] using ih

theorem modulo_step_has_active_output {Γ : Ctx sig} {source target : Proc Γ}
    (step : StepModulo source target) : activeOutput source = true := by
  obtain ⟨redex, reduct, before, firing, _⟩ := step
  exact (activeOutput_structural before).trans (actual_step_has_active_output firing)

/-- Equations inside an input do not authorize executing its suspended body. -/
theorem unary_guard_has_no_classified_step {Γ : Ctx sig}
    (channel : Name Γ) (body : Proc (.nm :: Γ)) (target : Proc Γ) :
    ¬ IntrinsicScopedAuthoredClassifiedReduction.ExtendedReduction rules equations
      (inp1 channel body) target := by
  intro step
  have impossible := modulo_step_has_active_output
    ((extension_iff_stepModulo _ _).mp step)
  simp only [inp1, activeOutput] at impossible
  cases impossible

theorem binary_guard_has_no_classified_step {Γ : Ctx sig}
    (channel : Name Γ) (body : Proc (.nm :: .nm :: Γ)) (target : Proc Γ) :
    ¬ IntrinsicScopedAuthoredClassifiedReduction.ExtendedReduction rules equations
      (inp2 channel body) target := by
  intro step
  have impossible := modulo_step_has_active_output
    ((extension_iff_stepModulo _ _).mp step)
  simp only [inp2, activeOutput] at impossible
  cases impossible

def privateCommunication : Proc [] :=
  nu (par (out1 (.var .zero) (.var .zero)) (inp1 (.var .zero) nil))

theorem private_communication_executes : Step privateCommunication (nu nil) :=
  .nu (.comm1 _ _ _)

theorem private_communication_is_authored :
    Nonempty (IntrinsicScopedLocalPolynomial.Tree rules (BindingCloneAlgebra.terms sig)
      ⟨[], Srt.pr, privateCommunication, nu nil⟩) :=
  step_complete private_communication_executes

theorem private_communication_is_classified :
    IntrinsicScopedAuthoredClassifiedReduction.ExtendedReduction rules equations
      privateCommunication (nu nil) :=
  (extension_iff_stepModulo _ _).mpr private_communication_executes.toModulo

theorem no_closed_name (name : Name []) : False := by
  cases name with
  | var impossible => nomatch impossible
  | op impossible args => cases impossible

theorem no_closed_unary_root (source target : Proc []) :
    ¬ comm1.RootStep source target := by
  rintro ⟨_, close, _, _⟩
  exact no_closed_name (close .nm .zero)

theorem no_closed_binary_root (source target : Proc []) :
    ¬ comm2.RootStep source target := by
  rintro ⟨_, close, _, _⟩
  exact no_closed_name (close .nm .zero)

/-- This control requires binder-local root occurrences; the closed-root
one-hole adapter is not the active profile's operational authority. -/
theorem closed_root_adapter_cannot_express_private_step (target : Proc []) :
    ¬ presentation.StepModE privateCommunication target := by
  rintro ⟨index, redex, reduct, _, ⟨context, root, result, _, firing, _, _⟩, _⟩
  rcases index with ⟨index, bounded⟩
  have small : index < 2 := by simpa [presentation] using bounded
  interval_cases index
  · exact no_closed_unary_root root result firing
  · exact no_closed_binary_root root result firing

theorem distinct_names_not_equated :
    ¬ EqClosure presentation.eqs
      (.var .zero : Name [Srt.nm, Srt.nm]) (.var (.succ .zero)) := by
  intro equal
  have impossible := (name_eqClosure_iff _ _).mp equal
  cases impossible

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredPresentationControls
