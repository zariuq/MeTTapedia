import Mettapedia.Logic.HOL.ConstantExpansionProofsFree

/-!
# Finite contextual beta evidence without extensionality

The existing typed beta-step and execution elaborators use neither eta nor
function extensionality, including under every logical constructor and binder.
This qualifies finite supplied executions; it supplies no normalization
algorithm or global termination theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.ContextualTrinity

universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base} {τ : Ty Base}
variable {source target : Term Const Γ τ}

theorem BetaStep.proof_free (step : BetaStep source target) (assumptions : List (Formula Const Γ)) :
    (step.proof assumptions).FunctionExtensionalityFree := by
  induction step with
  | _ => simp_all only [BetaStep.proof, ProofSyntax.FunctionExtensionalityFree,
      castEq_free, holeCongr_free, allCongr_free, exCongr_free]

theorem Execution.proof_free (execution : Execution source target)
    (assumptions : List (Formula Const Γ)) :
    (execution.proof assumptions).FunctionExtensionalityFree := by
  induction execution with
  | done => trivial
  | step first rest ih => exact ⟨first.proof_free assumptions, ih⟩

theorem Execution.variable_target (index : Var Γ τ) {target : Term Const Γ τ}
    (execution : Execution (.var index) target) : target = .var index := by
  cases execution with
  | done => rfl
  | step first _ => cases first

/-- An eta expansion of a variable is outside forward beta execution. This
does not assert a general characterization of beta-convertibility. -/
theorem variable_eta_not_executed {σ ρ : Ty Base} (index : Var Γ (σ ⇒ ρ)) :
    ¬Nonempty (Execution (.var index : Term Const Γ (σ ⇒ ρ))
      (.lam (.app (.var (.vs index)) (.var .vz)))) := by
  rintro ⟨execution⟩
  have same := execution.variable_target index
  cases same

namespace FreeControls

theorem outer_free (assumptions : List (Formula Controls.NoConstant Controls.here)) :
    (Controls.outerFirst.proof assumptions).FunctionExtensionalityFree :=
  Controls.outerFirst.proof_free assumptions

theorem inner_free (assumptions : List (Formula Controls.NoConstant Controls.here)) :
    (Controls.innerFirst.proof assumptions).FunctionExtensionalityFree :=
  Controls.innerFirst.proof_free assumptions

end FreeControls

#print axioms BetaStep.proof_free
#print axioms Execution.proof_free
#print axioms variable_eta_not_executed
#print axioms FreeControls.outer_free
#print axioms FreeControls.inner_free

end Mettapedia.Logic.HOL.ContextualTrinity
