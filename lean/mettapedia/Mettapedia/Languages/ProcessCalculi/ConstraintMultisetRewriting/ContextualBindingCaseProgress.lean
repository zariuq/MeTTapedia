import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingCase
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActiveSupport

/-!
# Progress belongs to the binding case actually returned by recovery

The selected name and body remain available after executable recovery.
Their support bounds remove that name from the retained equations. Every
original model is itself a residual model, with a strictly smaller finite
active potential; no finite ambient declaration family is required.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingCaseProgress

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualBindingCase
open ContextualActiveSupport

variable {S : Signature} {V W : Type} [DecidableEq V]
  {source : V → MetaArity S} {next : W → MetaArity S}

def answer {Γ : Ctx S} {sort : S.Srt} {left right : Term (signature S source) Γ sort}
    (binding : Case left right) : Assignment source source :=
  ContextualBinding.answer binding.chosen binding.body

theorem candidate_is_fixed {Γ : Ctx S} {sort : S.Srt}
    {left right : Term (signature S source) Γ sort} (binding : Case left right)
    (candidate : Assignment source next) (solved : instantiate candidate left = instantiate candidate right) :
    Assignment.compose candidate (answer binding) = candidate := by
  have models : ContextualFrameUnifier.Models candidate [(left, right)] := by
    intro equation member
    have same := List.mem_singleton.mp member
    subst equation
    exact solved
  obtain ⟨residual, components⟩ := binding.principal.factors next candidate models
  have factors : candidate = Assignment.compose residual (answer binding) := funext components
  have idempotent : Assignment.compose (answer binding) (answer binding) = answer binding :=
    ContextualBinding.answer_idempotent binding.chosen binding.body binding.absent
  rw [factors, ← Assignment.compose_associative, idempotent]

theorem source_name_is_active {Γ : Ctx S} {sort : S.Srt}
    {left right : Term (signature S source) Γ sort} (binding : Case left right)
    (problem : Problem source) (selected : (observe left, observe right) ∈ problem) :
    binding.chosen ∈ active problem := by
  apply (mem_active binding.chosen problem).mpr
  exact ⟨_, selected, List.mem_append.mp binding.selected⟩

theorem body_is_covered {Γ : Ctx S} {sort : S.Srt}
    {left right : Term (signature S source) Γ sort} (binding : Case left right)
    (problem : Problem source) (selected : (observe left, observe right) ∈ problem) :
    Bounded (fun name => name ∈ active problem) binding.body := by
  intro identity present
  exact (mem_active identity problem).mpr ⟨_, selected,
    List.mem_append.mp (binding.body_covered identity present)⟩

theorem model_progress {Γ : Ctx S} {sort : S.Srt}
    {left right : Term (signature S source) Γ sort} (binding : Case left right)
    (rest : Problem source) (candidate : Assignment source next)
    (solved : Models candidate ((observe left, observe right) :: rest)) :
    Models candidate (mapProblem (answer binding) rest) ∧
      (∀ identity, candidate identity = instantiate candidate (answer binding identity)) ∧
      potential candidate (active (mapProblem (answer binding) rest)) <
        potential candidate (active ((observe left, observe right) :: rest)) := by
  let full := (observe left, observe right) :: rest
  have equation := observe_injective (solved _ List.mem_cons_self)
  have fixed := candidate_is_fixed binding candidate equation
  have components : ∀ identity, candidate identity = instantiate candidate (answer binding identity) :=
    fun identity => (congrFun fixed identity).symm
  have restSolved : Models candidate rest :=
    fun pair member => solved pair (List.mem_cons_of_mem _ member)
  refine ⟨(models_of_components candidate _ candidate components rest).mp restSolved, components, ?_⟩
  exact binding_active_potential_decreases binding.chosen binding.body rest (active full)
    (active_tail_subset _ rest) (body_is_covered binding full List.mem_cons_self) binding.absent
    (source_name_is_active binding full List.mem_cons_self) candidate

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingCaseProgress
