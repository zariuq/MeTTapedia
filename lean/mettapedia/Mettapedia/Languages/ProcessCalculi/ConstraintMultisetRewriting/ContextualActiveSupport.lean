import Mettapedia.OSLF.Syntax.ContextualSupportSubstitution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualResidual
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBinding
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite active declarations and binding progress in an arbitrary family

The roster is computed from the actual equation terms. A valid binding
introduces no declaration outside that roster and removes its selected name
from every remaining equation. The sum of finite candidate-image sizes on
the resulting roster strictly decreases. The ambient declaration carrier
itself need not be finite, and no completeness claim is assumed here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActiveSupport

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open scoped BigOperators

variable {S : Signature} {V W : Type} [DecidableEq V] [DecidableEq W]
  {source : V → MetaArity S} {target : W → MetaArity S}

def observationNames (observation : Observation S source) : List V := support observation.2.2

def active (problem : Problem source) : Finset V :=
  (problem.flatMap fun equation => observationNames equation.1 ++ observationNames equation.2).toFinset

theorem mem_active (identity : V) (problem : Problem source) :
    identity ∈ active problem ↔
      ∃ equation ∈ problem, identity ∈ observationNames equation.1 ∨ identity ∈ observationNames equation.2 := by
  simp [active]

theorem map_active_subset (assignment : Assignment source target) (problem : Problem source)
    (before : Finset V) (after : Finset W) (covered : active problem ⊆ before)
    (images : ∀ identity ∈ before, Bounded (fun name => name ∈ after) (assignment identity)) :
    active (mapProblem assignment problem) ⊆ after := by
  intro identity present
  obtain ⟨equation, member, inside⟩ := (mem_active identity _).mp present
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  rcases original with ⟨⟨Γ, sort, left⟩, ⟨Δ, result, right⟩⟩
  cases inside with
  | inl first =>
      apply bounded_instantiate (fun name => name ∈ after) assignment left ?_ identity first
      intro name named
      exact images name (covered ((mem_active name _).mpr
        ⟨_, originalMember, .inl named⟩))
  | inr second =>
      apply bounded_instantiate (fun name => name ∈ after) assignment right ?_ identity second
      intro name named
      exact images name (covered ((mem_active name _).mpr
        ⟨_, originalMember, .inr named⟩))

omit [DecidableEq W] in
theorem binding_images_erase (chosen : V)
    (body : Term (signature S source) (source chosen).1 (source chosen).2)
    (roster : Finset V) (bodyCovered : Bounded (fun name => name ∈ roster) body)
    (absent : chosen ∉ support body) :
    ∀ identity ∈ roster,
      Bounded (fun name => name ∈ roster.erase chosen) (ContextualBinding.answer chosen body identity) := by
  intro identity present
  by_cases same : identity = chosen
  · subst identity
    rw [ContextualBinding.answer_same]
    intro name named
    exact Finset.mem_erase.mpr ⟨fun equal => absent (equal ▸ named), bodyCovered name named⟩
  · rw [ContextualBinding.answer_other chosen identity same body]
    intro name named
    rw [support_generator, List.mem_singleton] at named
    subst name
    exact Finset.mem_erase.mpr ⟨same, present⟩

omit [DecidableEq W] in
theorem binding_removes_selected_name (chosen : V)
    (body : Term (signature S source) (source chosen).1 (source chosen).2)
    (problem : Problem source) (roster : Finset V) (covered : active problem ⊆ roster)
    (bodyCovered : Bounded (fun name => name ∈ roster) body) (absent : chosen ∉ support body) :
    active (mapProblem (ContextualBinding.answer chosen body) problem) ⊆ roster.erase chosen :=
  map_active_subset _ problem roster (roster.erase chosen) covered
    (binding_images_erase chosen body roster bodyCovered absent)

def potential (candidate : Assignment source target) (roster : Finset V) : Nat :=
  ∑ identity ∈ roster, termSize (candidate identity)

omit [DecidableEq V] [DecidableEq W] in
theorem potential_monotone (candidate : Assignment source target) {small large : Finset V}
    (included : small ⊆ large) : potential candidate small ≤ potential candidate large :=
  Finset.sum_le_sum_of_subset included

omit [DecidableEq W] in
theorem potential_erase_lt (candidate : Assignment source target) (roster : Finset V)
    (chosen : V) (present : chosen ∈ roster) :
    potential candidate (roster.erase chosen) < potential candidate roster := by
  have split := Finset.sum_erase_add roster (fun identity => termSize (candidate identity)) present
  have positive := termSize_pos (candidate chosen)
  unfold potential
  omega

omit [DecidableEq W] in
theorem binding_active_potential_decreases (chosen : V)
    (body : Term (signature S source) (source chosen).1 (source chosen).2)
    (problem : Problem source) (roster : Finset V) (covered : active problem ⊆ roster)
    (bodyCovered : Bounded (fun name => name ∈ roster) body)
    (absent : chosen ∉ support body) (present : chosen ∈ roster)
    (candidate : Assignment source target) :
    potential candidate (active (mapProblem (ContextualBinding.answer chosen body) problem)) <
      potential candidate roster :=
  lt_of_le_of_lt (potential_monotone candidate
    (binding_removes_selected_name chosen body problem roster covered bodyCovered absent))
    (potential_erase_lt candidate roster chosen present)

omit [DecidableEq W] in
theorem active_tail_subset (equation : Equation (Observation S source)) (rest : Problem source) :
    active rest ⊆ active (equation :: rest) := by
  intro identity present
  obtain ⟨selected, member, inside⟩ := (mem_active identity rest).mp present
  exact (mem_active identity _).mpr ⟨selected, List.mem_cons_of_mem equation member, inside⟩

omit [DecidableEq W] in
theorem binding_prefix_progress (chosen : V)
    (body : Term (signature S source) (source chosen).1 (source chosen).2)
    (rest : Problem source) (absent : chosen ∉ support body)
    (candidate : Assignment source target)
    (solved : Models candidate ((observe (generator source chosen), observe body) :: rest)) :
    ∃ residual : Assignment source target,
      Models residual (mapProblem (ContextualBinding.answer chosen body) rest) ∧
      (∀ identity, candidate identity = instantiate residual (ContextualBinding.answer chosen body identity)) ∧
      potential residual (active (mapProblem (ContextualBinding.answer chosen body) rest)) <
        potential candidate (active ((observe (generator source chosen), observe body) :: rest)) := by
  let full := (observe (generator source chosen), observe body) :: rest
  have equation := observe_injective (solved _ List.mem_cons_self)
  rw [instantiate_generator] at equation
  have components := ContextualBinding.candidate_factors chosen body candidate equation
  have restSolved : Models candidate rest :=
    fun pair member => solved pair (List.mem_cons_of_mem _ member)
  refine ⟨candidate,
    (models_of_components candidate _ candidate (fun identity => congrFun components identity) rest).mp restSolved,
    (fun identity => congrFun components identity), ?_⟩
  apply binding_active_potential_decreases chosen body rest (active full)
    (active_tail_subset _ rest) ?_ absent ?_ candidate
  · intro identity named
    exact (mem_active identity full).mpr ⟨_, List.mem_cons_self, .inr named⟩
  · apply (mem_active chosen full).mpr
    refine ⟨_, List.mem_cons_self, .inl ?_⟩
    change chosen ∈ support (generator source chosen)
    simp only [support_generator, List.mem_singleton]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActiveSupport
