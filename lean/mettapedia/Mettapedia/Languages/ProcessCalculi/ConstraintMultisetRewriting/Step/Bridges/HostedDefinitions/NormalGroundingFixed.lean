import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.SourceProgressControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RuntimeSubstitution

/-! # Dependency licences checked on the actual fixed and helper equations -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalGroundingFixed

open SourceLanguage.Elaboration
open RuleBuilder

theorem all_paths {slots : Nat} (lhs rhs : Template slots)
    (checked : LiteralPaths.pathsChecked lhs = true) : GroundRead.Grounding (equation lhs rhs) := by
  apply GroundRead.equation_grounding
  unfold GroundRead.rhsPathsChecked
  apply List.all_eq_true.mpr
  intro index _
  exact List.all_eq_true.mp checked index (by simp)

theorem traversal : ∀ rule ∈ ContextRules.traversal, GroundRead.Grounding rule := by
  intro rule member
  obtain ⟨index, selected⟩ := List.mem_iff_get.mp member
  rw [← selected]
  fin_cases index
  all_goals apply all_paths
  all_goals decide +kernel

theorem primitive : ∀ rule ∈ ContextRules.primitive, GroundRead.Grounding rule := by
  intro rule member
  obtain ⟨index, selected⟩ := List.mem_iff_get.mp member
  rw [← selected]
  fin_cases index
  all_goals apply all_paths
  all_goals decide +kernel

theorem driver_prefix : ∀ rule ∈ ContextRules.driver.take 4, GroundRead.Grounding rule := by
  intro rule member
  obtain ⟨index, selected⟩ := List.mem_iff_get.mp member
  rw [← selected]
  fin_cases index
  all_goals apply all_paths
  all_goals decide +kernel

theorem fixed : ∀ rule ∈ ContextRules.fixed, GroundRead.Grounding rule := by
  intro rule member
  rcases List.mem_append.mp member with contexts | driver
  · rcases List.mem_append.mp contexts with outer | root
    · exact traversal rule outer
    · exact primitive rule root
  · rw [← List.take_append_drop 4 ContextRules.driver] at driver
    rcases List.mem_append.mp driver with early | worker
    · exact driver_prefix rule early
    · exact SourceProgressControls.actual_worker_grounding rule worker

theorem helpers : ∀ rule ∈ RuntimeSubstitution.rules, GroundRead.Grounding rule := by
  intro rule member
  obtain ⟨index, selected⟩ := List.mem_iff_get.mp member
  rw [← selected]
  fin_cases index
  all_goals apply all_paths
  all_goals decide +kernel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalGroundingFixed

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalGroundingFixed.fixed
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalGroundingFixed.helpers
