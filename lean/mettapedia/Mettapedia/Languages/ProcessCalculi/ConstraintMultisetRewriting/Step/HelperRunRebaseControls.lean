import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperRebaseDomain
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperContextResultControls

/-!
# A complete local run executes beside an existing same-shape context

The consumer preserves a pre-existing helper valued forty-two while running
the two local helper declarations valued seven and eight. Their declaration
scopes remain separate, both physical output identities are retained and a
context occupying the first output makes the exact plan domain empty.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.RunRebaseControls

open Helpers.Consumer (tiny start first)

abbrev localRun := ResidualRunExchangeControls.twoStepRun
abbrev placed := ContextResultControls.placed

theorem second_native_admitted : helperStep.Admits
    (s := ContextResultControls.next.state)
    (ContextResultControls.next.leftFiring
      (ResidualRunExchangeControls.T.residual first ResidualRunExchangeControls.first_admitted
        Helpers.Consumer.second)) :=
  (ContextResultControls.next.admitted_left_iff _ ResidualRunExchangeControls.second_after_first).mpr
    ⟨ContextResultControls.fresh_and_context_remain_solvable, by decide⟩

def plan : RebasePlan tiny Nat placed localRun :=
  .cons (by simp [Firing.selection]) ContextResultControls.native_admitted
    (.cons (by simp [Firing.selection]) second_native_admitted (.nil _))

def realization : RunRealization placed localRun := RebasePlan.realize placed localRun plan

theorem actual_run_has_two_events : realization.execution.word.length = 2 := realization.length_preserved

theorem occurrence_ids_retained : realization.resultIso.rename = Equiv.refl Nat := rfl

theorem actual_resource_outputs : realization.execution.last.present = {1, 2} := by
  have preserved := realization.resultIso.present
  rw [occurrence_ids_retained] at preserved
  simp only [Equiv.refl_toEmbedding, Finset.map_refl] at preserved
  have expected : realization.target.state.present = {1, 2} := by
    change localRun.last.present ∪ ContextResultControls.context.present = {1, 2}
    decide +kernel
  exact preserved.trans expected

theorem complete_source_checks : RebaseChecks placed localRun := (rebase_plan_iff_checks placed localRun).mp ⟨plan⟩

theorem aggregate_domain_holds :
    (localRun.word = [] ∨ (Frames.contextual tiny).Solvable placed.state.knowledge) ∧
      OutputsAvoid localRun ContextResultControls.context.present :=
  (rebase_plan_iff_aggregate placed localRun).mp ⟨plan⟩

def occupiedContext : Helpers.State tiny Nat := { ContextResultControls.context with present := {1} }
abbrev occupied : ContextPlacement start occupiedContext :=
  ⟨placed.frame, placed.leftMap, placed.rightMap⟩

theorem occupied_context_has_no_plan : ¬Nonempty (RebasePlan tiny Nat occupied localRun) := by
  intro existsPlan
  have avoids := ((rebase_plan_iff_aggregate occupied localRun).mp existsPlan).2
  have fresh := avoids ⟨start, first⟩ (by simp [localRun, ResidualRunExchangeControls.twoStepRun, Step.Run.word])
  exact fresh (Finset.mem_singleton_self _)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.RunRebaseControls
