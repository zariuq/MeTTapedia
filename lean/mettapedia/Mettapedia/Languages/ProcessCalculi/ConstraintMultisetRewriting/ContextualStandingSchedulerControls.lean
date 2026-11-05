import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStandingScheduler
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStandingCodeControls

/-!
# Stored source code runs through the indexed wake/fairness interface

The queue holds installation 7. Its independent source admission constructs
an actual invocation, which consumes request 1, keeps the code and publishes
its result. The target has its actual new declaration family and scope epoch.
An old input-indexed commit cannot be replayed against that later world.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStandingScheduler.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualRuleCode
open ContextualRuleCode.Controls (DataOp dataSignature locals captures declarationWorld declaration picked entry_source_admitted)
open ContextualStandingEvents
open ContextualConditionalRows

local instance : DecidableEq dataSignature.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : dataSignature.Srt) : DecidableEq (dataSignature.Op sort) := inferInstanceAs (DecidableEq DataOp)

def world : World dataSignature () Nat [] :=
  ⟨Nat, locals, inferInstance, declarationWorld, declarationWorld.present, []⟩
def queued : State dataSignature () Nat [] := ⟨world, {7}⟩
def wakeIndex : Index (S := dataSignature) (atom := ()) (O := Nat) (Γ := []) := referenceIndex

theorem source_ready : Ready world 7 :=
  ⟨declaration, picked, entry_source_admitted, by decide +kernel, PropagationHistory.fresh_empty _⟩

theorem ready_has_only_the_installed_code (installation : Nat) (ready : Ready world installation) : installation = 7 := by
  by_contra other
  obtain ⟨body, selected, admitted, _, _⟩ := ready
  have decoded := ContextualStandingEntry.admitted_decodes locals declarationWorld installation body selected admitted
  change decodeDeclaration (ContextualStoredRows.asTemplate locals captures (declarationWorld.rows installation).value) = some body at decoded
  have plain : ContextualStoredRows.asTemplate locals captures (declarationWorld.rows installation).value =
      ContextualRuleCode.Controls.request (ContextualRuleCode.Controls.symbol (if installation = 0 then 1 else 2)) := by
    simp only [declarationWorld, ContextualRuleCode.Controls.declarationRows, other, if_false,
      ContextualRuleCode.Controls.rows, ContextualRuleCode.Controls.plainRows, ofStored, ContextualStoredRows.asTemplate]
    rfl
  rw [plain] at decoded
  cases decoded

theorem queued_invariant : WakeInv queued := by
  refine ⟨Finset.Subset.refl _, ?_⟩
  intro installation ready
  have only := ready_has_only_the_installed_code installation ready
  subst installation
  exact Set.mem_singleton 7

theorem source_readiness_enables_the_actual_queue_task :
    (system (referenceIndex (S := dataSignature) (atom := ()) (O := Nat) (Γ := []))).TaskEnabled (runTask 7) queued :=
  ready_task_enabled queued_invariant source_ready

theorem the_indexed_scheduler_runs_the_stored_declaration :
    ∃ invocation : Invocation world, invocation.installation = 7 ∧ invocation.fuel = 0 ∧
      Allowed queued (.commit world (.invoke invocation)) ∧
      invocation.target.current.present = {1, 7, 90} ∧ epoch world < epoch invocation.target := by
  obtain ⟨actual, budget⟩ := ContextualStandingEntry.realize locals declarationWorld 7 declaration picked entry_source_admitted 0
  let invocation : Invocation world := ⟨7, declaration, picked, actual⟩
  refine ⟨invocation, rfl, budget, ⟨rfl, ⟨?_, PropagationHistory.fresh_empty _⟩, rfl⟩, ?_, invocation.epoch_increases⟩
  · change Disjoint picked.made.toFinset declarationWorld.present
    decide +kernel
  · change actual.actual.firing.target.present = {1, 7, 90}
    rw [actual.actual.physical_result]
    decide +kernel

theorem an_old_input_index_is_not_a_commit_on_the_later_world
    (invocation : Invocation world) (awake : Set Nat) :
    ¬ Allowed (State.mk invocation.target awake) (.commit world (.invoke invocation)) := by
  intro allowed
  have same := congrArg epoch allowed.1
  exact (Nat.ne_of_lt invocation.epoch_increases) same.symm

theorem the_actual_source_commit_preserves_wake_coverage :
    ∃ invocation : Invocation world,
      Allowed queued (.commit world (.invoke invocation)) ∧
      WakeInv (next wakeIndex queued (.commit world (.invoke invocation))) ∧
      7 ∈ (next wakeIndex queued (.commit world (.invoke invocation))).awake ∧
      invocation.target.current.present = {1, 7, 90} := by
  obtain ⟨invocation, installation, _, allowed, physical, _⟩ :=
    the_indexed_scheduler_runs_the_stored_declaration
  refine ⟨invocation, allowed,
    wakeInv_next (index := wakeIndex) reference_no_lost_wakeup queued_invariant allowed, ?_, physical⟩
  refine ⟨?_, Or.inl (Set.mem_singleton 7)⟩
  exact installation ▸ invocation.installation_kept

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStandingScheduler.Controls
