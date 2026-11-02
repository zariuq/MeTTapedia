import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchedulePromotionRecovery
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchedulePromotionTransport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPathSnapshotControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionControls

/-!
# Conditional schedule certificates compose and retain their refusing guards

The positive certificate consists of explicit production and consumption
data, with actual solver receipts, and reconstructs the existing two-event
path. An unsupported guard can coexist with well-formed resource and solver
data; removing it changes acceptance even though output rows and equations
coincide. A genuine later tell does not repair an earlier retained question.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchedulePromotionControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualExecution ContextualSchedulePromotion
open ContextualWorldScopeLedger ContextualScopeSupport
open ContextualSelectionViews.Controls (base locals captures active atom p)
open ContextualGuardedStep.Controls (countRule equalityRule selection outputs)
open ContextualGuardedExecutionControls (initial)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)
local instance : Quiver (Endpoint locals Nat [] ()) := ContextualExecution.graph locals Nat

def production : Prepared locals initial where
  rule := countRule
  ruleCovered := ContextualGuardedExecutionControls.rule_covered
  selection := selection
  outputs := outputs
  formation := ⟨rfl, rfl, rfl⟩
  resources := ⟨⟨{7, 99}, by decide +kernel⟩, by decide +kernel⟩
  fuel := 0
  update := ContextualGuardedExecutionControls.update
  computed := rfl
  finished := rfl

theorem production_target_is_the_original_full_endpoint :
    production.target = ContextualGuardedExecutionControls.after := rfl

def consumption : Prepared locals production.target where
  rule := ContextualPathSnapshotControls.consumeRule
  ruleCovered := ContextualPathSnapshotControls.consumeRule_covered
  selection := ContextualPathSnapshotControls.consume
  outputs := ContextualPathSnapshotControls.consumeOutputs
  formation := ⟨rfl, rfl, rfl⟩
  resources := ⟨⟨{7}, by decide +kernel⟩, by decide +kernel⟩
  fuel := 1
  update := ContextualPathSnapshotControls.consumeUpdate
  computed := ContextualPathSnapshotControls.consume_computed
  finished := rfl

def firstCertificate : Certificate locals initial production.target := .snoc (.nil initial) production
def secondCertificate : Certificate locals production.target consumption.target :=
  .snoc (.nil production.target) consumption
def combinedCertificate : Certificate locals initial consumption.target :=
  firstCertificate.append secondCertificate

theorem production_checks : Checked locals production.questions := by
  intro question member
  obtain ⟨check, present, rfl⟩ := List.mem_map.mp member
  exact ContextualGuardedExecutionControls.admitted.checks check present

theorem consumption_checks : Checked locals consumption.questions := by
  intro question member
  cases member

theorem first_checked : Checked locals firstCertificate.questions := by
  exact (checked_append_iff locals [] production.questions).mpr
    ⟨(by intro question member; cases member), production_checks⟩

theorem second_checked : Checked locals secondCertificate.questions := by
  exact (checked_append_iff locals [] consumption.questions).mpr
    ⟨(by intro question member; cases member), consumption_checks⟩

theorem combined_checked : Checked locals combinedCertificate.questions :=
  (Certificate.checked_append firstCertificate secondCertificate).mpr ⟨first_checked, second_checked⟩

theorem actual_composition_and_full_endpoint :
    Nonempty (Quiver.Path initial ContextualPathSnapshotControls.final) ∧
      ContextualExecution.selections (combinedCertificate.realize combined_checked) =
        [selection, ContextualPathSnapshotControls.consume] ∧
      ContextualExecution.fuels (combinedCertificate.realize combined_checked) = [0, 1] ∧
      consumption.target.inventory.configuration.present = {7} ∧
      combinedCertificate.questions.length = 1 := by
  refine ⟨⟨combinedCertificate.realize combined_checked⟩, ?_, ?_, by decide +kernel, rfl⟩
  · exact Certificate.realize_selections combinedCertificate combined_checked
  · exact Certificate.realize_fuels combinedCertificate combined_checked

theorem realization_composes_as_the_original_paths :
    combinedCertificate.realize combined_checked =
      (firstCertificate.realize first_checked).comp (secondCertificate.realize second_checked) :=
  Certificate.realize_append firstCertificate secondCertificate first_checked second_checked

theorem the_original_guard_keeps_its_preproduction_world :
    (production.questionAt (.count (p (atom active)) 1)
      (secondCertificate.realize second_checked)).world = {7} ∧
      production.target.inventory.configuration.present = {7, 99} := ⟨rfl, by decide +kernel⟩

theorem unsupported_rule_covered :
    RuleCovered (privateScopes initial.scopes) initial.occupied equalityRule := by
  apply (ruleRoots_covered_iff (privateScopes initial.scopes) initial.occupied equalityRule).mp
  decide +kernel

def unsupported : Prepared locals initial where
  rule := equalityRule
  ruleCovered := unsupported_rule_covered
  selection := selection
  outputs := outputs
  formation := ⟨rfl, rfl, rfl⟩
  resources := ⟨⟨{7, 99}, by decide +kernel⟩, by decide +kernel⟩
  fuel := 0
  update := ContextualGuardedExecutionControls.update
  computed := rfl
  finished := rfl

theorem unsupported_guard_is_retained_and_refuses :
    unsupported.questions.length = 1 ∧ ¬ Checked locals unsupported.questions := by
  refine ⟨rfl, ?_⟩
  intro accepted
  exact ContextualGuardedExecutionControls.the_unsupported_guard_cannot_be_admitted
    (unsupported.admission accepted)

def strippedRule := { equalityRule with checks := [] }

theorem stripped_rule_covered :
    RuleCovered (privateScopes initial.scopes) initial.occupied strippedRule := by
  apply (ruleRoots_covered_iff (privateScopes initial.scopes) initial.occupied strippedRule).mp
  decide +kernel

def stripped : Prepared locals initial where
  rule := strippedRule
  ruleCovered := stripped_rule_covered
  selection := selection
  outputs := outputs
  formation := ⟨rfl, rfl, rfl⟩
  resources := ⟨⟨{7, 99}, by decide +kernel⟩, by decide +kernel⟩
  fuel := 0
  update := ContextualGuardedExecutionControls.update
  computed := rfl
  finished := rfl

theorem deleting_a_guard_changes_acceptance_despite_equal_visible_results :
    ¬ Checked locals unsupported.questions ∧ Checked locals stripped.questions ∧
      unsupported.target.inventory.configuration = stripped.target.inventory.configuration ∧
      unsupported.target.inventory.rows = stripped.target.inventory.rows ∧
      unsupported.rule.produce = stripped.rule.produce := by
  refine ⟨unsupported_guard_is_retained_and_refuses.2, ?_, rfl, rfl, rfl⟩
  intro question member
  cases member

def earlierQuestion : Question locals (O := Nat) [] () where
  Names := Nat
  declarations := captures
  equations := initial.inventory.configuration.equations
  rows := initial.inventory.rows
  world := initial.inventory.configuration.present
  check := .equal (generator captures 0) (atom captures)

theorem actual_later_tell_cannot_accept_an_earlier_question :
    ∃ target : Endpoint locals Nat [] (), ∃ path : Quiver.Path initial target,
      ¬ (earlierQuestion.map (pathAssignment path)).Holds locals ∧
      ContextualGuardSemantics.Ask locals target.inventory.configuration.equations target.inventory.rows
        target.inventory.configuration.present
        (earlierQuestion.check.map (instantiate (pathAssignment path))) ∧
      ∃ certificate : Certificate locals initial target,
        Checked locals certificate.questions ∧
        ¬ Checked locals (earlierQuestion :: certificate.questions) := by
  obtain ⟨target, edge, _rule, _selection, path, _one, _selected, refused, after⟩ :=
    ContextualPathSnapshotControls.actual_later_tell_does_not_discharge_the_retained_prefix_question
  obtain ⟨certificate, checked, _selections, _fuels⟩ := Certificate.recover path
  refine ⟨target, path, refused, after, certificate, checked, ?_⟩
  intro accepted
  exact ContextualPathSnapshotControls.original_caller_question_unentailed
    (accepted earlierQuestion List.mem_cons_self)

/-- A computed two-use schema activation survives recovery with both physical
read ports intact. The solver really returns after its six-step budget. -/
theorem actual_shared_schema_reads_survive_certificate_recovery :
    ∃ target : Endpoint locals Nat [] (),
      ∃ certificate : Certificate locals ContextualExecutionControls.initial target,
        Checked locals certificate.questions ∧
        ∃ picked : Selection Nat, certificate.selections = [picked] ∧ picked.read = [7, 7] ∧
          certificate.fuels = [6] ∧ target.inventory.configuration.present = {7, 8, 99} := by
  obtain ⟨target, edge, shared, fuel, present, _ledger, _path, _selected⟩ :=
    ContextualExecutionControls.actual_shared_schema_path
  obtain ⟨certificate, checked, selected, spent⟩ := Certificate.recover (Quiver.Hom.toPath edge)
  have fuelList : certificate.fuels = [edge.fuel] := spent
  rw [fuel] at fuelList
  exact ⟨target, certificate, checked, edge.selection, selected, shared, fuelList, present⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchedulePromotionControls
