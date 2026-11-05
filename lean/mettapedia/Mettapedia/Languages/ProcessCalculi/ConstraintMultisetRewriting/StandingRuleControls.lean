import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StandingRuleMachine
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EquationWakeupControls

/-!
# An installed absence rule wakes on equations and survives its firing

The rule is a physical occurrence beside f(x). Telling x = 1 changes no
physical row, but makes the absence of f(0) certain. A physical-only wake
index misses this enabling. The reference index wakes it, and its actual
candidate firing keeps the installation while producing its answer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StandingRuleMachine.Controls

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness

abbrev signature := EquationWakeupControls.signature
abbrev A := EquationWakeupControls.A
abbrev x := EquationWakeupControls.x
abbrev f := EquationWakeupControls.f
abbrev zeroTerm := EquationWakeupControls.zeroTerm
abbrev oneTerm := EquationWakeupControls.oneTerm

def label (occurrence : Nat) : Term signature := if occurrence = 2 then .const 99 else EquationWakeupControls.label occurrence
def body := EquationWakeupControls.pending
def definition : StandingRuleRows.Definition (Term signature) := ⟨body, .perSelection⟩
def decode : Term signature → Option (StandingRuleRows.Definition (Term signature))
  | .const 99 => some definition
  | _ => none

def beforeWorld : Configuration (Term signature) Nat := ⟨[], {0, 2}⟩
def before : State (Term signature) Nat := ⟨beforeWorld, {0, 2}, [], ∅⟩
def tell := EquationWakeupControls.tell
def tellSelection := EquationWakeupControls.tellSelection
def tellFiring : ConditionalSchedule.Firing (Term signature) Nat := (tell, tellSelection)
def afterWorld := tellSelection.result label tell beforeWorld
def picked := EquationWakeupControls.pendingSelection

def beforeInstallation : State (Term signature) Nat := ⟨⟨[], {0}⟩, {0}, [], ∅⟩
def install : ConditionalSchedule.Firing (Term signature) Nat :=
  (StandingRuleRows.installRule label 2, StandingRuleRows.installSelection 2)

theorem installation_is_an_ordinary_allowed_firing : Allowed A label decode beforeInstallation (.env install) := by
  refine ⟨(StandingRuleRows.install_valid_iff A label 2 beforeInstallation.world).mpr ?_, by decide +kernel⟩
  exact ⟨by decide +kernel, ConstraintMultisetRewriting.Controls.zero, A.models_nil _⟩

theorem installing_really_produces_the_physical_rule :
    (next label decode (referenceIndex label) beforeInstallation (.env install)).world.present = {0, 2} := by
  decide +kernel

theorem tell_valid : tellSelection.Valid A label tell beforeWorld := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl, by decide +kernel, ?_, ?_⟩
  · refine ⟨ConstraintMultisetRewriting.Controls.one, ?_⟩
    intro equation member
    have only : equation = (x, oneTerm) := by
      simpa [Selection.problem, Selection.equations, tellSelection, tell, EquationWakeupControls.tellSelection,
        EquationWakeupControls.tell, beforeWorld] using member
    subst equation
    rfl
  · intro check member
    cases member

theorem body_cannot_fire_before (selection : Selection Nat) : ¬ selection.Valid A label body beforeWorld := by
  intro valid
  have noTake : selection.taken = [] := List.length_eq_zero_iff.mp valid.take_length.symm
  have noRead : selection.read = [] := List.length_eq_zero_iff.mp valid.read_length.symm
  have asked := valid.checks (.absent (f zeroTerm)) (by simp [body, EquationWakeupControls.pending])
  have held := asked ConstraintMultisetRewriting.Controls.zero (by
    simp [Selection.problem, Selection.equations, noTake, noRead, body, EquationWakeupControls.pending, beforeWorld])
  exact held 0 (by decide +kernel) rfl

theorem body_can_fire_after : picked.Valid A label body afterWorld := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl, by decide +kernel, ?_, ?_⟩
  · refine ⟨ConstraintMultisetRewriting.Controls.one, ?_⟩
    intro equation member
    have only : equation = (x, oneTerm) := by
      simpa [Selection.problem, Selection.equations, Selection.result, picked, body, afterWorld,
        EquationWakeupControls.pendingSelection, EquationWakeupControls.pending, tellSelection, tell,
        EquationWakeupControls.tellSelection, EquationWakeupControls.tell, beforeWorld] using member
    subst equation
    rfl
  · intro check member assignment model
    have only : check = .absent (f zeroTerm) := by simpa [body, EquationWakeupControls.pending] using member
    subst check
    have value := model (x, oneTerm) (by
      simp [Selection.problem, Selection.equations, Selection.result, picked, body, afterWorld,
        EquationWakeupControls.pendingSelection, EquationWakeupControls.pending, tellSelection, tell,
        EquationWakeupControls.tellSelection, EquationWakeupControls.tell, beforeWorld])
    change assignment 0 = Term.const (σ := signature) 1 at value
    intro occurrence present same
    have cases : occurrence = 0 ∨ occurrence = 2 := by
      simpa [afterWorld, Selection.result, fire, tellSelection, EquationWakeupControls.tellSelection, Selection.commit, beforeWorld] using present
    rcases cases with rfl | rfl
    · change f zeroTerm = f (assignment 0) at same
      have argument := congr_fun (eq_of_heq (Term.app.inj same).2) (0 : Fin 1)
      change zeroTerm = assignment 0 at argument
      rw [value] at argument
      cases argument
    · change f zeroTerm = Term.const (σ := signature) 99 at same
      cases same

theorem not_ready_before : ¬ Ready A label decode before 2 := by
  rintro ⟨declared, decoded, selected, valid, _, _⟩
  change some definition = some declared at decoded
  have only := Option.some.inj decoded
  subst declared
  exact body_cannot_fire_before selected ((StandingRuleRows.valid_iff A label 2 body selected beforeWorld).mp valid).2.2

theorem ready_after_equations : Ready A label decode (baseNext label before tellFiring []) 2 := by
  refine ⟨definition, rfl, picked, ?_, by decide +kernel, ?_⟩
  · exact (StandingRuleRows.valid_iff A label 2 body picked afterWorld).mpr
      ⟨by decide +kernel, by decide +kernel, body_can_fire_after⟩
  · exact PropagationHistory.fresh_empty _

def physicalIndex (world : Configuration (Term signature) Nat) (firing : ConditionalSchedule.Firing (Term signature) Nat) (_ : Nat) : Prop :=
  world.present ≠ (firing.2.result label firing.1 world).present

theorem a_physical_only_index_loses_the_installed_rule : ¬ NoLostWakeup A label decode physicalIndex := by
  intro adequate
  have notified := adequate before tellFiring tell_valid (by decide +kernel) []
    (by intro key member; cases member) 2 not_ready_before ready_after_equations
  exact notified rfl

def missed := next label decode physicalIndex before (.env tellFiring)

theorem the_physical_index_leaves_a_ready_rule_asleep : Ready A label decode missed 2 ∧ 2 ∉ missed.awake := by
  refine ⟨ready_after_equations, ?_⟩
  intro member
  change 2 ∈ afterWorld.present ∧ (2 ∈ (∅ : Set Nat) ∨ physicalIndex beforeWorld tellFiring 2) at member
  rcases member.2 with empty | notified
  · exact empty
  · exact notified rfl

theorem fairness_of_queued_tasks_cannot_repair_the_missing_wakeup :
    ¬ (system A label decode physicalIndex).TaskEnabled (runTask 2) missed := by
  rintro ⟨event, task, allowed⟩
  cases event with
  | env firing => cases task
  | run installation selected =>
      have only : installation = 2 := task
      subst installation
      obtain ⟨_, _, awake, _, _, _⟩ := allowed
      exact the_physical_index_leaves_a_ready_rule_asleep.2 awake
  | sleep installation => cases task
  | idle => cases task

theorem reference_index_sees_the_equation_change : referenceIndex label beforeWorld tellFiring 2 := by
  right
  decide +kernel

theorem initially_no_ready_rule (installation : Nat) : ¬ Ready A label decode before installation := by
  by_cases isRule : installation = 2
  · subst installation
    exact not_ready_before
  · rintro ⟨declared, decoded, _, _, _, _⟩
    by_cases isData : installation = 0
    · subst installation
      cases decoded
    · simp [decode, label, isRule, EquationWakeupControls.label, isData] at decoded

theorem initial_invariant : WakeInv A label decode before :=
  ⟨Finset.Subset.refl _, fun installation ready => False.elim (initially_no_ready_rule installation ready)⟩

def after : State (Term signature) Nat := next label decode (referenceIndex label) before (.env tellFiring)

theorem after_invariant : WakeInv A label decode after :=
  wakeInv_next A label decode (referenceIndex label) (reference_no_lost_wakeup A label decode) initial_invariant
    ⟨tell_valid, by decide +kernel⟩

theorem the_rule_is_actually_awake : 2 ∈ after.awake :=
  ⟨by decide +kernel, Or.inr reference_index_sees_the_equation_change⟩

theorem run_allowed : Allowed A label decode after (.run 2 picked) :=
  ⟨definition, rfl, the_rule_is_actually_awake,
    (StandingRuleRows.valid_iff A label 2 body picked afterWorld).mpr
      ⟨by decide +kernel, by decide +kernel, body_can_fire_after⟩,
    by decide +kernel, PropagationHistory.fresh_empty _⟩

def result := next label decode (referenceIndex label) after (.run 2 picked)

theorem the_actual_firing_keeps_the_rule_and_makes_the_answer :
    result.world.present = {0, 1, 2} ∧ 2 ∈ result.world.present ∧ result.history.length = 1 :=
  ⟨by decide +kernel, run_keeps_its_installation A label decode (referenceIndex label) run_allowed, rfl⟩

theorem a_refused_attempt_keeps_its_installation :
    let checking := {before with awake := ({2} : Set Nat)}
    Allowed A label decode checking (.sleep 2) ∧
      (next label decode (referenceIndex label) checking (.sleep 2)).world = beforeWorld ∧
      2 ∈ (next label decode (referenceIndex label) checking (.sleep 2)).world.present := by
  exact ⟨⟨rfl, not_ready_before⟩, rfl, by decide +kernel⟩

theorem changing_only_the_output_does_not_replay :
    ¬ Allowed A label decode result (.run 2 ⟨[], [], [3]⟩) := by
  rintro ⟨declared, decoded, _, _, _, fresh⟩
  change some definition = some declared at decoded
  have only := Option.some.inj decoded
  subst declared
  exact PropagationHistory.same_selection_cannot_replay
    (first := StandingRuleRows.event 2 .perSelection picked)
    (second := StandingRuleRows.event 2 .perSelection ⟨[], [], [3]⟩) rfl rfl rfl rfl rfl rfl [] fresh

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StandingRuleMachine.Controls
