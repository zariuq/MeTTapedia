import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CheckFreeInstanceLifting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalStepControls

/-!
# Existing LP-term controls separate check-free lifting from guarded promotion

Each guarded separator publishes a real fresh output and retains its original
made-label agreement. The failure is its universal source check, not an arity,
output-shape, resource or newly invented syntax issue. The existing producer
counterexample independently shows why base made labels cannot be omitted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InstanceLiftingControls

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Controls
  (signature A zero one callRule callSelection label initial call_valid)

def guardLabel (occurrence : Nat) : Term signature :=
  if occurrence = 0 then .const 0 else .const 1

def guardWorld : Configuration (Term signature) Nat := ⟨[], {0}⟩
def makeOutput : Selection Nat := ⟨[], [], [2]⟩

def guarded (check : Check (Term signature)) : RuleInstance (Term signature) :=
  ⟨[], [], [], [check], [.const 1]⟩

theorem original_made_labels (check : Check (Term signature)) :
    makeOutput.made.map guardLabel = (guarded check).produce := rfl

private theorem image_valid_of_check (instance_ : Subst signature) (check : Check (Term signature))
    (holds : ∀ residual, (check.map (A.apply instance_)).Holds A residual
      (fun occurrence => A.apply instance_ (guardLabel occurrence)) guardWorld.present) :
    makeOutput.Valid A (fun occurrence => A.apply instance_ (guardLabel occurrence))
      ((guarded check).map (A.apply instance_)) (SubstitutionStability.configuration A instance_ guardWorld) := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · exact ⟨by simp [Selection.commit, makeOutput], by simp [Selection.commit, makeOutput],
      by simp [Selection.commit, makeOutput], by simp [Selection.commit, makeOutput,
        SubstitutionStability.configuration, guardWorld], by simp [Selection.commit]⟩
  · refine ⟨A.identity, ?_⟩
    intro equation member
    simp [Selection.problem, Selection.equations, SubstitutionStability.configuration,
      RuleInstance.map, makeOutput, guardWorld, guarded, SubstitutionAction.applyStore] at member
  · intro queried member residual _
    have same : queried = check.map (A.apply instance_) := by
      simpa only [guarded, RuleInstance.map, List.map_singleton, List.mem_singleton] using member
    subst queried
    exact holds residual

def equalityCheck : Check (Term signature) := .equal (.var 0) (.const 0)
def absenceCheck : Check (Term signature) := .absent (.var 0)
def countCheck : Check (Term signature) := .count (.var 0) 1

theorem equality_instance_valid :
    makeOutput.Valid A (fun occurrence => A.apply zero (guardLabel occurrence))
      ((guarded equalityCheck).map (A.apply zero)) (SubstitutionStability.configuration A zero guardWorld) :=
  image_valid_of_check zero equalityCheck (by intro residual; rfl)

theorem equality_source_refused : ¬ makeOutput.Valid A guardLabel (guarded equalityCheck) guardWorld := by
  intro valid
  have asked := valid.checks equalityCheck (by simp [guarded]) one (by
    intro equation member
    simp [Selection.problem, Selection.equations, makeOutput, guardWorld, guarded] at member)
  change Term.const (σ := signature) 1 = .const 0 at asked
  cases asked

theorem absence_instance_valid :
    makeOutput.Valid A (fun occurrence => A.apply one (guardLabel occurrence))
      ((guarded absenceCheck).map (A.apply one)) (SubstitutionStability.configuration A one guardWorld) := by
  apply image_valid_of_check one absenceCheck
  intro residual occurrence present same
  have atZero : occurrence = 0 := by simpa [guardWorld] using present
  subst occurrence
  change Term.const (σ := signature) 1 = .const 0 at same
  cases same

theorem absence_source_refused : ¬ makeOutput.Valid A guardLabel (guarded absenceCheck) guardWorld := by
  intro valid
  have asked := valid.checks absenceCheck (by simp [guarded]) zero (by
    intro equation member
    simp [Selection.problem, Selection.equations, makeOutput, guardWorld, guarded] at member)
  exact asked 0 (by simp [guardWorld]) rfl

theorem count_instance_valid :
    makeOutput.Valid A (fun occurrence => A.apply zero (guardLabel occurrence))
      ((guarded countCheck).map (A.apply zero)) (SubstitutionStability.configuration A zero guardWorld) := by
  apply image_valid_of_check zero countCheck
  intro residual
  change (Check.matches A residual (fun occurrence => A.apply zero (guardLabel occurrence))
    guardWorld.present (A.apply zero (.var 0))).card = 1
  have region : Check.matches A residual (fun occurrence => A.apply zero (guardLabel occurrence))
      guardWorld.present (A.apply zero (.var 0)) = {0} := by
    classical
    ext occurrence
    simp only [Check.matches, Finset.mem_filter]
    constructor
    · exact fun member => by simpa [guardWorld] using member.1
    · intro member
      have atZero : occurrence = 0 := by simpa using member
      subst occurrence
      exact ⟨by simp [guardWorld], rfl⟩
  rw [region]
  decide

theorem count_source_refused : ¬ makeOutput.Valid A guardLabel (guarded countCheck) guardWorld := by
  intro valid
  have asked := valid.checks countCheck (by simp [guarded]) one (by
    intro equation member
    simp [Selection.problem, Selection.equations, makeOutput, guardWorld, guarded] at member)
  have region : Check.matches A one guardLabel guardWorld.present (.var 0) = ∅ := by
    classical
    ext occurrence
    constructor
    · intro member
      obtain ⟨present, same⟩ := Finset.mem_filter.mp member
      have atZero : occurrence = 0 := by simpa [guardWorld] using present
      subst occurrence
      change Term.const (σ := signature) 1 = .const 0 at same
      cases same
    · intro member
      cases member
  change (Check.matches A one guardLabel guardWorld.present (.var 0)).card = 1 at asked
  simp [region] at asked

theorem check_free_nonidentity_instance_lifts :
    callSelection.Valid A (fun occurrence => A.apply zero (label occurrence))
      (callRule.map (A.apply zero)) (SubstitutionStability.configuration A zero initial) ∧
      callSelection.Valid A label callRule initial := by
  have sourceSolved : A.Models zero (callSelection.problem label callRule initial) := by
    intro equation member
    have same : equation = (Controls.f (.const 0), Controls.f (.var 0)) := by
      simpa [Selection.problem, Selection.equations, callSelection, callRule, initial, label] using member
    subst equation
    rfl
  have compatible : A.Consistent (A.applyStore zero (callSelection.problem label callRule initial)) :=
    ⟨A.identity, (A.models_applyStore A.identity zero _).mpr (A.models_compose sourceSolved A.identity)⟩
  have instanceValid := (CheckFreeInstanceLifting.valid_instance_iff A zero callSelection label callRule initial
    rfl call_valid.outputs).mpr ⟨call_valid, compatible⟩
  exact ⟨instanceValid, CheckFreeInstanceLifting.lift_instance A zero callSelection label callRule initial
    rfl call_valid.outputs instanceValid⟩

/-- Check-freeness does not repair a source output mismatch hidden by a
noninjective substitution; the original made-label premise is necessary. -/
theorem original_made_label_premise_is_necessary :
    PrincipalStep.Controls.producer.checks = [] ∧
      ¬ PrincipalStep.Controls.outputSelection.Valid A label PrincipalStep.Controls.producer PrincipalStep.Controls.empty ∧
      PrincipalStep.Controls.outputSelection.Valid A (fun occurrence => A.apply zero (label occurrence))
        (PrincipalStep.Controls.producer.map (A.apply zero))
        (SubstitutionStability.configuration A zero PrincipalStep.Controls.empty) :=
  ⟨rfl, PrincipalStep.Controls.substituted_outputs_can_hide_a_shape_failure⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InstanceLiftingControls
