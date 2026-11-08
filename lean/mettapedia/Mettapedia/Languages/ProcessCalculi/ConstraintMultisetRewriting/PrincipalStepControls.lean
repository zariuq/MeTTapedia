import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalChecksControls

/-!
# Principal firing controls retain counts, shared reads and output identity

Two reads share occurrence 1, while occurrences 1 and 4 have the same value.
The count is two physical occurrences. A principal answer preserves this
guard and the absence check. The wrong count is rejected before and after
instantiation. A separate producer shows why the original output-shape test
must survive even when instantiated output values become equal.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalStep.Controls

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ConstraintMultisetRewriting.Controls
  (signature A f label zero callRule callSelection call_valid call_has_principal_answer caller_binding_reaches_frame)

def initial : Configuration (Term signature) Nat := ⟨[], {0, 1, 4}⟩
def selected : Selection Nat := ⟨[0], [1, 1], [2]⟩
def rule : RuleInstance (Term signature) :=
  ⟨[f (.const 0)], [.var 0, .var 0], [], [.count (.var 0) 2, .absent (.const 9)], [.const 1]⟩

def problem : EquationStore (Term signature) := selected.problem label rule initial

theorem problem_models_iff (assignment : Subst signature) :
    A.Models assignment problem ↔
      A.Models assignment (callSelection.problem label callRule ConstraintMultisetRewriting.Controls.initial) := by
  simp [problem, Selection.problem, Selection.equations, selected, rule, initial,
    callSelection, callRule, ConstraintMultisetRewriting.Controls.initial, label,
    SubstitutionAction.Models, SubstitutionAction.Solves, FirstOrder.action]

theorem has_an_actual_principal_answer : ∃ answer, A.Principal problem answer := by
  obtain ⟨answer, principal⟩ := call_has_principal_answer
  exact ⟨answer, ⟨(problem_models_iff answer).mpr principal.sound,
    fun candidate solved => principal.factors candidate ((problem_models_iff candidate).mp solved)⟩⟩

theorem matching_region_contains_two_equal_valued_occurrences (assignment : Subst signature)
    (solved : A.Models assignment problem) :
    Check.matches A assignment label initial.present (.var 0) = {1, 4} := by
  classical
  have bound := caller_binding_reaches_frame assignment ((problem_models_iff assignment).mp solved)
  change assignment 0 = Term.const (σ := signature) 0 at bound
  ext occurrence
  constructor
  · intro member
    obtain ⟨present, same⟩ := Finset.mem_filter.mp member
    have cases : occurrence = 0 ∨ occurrence = 1 ∨ occurrence = 4 := by simpa [initial] using present
    rcases cases with rfl | rfl | rfl
    · change assignment 0 = f (assignment 0) at same
      rw [bound] at same
      cases same
    · simp
    · simp
  · intro member
    have cases : occurrence = 1 ∨ occurrence = 4 := by simpa using member
    rcases cases with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨by simp [initial], rfl⟩
    · exact Finset.mem_filter.mpr ⟨by simp [initial], rfl⟩

theorem count_two_holds (assignment : Subst signature) (solved : A.Models assignment problem) :
    (Check.count (.var 0) 2).Holds A assignment label initial.present := by
  change (Check.matches A assignment label initial.present (.var 0)).card = 2
  rw [matching_region_contains_two_equal_valued_occurrences assignment solved]
  decide

theorem absence_holds (assignment : Subst signature) (solved : A.Models assignment problem) :
    (Check.absent (.const 9)).Holds A assignment label initial.present := by
  have bound := caller_binding_reaches_frame assignment ((problem_models_iff assignment).mp solved)
  change assignment 0 = Term.const (σ := signature) 0 at bound
  intro occurrence present same
  have cases : occurrence = 0 ∨ occurrence = 1 ∨ occurrence = 4 := by simpa [initial] using present
  rcases cases with rfl | rfl | rfl
  · change Term.const (σ := signature) 9 = f (assignment 0) at same
    cases same
  · change Term.const (σ := signature) 9 = assignment 0 at same
    rw [bound] at same
    cases same
  · change Term.const (σ := signature) 9 = assignment 0 at same
    rw [bound] at same
    cases same

theorem ordinary_firing_is_valid : selected.Valid A label rule initial := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · obtain ⟨answer, principal⟩ := has_an_actual_principal_answer
    exact ⟨answer, principal.sound⟩
  · intro check member assignment solved
    change check ∈ [Check.count (.var 0) 2, .absent (.const 9)] at member
    rcases List.mem_cons.mp member with rfl | member
    · exact count_two_holds assignment solved
    · have same := List.mem_singleton.mp member
      subst check
      exact absence_holds assignment solved

def observed : List (Term signature) := [f (.var 0), .var 0, .const 9, .const 1]

theorem check_arguments_are_retained :
    ∀ check ∈ rule.checks, ∀ term ∈ check.terms, term ∈ observed := by
  intro check member term inTerms
  simp [rule] at member
  rcases member with rfl | rfl
  · have same := List.mem_singleton.mp inTerms
    subst term
    simp [observed]
  · have same := List.mem_singleton.mp inTerms
    subst term
    simp [observed]

theorem the_whole_observation_world_is_retained :
    ∀ occurrence ∈ initial.present, label occurrence ∈ observed := by
  intro occurrence member
  have cases : occurrence = 0 ∨ occurrence = 1 ∨ occurrence = 4 := by simpa [initial] using member
  rcases cases with rfl | rfl | rfl <;> simp [label, observed]

theorem an_actual_principal_answer_preserves_the_guarded_firing :
    ∃ answer, A.PrincipalOn problem answer observed ∧
      selected.Valid A (fun occurrence => A.apply answer (label occurrence))
        (rule.map (A.apply answer)) (SubstitutionStability.configuration A answer initial) := by
  obtain ⟨answer, principal⟩ := has_an_actual_principal_answer
  have interface := SubstitutionAction.Principal.on A principal observed
  refine ⟨answer, interface, (valid_iff A label interface ?_ ordinary_firing_is_valid.occurrences
    check_arguments_are_retained the_whole_observation_world_is_retained).mp ordinary_firing_is_valid⟩
  exact ⟨ordinary_firing_is_valid.take_distinct, ordinary_firing_is_valid.output_distinct,
    ordinary_firing_is_valid.take_length, ordinary_firing_is_valid.read_length, ordinary_firing_is_valid.outputs⟩

def wrongCount : RuleInstance (Term signature) := {rule with checks := [.count (.var 0) 1]}

theorem the_wrong_multiplicity_is_rejected : ¬ selected.Valid A label wrongCount initial := by
  intro valid
  obtain ⟨answer, principal⟩ := has_an_actual_principal_answer
  have one := valid.checks (.count (.var 0) 1) (by simp [wrongCount]) answer principal.sound
  have two := count_two_holds answer principal.sound
  change (Check.matches A answer label initial.present (.var 0)).card = 1 at one
  change (Check.matches A answer label initial.present (.var 0)).card = 2 at two
  omega

theorem principal_transport_also_rejects_the_wrong_multiplicity
    {answer : Subst signature} (principal : A.PrincipalOn problem answer observed) :
    ¬ selected.Valid A (fun occurrence => A.apply answer (label occurrence))
      (wrongCount.map (A.apply answer)) (SubstitutionStability.configuration A answer initial) := by
  intro valid
  apply the_wrong_multiplicity_is_rejected
  apply (valid_iff A label (rule := wrongCount) (selection := selected) (before := initial)
    principal ?_ ?_ ?_ the_whole_observation_world_is_retained).mpr valid
  · exact ⟨ordinary_firing_is_valid.take_distinct, ordinary_firing_is_valid.output_distinct,
      ordinary_firing_is_valid.take_length, ordinary_firing_is_valid.read_length, ordinary_firing_is_valid.outputs⟩
  · exact ordinary_firing_is_valid.occurrences
  · intro check member term inTerms
    have same := List.mem_singleton.mp member
    subst check
    have same := List.mem_singleton.mp inTerms
    subst term
    simp [observed]

def empty : Configuration (Term signature) Nat := ⟨[], ∅⟩
def producer : RuleInstance (Term signature) := ⟨[], [], [], [], [.var 0]⟩
def outputSelection : Selection Nat := ⟨[], [], [3]⟩

theorem substituted_outputs_can_hide_a_shape_failure :
    ¬ outputSelection.Valid A label producer empty ∧
      outputSelection.Valid A (fun occurrence => A.apply zero (label occurrence))
        (producer.map (A.apply zero)) (SubstitutionStability.configuration A zero empty) := by
  constructor
  · intro valid
    have same := valid.outputs
    change [Term.const (σ := signature) 0] = [Term.var (σ := signature) 0] at same
    cases same
  · refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ?_, ?_⟩
    · exact ⟨A.identity, A.models_nil A.identity⟩
    · intro check member
      cases member

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalStep.Controls
