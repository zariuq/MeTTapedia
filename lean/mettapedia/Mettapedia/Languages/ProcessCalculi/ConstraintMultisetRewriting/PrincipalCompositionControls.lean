import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalComposition
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalStepControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CompositionControls

/-!
# Conditional transport with shared reads and prefix-sensitive guards

The first step binds the selected call while two reads share occurrence 1.
The second step sees two remaining equal-valued occurrences and observes that
the consumed call is absent. The compiled conditional pair preserves admission
under its actual principal answer. A later binding cannot supply the principal
interface of an earlier empty equation prefix.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalComposition.Controls

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ConstraintMultisetRewriting.Controls (signature A f label zero caller_binding_reaches_frame)
open PrincipalStep.Controls (initial selected rule problem problem_models_iff has_an_actual_principal_answer ordinary_firing_is_valid)

def afterFirst := selected.result label rule initial
def right : Selection Nat := ⟨[], [], []⟩
def second : RuleInstance (Term signature) :=
  ⟨[], [], [], [.count (.var 0) 2, .absent (f (.const 0))], []⟩

theorem after_first_membership (occurrence : Nat) :
    occurrence ∈ afterFirst.present ↔ occurrence = 1 ∨ occurrence = 2 ∨ occurrence = 4 := by
  simp only [afterFirst, Selection.result, fire, Selection.commit, selected, initial]
  simp
  omega

theorem after_first_region (assignment : Subst signature) (solved : A.Models assignment problem) :
    Check.matches A assignment label afterFirst.present (.var 0) = {1, 4} := by
  classical
  have bound := caller_binding_reaches_frame assignment ((problem_models_iff assignment).mp solved)
  change assignment 0 = Term.const (σ := signature) 0 at bound
  ext occurrence
  constructor
  · intro member
    obtain ⟨present, same⟩ := Finset.mem_filter.mp member
    rcases (after_first_membership occurrence).mp present with rfl | rfl | rfl
    · simp
    · change assignment 0 = Term.const (σ := signature) 1 at same
      rw [bound] at same
      cases same
    · simp
  · intro member
    have choices : occurrence = 1 ∨ occurrence = 4 := by simpa using member
    rcases choices with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨(after_first_membership 1).mpr (by simp), rfl⟩
    · exact Finset.mem_filter.mpr ⟨(after_first_membership 4).mpr (by simp), rfl⟩

theorem second_firing_is_valid : right.Valid A label second afterFirst := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide,
    ordinary_firing_is_valid.consistent, ?_⟩
  intro check member assignment solved
  change A.Models assignment problem at solved
  change check ∈ [Check.count (.var 0) 2, .absent (f (.const 0))] at member
  rcases List.mem_cons.mp member with rfl | member
  · change (Check.matches A assignment label afterFirst.present (.var 0)).card = 2
    rw [after_first_region assignment solved]
    decide
  · have only := List.mem_singleton.mp member
    subst check
    have bound := caller_binding_reaches_frame assignment ((problem_models_iff assignment).mp solved)
    change assignment 0 = Term.const (σ := signature) 0 at bound
    intro occurrence present same
    rcases (after_first_membership occurrence).mp present with rfl | rfl | rfl
    · change f (.const 0) = assignment 0 at same
      rw [bound] at same
      cases same
    · change f (.const 0) = Term.const (σ := signature) 1 at same
      cases same
    · change f (.const 0) = assignment 0 at same
      rw [bound] at same
      cases same

def observed : List (Term signature) := PrincipalStep.Controls.observed ++ [f (.const 0)]

theorem second_arguments : ∀ check ∈ second.checks, ∀ term ∈ check.terms, term ∈ observed := by
  intro check member term inTerms
  simp [second] at member
  rcases member with rfl | rfl
  · have same := List.mem_singleton.mp inTerms
    subst term
    simp [observed, PrincipalStep.Controls.observed]
  · have same := List.mem_singleton.mp inTerms
    subst term
    simp [observed]

theorem second_values : ∀ occurrence ∈ afterFirst.present, label occurrence ∈ observed := by
  intro occurrence member
  rcases (after_first_membership occurrence).mp member with rfl | rfl | rfl <;>
    simp [observed, PrincipalStep.Controls.observed, label]

theorem a_principal_answer_preserves_the_conditional_pair :
    ∃ answer,
      (ConditionalComposite.compilePair label rule second selected right).Holds A label initial ∧
      (ConditionalComposite.compilePair (fun occurrence => A.apply answer (label occurrence))
        (rule.map (A.apply answer)) (second.map (A.apply answer)) selected right).Holds A
          (fun occurrence => A.apply answer (label occurrence))
          (SubstitutionStability.configuration A answer initial) := by
  obtain ⟨answer, principal⟩ := has_an_actual_principal_answer
  have interface := SubstitutionAction.Principal.on A principal observed
  have admitted := (ConditionalComposite.holds_pair_iff A label rule second selected right initial).mpr
    ⟨ordinary_firing_is_valid, second_firing_is_valid⟩
  refine ⟨answer, admitted, (pair_holds_iff A answer label rule second selected right initial observed observed
    interface interface ?_ ?_ ordinary_firing_is_valid.occurrences second_firing_is_valid.occurrences
      ?_ second_arguments ?_ second_values).mp admitted⟩
  · exact ⟨ordinary_firing_is_valid.take_distinct, ordinary_firing_is_valid.output_distinct,
      ordinary_firing_is_valid.take_length, ordinary_firing_is_valid.read_length, ordinary_firing_is_valid.outputs⟩
  · exact ⟨second_firing_is_valid.take_distinct, second_firing_is_valid.output_distinct,
      second_firing_is_valid.take_length, second_firing_is_valid.read_length, second_firing_is_valid.outputs⟩
  · intro check member term inTerms
    exact List.mem_append_left _ (PrincipalStep.Controls.check_arguments_are_retained check member term inTerms)
  · intro occurrence member
    exact List.mem_append_left _ (PrincipalStep.Controls.the_whole_observation_world_is_retained occurrence member)

/-- The final substitution makes this equation true, but cannot factor all
models of the earlier empty prefix on its retained guard terms. -/
theorem the_later_binding_is_not_principal_for_the_earlier_guard :
    ¬ A.PrincipalOn [] zero [Term.var 0, .const 0] := by
  intro principal
  have all : ∀ residual, (Check.equal (.var 0) (.const 0)).Holds A (A.compose residual zero) label ∅ := by
    intro residual
    rfl
  have unjustified := (SubstitutionAction.PrincipalOn.check_iff A principal label ∅
    (.equal (.var 0) (.const 0)) (by intro term member; exact member)
      (by intro occurrence member; cases member)).mpr all
  have contradiction := unjustified ConstraintMultisetRewriting.Controls.one
    (A.models_nil ConstraintMultisetRewriting.Controls.one)
  change Term.const (σ := signature) 1 = Term.const (σ := signature) 0 at contradiction
  cases contradiction

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalComposition.Controls
