import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Controls

/-!
# Substitution of the whole symbolic configuration

Substitution acts on both sides of equations, selected occurrences, outputs
and check arguments. Certain checks are preserved by this action. Execution
additionally requires the instantiated equations to remain consistent: a
substitution that contradicts an already required binding is not admissible.

The substitution action supplies capture avoidance in binding-tree profiles.
No claim is made for substituting only a rule while leaving its shared frame
or retained checks behind.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SubstitutionStability

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

def configuration (A : SubstitutionAction T S) (θ : S) (before : Configuration T O) :
    Configuration T O := ⟨A.applyStore θ before.equations, before.present⟩

omit [DecidableEq O] in
theorem problem_map (A : SubstitutionAction T S) (θ : S) (label : O → T)
    (rule : RuleInstance T) (selection : Selection O) (before : Configuration T O) :
    selection.problem (fun o => A.apply θ (label o)) (rule.map (A.apply θ))
      (configuration A θ before) = A.applyStore θ (selection.problem label rule before) := by
  simp only [Selection.problem, Selection.equations, configuration, RuleInstance.map,
    SubstitutionAction.applyStore, List.map_append, List.zipWith_map_left, List.map_zipWith]

omit [DecidableEq O] in
private theorem region_map (A : SubstitutionAction T S) (outer inner : S) (label : O → T)
    (world : Finset O) (pattern : T) :
    Check.matches A outer (fun o => A.apply inner (label o)) world (A.apply inner pattern) =
      Check.matches A (A.compose outer inner) label world pattern := by
  classical
  ext o
  simp only [Check.matches, Finset.mem_filter, A.apply_compose]

omit [DecidableEq O] in
theorem check_map (A : SubstitutionAction T S) (outer inner : S) (label : O → T)
    (world : Finset O) (check : Check T) :
    (check.map (A.apply inner)).Holds A outer (fun o => A.apply inner (label o)) world ↔
      check.Holds A (A.compose outer inner) label world := by
  cases check with
  | equal _ _ => simp only [Check.map, Check.Holds, SubstitutionAction.Solves, A.apply_compose]
  | absent _ => simp only [Check.map, Check.Holds, A.apply_compose]
  | count _ _ => simp only [Check.map, Check.Holds, region_map]

theorem valid_map (A : SubstitutionAction T S) (θ : S) (label : O → T)
    {rule : RuleInstance T} {selection : Selection O} {before : Configuration T O}
    (valid : selection.Valid A label rule before)
    (compatible : A.Consistent (A.applyStore θ (selection.problem label rule before))) :
    selection.Valid A (fun o => A.apply θ (label o)) (rule.map (A.apply θ))
      (configuration A θ before) := by
  refine ⟨valid.take_distinct, valid.output_distinct, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [RuleInstance.map, List.length_map] using valid.take_length
  · simpa only [RuleInstance.map, List.length_map] using valid.read_length
  · simpa only [RuleInstance.map, List.map_map, Function.comp_def] using
      congrArg (List.map (A.apply θ)) valid.outputs
  · exact ⟨valid.occurrences.taken_subset, valid.occurrences.kept_subset,
      valid.occurrences.apart, valid.occurrences.fresh, by simp [Selection.commit]⟩
  · simpa only [problem_map] using compatible
  · intro check member σ solved
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    rw [problem_map] at solved
    have originalModels := (A.models_applyStore σ θ (selection.problem label rule before)).mp solved
    exact (check_map A σ θ label before.present original).mpr
      (valid.checks original present (A.compose σ θ) originalModels)

theorem result_map (A : SubstitutionAction T S) (θ : S) (label : O → T)
    (rule : RuleInstance T) (selection : Selection O) (before : Configuration T O) :
    selection.result (fun o => A.apply θ (label o)) (rule.map (A.apply θ))
      (configuration A θ before) = configuration A θ (selection.result label rule before) := by
  apply congrArg₂ Configuration.mk
  · exact problem_map A θ label rule selection before
  · rfl

/-- Actual two-sided steps are stable under compatible substitution of all
shared terms and conditions, with the same occurrence choices. -/
theorem step_map (A : SubstitutionAction T S) (θ : S) (label : O → T)
    (rule : RuleInstance T) {before after : Configuration T O}
    (step : Step A label rule before after)
    (compatible : A.Consistent (A.applyStore θ after.equations)) :
    Step A (fun o => A.apply θ (label o)) (rule.map (A.apply θ))
      (configuration A θ before) (configuration A θ after) := by
  obtain ⟨selection, valid, rfl⟩ := step
  exact ⟨selection, valid_map A θ label valid compatible,
    (result_map A θ label rule selection before).symm⟩

namespace Controls

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Controls

/-- Scope-correct substitution alone cannot override a conflicting input
binding: the instantiated call still has to satisfy its equations. -/
theorem conflicting_call_substitution_is_inconsistent :
    ¬ A.Consistent (A.applyStore one (callSelection.problem label callRule initial)) := by
  rintro ⟨σ, solved⟩
  have original := (A.models_applyStore σ one (callSelection.problem label callRule initial)).mp solved
  have conflict := caller_binding_reaches_frame (Mettapedia.Logic.LP.Subst.comp σ one) original
  change (Mettapedia.Logic.LP.Term.const (σ := signature) 1) = .const 0 at conflict
  cases conflict

end Controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SubstitutionStability
