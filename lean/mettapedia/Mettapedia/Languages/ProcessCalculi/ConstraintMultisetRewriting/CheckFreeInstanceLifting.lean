import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SubstitutionStability

/-!
# Exact lifting of check-free instances, retaining original made labels

Instantiation reuses the existing whole-configuration substitution. A
substitution can identify different output terms, so original made-label
agreement is an explicit premise. Under that premise a check-free instance
is valid exactly when its source firing is valid and its mapped joint
problem remains consistent.

This does not construct a principal unifier, an anti-unifier or a promotion
certificate. Guarded reflection requires its retained universal observations
and is not inferred from one successful concrete instance.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CheckFreeInstanceLifting

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-- Forward transport is the existing compatible substitution law. Reflection
uses the original exact output labels, not equality after substitution. -/
theorem valid_instance_iff (action : SubstitutionAction T S) (instance_ : S)
    (picked : Selection O) (label : O → T) (rule : RuleInstance T)
    (before : Configuration T O) (checkFree : rule.checks = [])
    (baseMadeLabels : picked.made.map label = rule.produce) :
    picked.Valid action (fun occurrence => action.apply instance_ (label occurrence))
      (rule.map (action.apply instance_)) (SubstitutionStability.configuration action instance_ before) ↔
      picked.Valid action label rule before ∧
        action.Consistent (action.applyStore instance_ (picked.problem label rule before)) := by
  constructor
  · intro valid
    have consistent := valid.consistent
    rw [SubstitutionStability.problem_map] at consistent
    refine ⟨⟨valid.take_distinct, valid.output_distinct, ?_, ?_, baseMadeLabels, ?_, ?_, ?_⟩, consistent⟩
    · simpa only [RuleInstance.map, List.length_map] using valid.take_length
    · simpa only [RuleInstance.map, List.length_map] using valid.read_length
    · exact ⟨valid.occurrences.taken_subset, valid.occurrences.kept_subset,
        valid.occurrences.apart, valid.occurrences.fresh, by simp [Selection.commit]⟩
    · obtain ⟨residual, solved⟩ := consistent
      exact ⟨action.compose residual instance_, (action.models_applyStore residual instance_ _).mp solved⟩
    · simp [checkFree]
  · rintro ⟨valid, consistent⟩
    exact SubstitutionStability.valid_map action instance_ label valid consistent

theorem lift_instance (action : SubstitutionAction T S) (instance_ : S)
    (picked : Selection O) (label : O → T) (rule : RuleInstance T)
    (before : Configuration T O) (checkFree : rule.checks = [])
    (baseMadeLabels : picked.made.map label = rule.produce)
    (valid : picked.Valid action (fun occurrence => action.apply instance_ (label occurrence))
      (rule.map (action.apply instance_)) (SubstitutionStability.configuration action instance_ before)) :
    picked.Valid action label rule before :=
  ((valid_instance_iff action instance_ picked label rule before checkFree baseMadeLabels).mp valid).1

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CheckFreeInstanceLifting
