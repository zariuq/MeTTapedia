import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Core
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PredicateQueryAdmission

/-!
# The guarded two-way diamond retains complete query observations

The original diamond supplies both actual resource/constraint admissions.
Each census additionally retains its complete region at its original cut;
the other event may not write that region in a common joint solution.
Shared equations remain permitted. Physical independence alone is not the
new premise, and the theorem does not infer source-context independence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CensusComposition

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open GuardFreeProcessOrders

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

theorem independently_ready_commute (A : SubstitutionAction T S) (label : O → T)
    (first second : ConditionalSchedule.Firing T O) (before : Configuration T O)
    (firstQueries secondQueries : List (PredicateQueryAdmission.Query T S O))
    (firstReady : PredicateQueryAdmission.Valid A label first.1 firstQueries before first.2)
    (secondReady : PredicateQueryAdmission.Valid A label second.1 secondQueries before second.2)
    (resources : Independent label first.2.commit second.2.commit)
    (joint : A.Consistent ((before.equations ++ added label first.1 first.2) ++ added label second.1 second.2))
    (firstChecks : ∀ check ∈ first.1.checks,
      Check.IgnoresWrites A ((before.equations ++ added label first.1 first.2) ++ added label second.1 second.2)
        label second.2 check)
    (secondChecks : ∀ check ∈ second.1.checks,
      Check.IgnoresWrites A ((before.equations ++ added label first.1 first.2) ++ added label second.1 second.2)
        label first.2 check)
    (firstCensus : ∀ query ∈ firstQueries,
      query.IgnoresWrites A ((before.equations ++ added label first.1 first.2) ++ added label second.1 second.2)
        label second.2)
    (secondCensus : ∀ query ∈ secondQueries,
      query.IgnoresWrites A ((before.equations ++ added label first.1 first.2) ++ added label second.1 second.2)
        label first.2) :
    PredicateQueryAdmission.Valid A label second.1 secondQueries (first.2.result label first.1 before) second.2 ∧
      PredicateQueryAdmission.Valid A label first.1 firstQueries (second.2.result label second.1 before) first.2 ∧
      SameUpTo A (second.2.result label second.1 (first.2.result label first.1 before))
        (first.2.result label first.1 (second.2.result label second.1 before)) := by
  obtain ⟨secondRaw, firstRaw, same⟩ := Core.independently_ready_commute A label first second before
    firstReady.firing secondReady.firing resources joint firstChecks secondChecks
  refine ⟨secondReady.after secondRaw rfl ?_ ?_, firstReady.after firstRaw rfl ?_ ?_, same⟩
  · intro candidate solved
    simp only [problem_eq, result_equations, SubstitutionAction.models_append] at solved ⊢
    exact ⟨solved.1.1, solved.2⟩
  · intro query member candidate solved
    apply secondCensus query member candidate
    simpa only [problem_eq, result_equations] using solved
  · intro candidate solved
    simp only [problem_eq, result_equations, SubstitutionAction.models_append] at solved ⊢
    exact ⟨solved.1.1, solved.2⟩
  · intro query member candidate solved
    apply firstCensus query member candidate
    simp only [problem_eq, result_equations, SubstitutionAction.models_append] at solved ⊢
    exact ⟨⟨solved.1.1, solved.2⟩, solved.1.2⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CensusComposition
