import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalChecks
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SubstitutionStability
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ConditionalComposition

/-!
# Principal answers preserve the guards of ordinary occurrence firings

The interface retains each check argument and every value in its observation
world. Applying a principal answer then preserves the universal guard test in
both directions. Merely finding one concrete successful check is insufficient.

For the actual step, original shape and resource tests remain explicit. A
substitution may identify distinct output terms, so an equality of substituted
output lists cannot replace the original occurrence/output identity check.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalStep

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO}

theorem residual_store_is_always_solved (A : SubstitutionAction T S)
    {problem : EquationStore T} {answer : S} (solved : A.Models answer problem)
    (residual : S) : A.Models residual (A.applyStore answer problem) :=
  (A.models_applyStore residual answer problem).mpr (A.models_compose solved residual)

theorem check_iff (A : SubstitutionAction T S)
    {problem : EquationStore T} {answer : S} {observed : List T}
    (principal : A.PrincipalOn problem answer observed) (label : O → T)
    (world : Finset O) (check : Check T)
    (arguments : ∀ term ∈ check.terms, term ∈ observed)
    (values : ∀ occurrence ∈ world, label occurrence ∈ observed) :
    A.Entails problem (fun assignment => check.Holds A assignment label world) ↔
      A.Entails (A.applyStore answer problem)
        (fun residual => (check.map (A.apply answer)).Holds A residual
          (fun occurrence => A.apply answer (label occurrence)) world) := by
  rw [SubstitutionAction.PrincipalOn.check_iff A principal label world check arguments values]
  constructor
  · intro holds residual _
    exact (SubstitutionStability.check_map A residual answer label world check).mpr (holds residual)
  · intro holds residual
    exact (SubstitutionStability.check_map A residual answer label world check).mp
      (holds residual (residual_store_is_always_solved A principal.sound residual))

variable [DecidableEq O]

/-- Resource identity and output shape remain the original tests. The
principal interface is for this firing's own equation prefix and check world,
not a later state that might decide an earlier pending guard. -/
theorem valid_iff (A : SubstitutionAction T S) (label : O → T)
    {rule : RuleInstance T} {selection : Selection O} {before : Configuration T O}
    {answer : S} {observed : List T}
    (principal : A.PrincipalOn (selection.problem label rule before) answer observed)
    (shape : (ShapeTest.ofSelection rule selection).Holds label)
    (enabled : Enabled label before.present selection.commit)
    (arguments : ∀ check ∈ rule.checks, ∀ term ∈ check.terms, term ∈ observed)
    (values : ∀ occurrence ∈ before.present, label occurrence ∈ observed) :
    selection.Valid A label rule before ↔
      selection.Valid A (fun occurrence => A.apply answer (label occurrence))
        (rule.map (A.apply answer)) (SubstitutionStability.configuration A answer before) := by
  constructor
  · intro valid
    exact SubstitutionStability.valid_map A answer label valid
      ⟨A.identity, residual_store_is_always_solved A principal.sound A.identity⟩
  · intro valid
    refine ⟨shape.1, shape.2.1, shape.2.2.1, shape.2.2.2.1, shape.2.2.2.2,
      enabled, ⟨answer, principal.sound⟩, ?_⟩
    intro check member
    apply (check_iff A principal label before.present check (arguments check member) values).mpr
    intro residual solved
    have checks := valid.checks (check.map (A.apply answer))
      (List.mem_map.mpr ⟨check, member, rfl⟩) residual
    rw [SubstitutionStability.problem_map] at checks
    exact checks solved

theorem step_of_substituted_selection (A : SubstitutionAction T S) (label : O → T)
    {rule : RuleInstance T} {selection : Selection O} {before : Configuration T O}
    {answer : S} {observed : List T}
    (principal : A.PrincipalOn (selection.problem label rule before) answer observed)
    (shape : (ShapeTest.ofSelection rule selection).Holds label)
    (enabled : Enabled label before.present selection.commit)
    (arguments : ∀ check ∈ rule.checks, ∀ term ∈ check.terms, term ∈ observed)
    (values : ∀ occurrence ∈ before.present, label occurrence ∈ observed)
    (valid : selection.Valid A (fun occurrence => A.apply answer (label occurrence))
      (rule.map (A.apply answer)) (SubstitutionStability.configuration A answer before)) :
    Step A label rule before (selection.result label rule before) :=
  ⟨selection, (valid_iff A label principal shape enabled arguments values).mpr valid, rfl⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalStep
