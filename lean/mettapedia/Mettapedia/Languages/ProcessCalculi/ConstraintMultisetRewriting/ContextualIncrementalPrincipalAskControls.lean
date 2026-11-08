import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualIncrementalPrincipalAsks
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrincipalAskControls

/-!
# Reusing a principal prefix while retaining a real new equation

The prefix aliases two caller variables; a third variable remains independent.
The extra equation aliases that third variable. The prefix answer is principal
for the prefix and does not solve the extra equation, yet it preserves every
ask about the full problem when the extra equation is retained and transported.
Both problems have models, so the separation is not inconsistent vacuity.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualIncrementalPrincipalAskControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualPrefixModels
open ContextualPrefixModelControls (emptySignature noDeclarations newDeclaration callers
  aliasCallers oldCallerProblem alias_answer_is_principal)

abbrev declarations := extended newDeclaration callers
def first : Term (signature emptySignature declarations) [] () := generator declarations (.inr false)
def second : Term (signature emptySignature declarations) [] () := generator declarations (.inr true)
def third : Term (signature emptySignature declarations) [] () := generator declarations (.inl ())
def rows (_ : Nat) : ContextualStoredRows.Row noDeclarations declarations [] () := .shared first
def prefixProblem := ContextualFrameUnifier.mapProblem (inclusion newDeclaration callers) oldCallerProblem
def extra : EquationStore (Term (signature emptySignature declarations) [] ()) := [(third, first)]
def answer : Assignment declarations declarations := ContextualStoredRows.liftCaptures newDeclaration aliasCallers

theorem answer_is_principal_for_prefix : ContextualFrameUnifier.Principal prefixProblem answer :=
  principal_with_unused newDeclaration alias_answer_is_principal

theorem prefix_answer_keeps_the_third_variable_distinct :
    instantiate answer third ≠ instantiate answer first := by
  intro same
  change generator declarations (.inl ()) = generator declarations (.inr false) at same
  have heads := (Term.op.inj same).1
  have names := congrArg Operator.key (Sum.inr.inj heads)
  cases names

theorem the_prefix_does_not_entail_the_extra :
    ¬ ContextualGuardSemantics.Ask noDeclarations prefixProblem rows {7} (.equal third first) := by
  intro asked
  exact prefix_answer_keeps_the_third_variable_distinct
    (asked (Unit ⊕ Bool) declarations answer answer_is_principal_for_prefix.sound)

theorem the_prefix_answer_does_not_solve_the_larger_problem :
    ¬ ContextualFrameUnifier.Models answer (prefixProblem ++ extra) := by
  intro solved
  exact prefix_answer_keeps_the_third_variable_distinct
    (solved (third, first) (List.mem_append_right _ (List.mem_singleton_self _)))

theorem the_larger_problem_entails_its_extra :
    ContextualGuardSemantics.Ask noDeclarations (prefixProblem ++ extra) rows {7} (.equal third first) :=
  ContextualGuardSemantics.Ask.equal_of_mem noDeclarations (prefixProblem ++ extra) rows {7}
    third first (List.mem_append_right _ (List.mem_singleton_self _))

def common : Assignment declarations declarations
  | .inl _ => generator declarations (.inr false)
  | .inr _ => generator declarations (.inr false)

theorem the_larger_problem_has_a_model :
    ContextualFrameUnifier.Models common (prefixProblem ++ extra) := by
  intro equation member
  change equation ∈ [(first, second), (third, first)] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

theorem every_larger_question_reflects_through_the_prefix_answer
    (check : Check (Term (signature emptySignature declarations) [] ())) :
    ContextualGuardSemantics.Ask noDeclarations
        (ContextualFrameUnifier.mapProblem answer (prefixProblem ++ extra))
        (fun occurrence => (rows occurrence).map noDeclarations answer) {7}
        (check.map (instantiate answer)) ↔
      ContextualGuardSemantics.Ask noDeclarations (prefixProblem ++ extra) rows {7} check :=
  ContextualGuardSemantics.Ask.prefix_principal_transport_iff noDeclarations prefixProblem extra
    answer answer_is_principal_for_prefix rows {7} check

theorem actual_completed_prefix_driver_preserves_every_larger_question :
    ∃ (fuel : Nat) (update : ContextualFrameUpdate.Update (ContextualResidual.observeProblem prefixProblem)),
      ContextualFrameWorklist.run fuel declarations (ContextualResidual.observeProblem prefixProblem) =
        .residual update ∧ update.remaining = [] ∧
      (∀ check : Check (Term (signature emptySignature declarations) [] ()),
        ContextualGuardSemantics.Ask noDeclarations
            (ContextualFrameUnifier.mapProblem update.answer (prefixProblem ++ extra))
            (fun occurrence => (rows occurrence).map noDeclarations update.answer) {7}
            (check.map (instantiate update.answer)) ↔
          ContextualGuardSemantics.Ask noDeclarations (prefixProblem ++ extra) rows {7} check) := by
  have structural : ContextualPatternFragment.ProblemPattern
      (ContextualResidual.observeProblem prefixProblem) :=
    (ContextualPatternFragment.checkProblem_iff _).mp (by decide +kernel)
  have model : ContextualResidual.Models answer (ContextualResidual.observeProblem prefixProblem) :=
    (ContextualResidual.models_observeProblem answer prefixProblem).mpr answer_is_principal_for_prefix.sound
  obtain ⟨fuel, update, computed, finished, _solved⟩ :=
    ContextualPatternCompleteness.solves_of_model declarations
      (ContextualResidual.observeProblem prefixProblem) structural answer model
  refine ⟨fuel, update, computed, finished, ?_⟩
  intro check
  exact ContextualGuardSemantics.Ask.completed_prefix_update_iff noDeclarations
    prefixProblem extra update finished rows {7} check

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualIncrementalPrincipalAskControls
