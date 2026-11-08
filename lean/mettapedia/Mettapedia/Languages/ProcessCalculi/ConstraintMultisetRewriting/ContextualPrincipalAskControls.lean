import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrincipalAsks
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixModelControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternCompleteness

/-!
# A solved alias question preserves its shared count, not an earlier empty ask

The actual pattern driver solves a nonempty caller-alias problem in a signature
with no ground operators. Its completed answer reflects every original guard.
The same alias substitution makes a previously unresolved empty-prefix equality
certain, and is not principal for that empty prefix.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrincipalAskControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualPatternFragment
open ContextualPrefixModelControls (emptySignature noDeclarations callers aliasCallers oldCallerProblem)

local instance : DecidableEq emptySignature.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : emptySignature.Srt) : DecidableEq (emptySignature.Op sort) :=
  inferInstanceAs (DecidableEq Empty)

def first : Term (signature emptySignature callers) [] () := generator callers false
def second : Term (signature emptySignature callers) [] () := generator callers true
def rows (_ : Nat) : ContextualStoredRows.Row noDeclarations callers [] () := .shared first

theorem alias_question_has_one_shared_match :
    ContextualGuardSemantics.Ask noDeclarations oldCallerProblem rows {7} (.count second 1) := by
  intro Future future candidate solved
  have equal := solved (first, second) (List.mem_singleton_self _)
  have matched : ContextualGuardMatching.Matches noDeclarations candidate
      (instantiate candidate second) (rows 7) := equal.symm
  change (ContextualGuardSemantics.region noDeclarations candidate rows {7} second).card = 1
  rw [ContextualGuardSemantics.region_singleton noDeclarations candidate rows second 7 matched]
  rfl

def problem := ContextualResidual.observeProblem oldCallerProblem

theorem the_nonempty_alias_problem_is_structural : ProblemPattern problem :=
  (checkProblem_iff _).mp (by decide +kernel)

theorem actual_completed_driver_reflects_every_original_ask :
    ∃ (fuel : Nat) (update : ContextualFrameUpdate.Update problem),
      ContextualFrameWorklist.run fuel callers problem = .residual update ∧
      update.remaining = [] ∧
      (∀ check : Check (Term (signature emptySignature callers) [] ()),
        ContextualGuardSemantics.Ask noDeclarations
            (ContextualFrameUnifier.mapProblem update.answer oldCallerProblem)
            (fun occurrence => (rows occurrence).map noDeclarations update.answer) {7}
            (check.map (instantiate update.answer)) ↔
          ContextualGuardSemantics.Ask noDeclarations oldCallerProblem rows {7} check) ∧
      ContextualGuardSemantics.Ask noDeclarations
        (ContextualFrameUnifier.mapProblem update.answer oldCallerProblem)
        (fun occurrence => (rows occurrence).map noDeclarations update.answer) {7}
        ((Check.count second 1).map (instantiate update.answer)) := by
  have model : ContextualResidual.Models aliasCallers problem :=
    (ContextualResidual.models_observeProblem aliasCallers oldCallerProblem).mpr
      ContextualPrefixModelControls.alias_answer_is_principal.sound
  obtain ⟨fuel, update, computed, empty, _solved⟩ :=
    ContextualPatternCompleteness.solves_of_model callers problem
      the_nonempty_alias_problem_is_structural aliasCallers model
  refine ⟨fuel, update, computed, empty, ?_, ?_⟩
  · intro check
    exact ContextualGuardSemantics.Ask.completed_update_iff noDeclarations oldCallerProblem
      update empty rows {7} check
  · exact (ContextualGuardSemantics.Ask.completed_update_iff noDeclarations oldCallerProblem
      update empty rows {7} (.count second 1)).mpr alias_question_has_one_shared_match

theorem empty_prefix_does_not_entail_the_alias :
    ¬ ContextualGuardSemantics.Ask noDeclarations [] rows {7} (.equal first second) := by
  intro asked
  have equal := asked Bool callers (generator callers) (by intro equation member; cases member)
  change instantiate (generator callers) first = instantiate (generator callers) second at equal
  rw [instantiate_identity, instantiate_identity] at equal
  have heads := (Term.op.inj equal).1
  have names := congrArg Operator.key (Sum.inr.inj heads)
  cases names

theorem transporting_the_empty_question_through_the_later_answer_decides_it :
    ContextualGuardSemantics.Ask noDeclarations
      (ContextualFrameUnifier.mapProblem aliasCallers [])
      (fun occurrence => (rows occurrence).map noDeclarations aliasCallers) {7}
      ((Check.equal first second).map (instantiate aliasCallers)) := by
  intro Future future candidate _solved
  change instantiate candidate (instantiate aliasCallers first) =
    instantiate candidate (instantiate aliasCallers second)
  rfl

theorem the_later_answer_is_not_principal_for_the_empty_question :
    ¬ ContextualFrameUnifier.Principal
      ([] : EquationStore (Term (signature emptySignature callers) [] ())) aliasCallers := by
  intro principal
  exact empty_prefix_does_not_entail_the_alias
    ((ContextualGuardSemantics.Ask.principal_transport_iff noDeclarations [] aliasCallers
      principal rows {7} (.equal first second)).mp
        transporting_the_empty_question_through_the_later_answer_decides_it)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrincipalAskControls
