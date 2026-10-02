import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivePairContextualReflection
import Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution

/-!
# The authored reflection profile selects scoped Cost activation

The synchronous whole-pair instance enters the shared interpreter through its
existing reflection profile. This connects open binder elimination to source
selection rather than a caller-selected operation. Matching remains literal.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.ActivePairSourceSelectedReflection

open Mettapedia.OSLF.MeTTaIL
open Syntax
open ActivePairContextualReflection

/-- Source selection releases the checked target in the original open context. -/
theorem open_firing : ScopedReflectiveExecution.applyRuleAt
    ActivePair.presentation.reflection.1 Engine.RelationEnv.empty ActivePair.language 1
    ActivePair.rule ActivePair.openSource = [correctedTarget] := by
  rw [ScopedReflectiveExecution.selected _ _ _ _ _ _ declaration declaration_selected]
  exact corrected_open_firing

/-- Source selection does not add authorization to an empty purse. -/
theorem empty_purse_blocked : ScopedReflectiveExecution.applyRuleAt
    ActivePair.presentation.reflection.1 Engine.RelationEnv.empty ActivePair.language 1
    ActivePair.rule (sourceWithStack FiniteWhole.emptyStack) = [] := by
  rw [ScopedReflectiveExecution.selected _ _ _ _ _ _ declaration declaration_selected]
  exact ActivePairContextualReflection.empty_purse_blocked

/-- The returned firing has its original captured and completed contexts. -/
theorem open_firing_has_capture :
    ∃ spec captured assignment,
      ActivePair.rule.bindings = some spec ∧ RuleBinding.admittedFor ActivePair.rule spec = true ∧
      captured ∈ ScopedRuleMatching.matchRuleAt ActivePair.rule spec 1 ActivePair.openSource ∧
      assignment ∈ ScopedRuleExecution.completeAssignments Engine.RelationEnv.empty
        ActivePair.language 1 ActivePair.rule spec captured ∧
      ScopedRuleMatching.reductWith?
        (ScopedReflectiveExecution.binderOperation ActivePair.presentation.reflection.1 ActivePair.rule)
        ActivePair.rule spec 1 assignment = some correctedTarget := by
  apply (ScopedReflectiveExecution.mem_applyRuleAt_iff _ _ _ _ _ _ _).mp
  rw [open_firing]
  exact List.mem_singleton_self _

/-- Language-level traversal includes this same firing under the authored rule. -/
theorem open_language_firing : correctedTarget ∈ ScopedReflectiveExecution.rewriteStepAt
    ActivePair.presentation.reflection.1 Engine.RelationEnv.empty ActivePair.language 1
    ActivePair.openSource := by
  apply (ScopedReflectiveExecution.mem_rewriteStepAt_iff _ _ _ _ _ _).mpr
  refine ⟨ActivePair.rule, ?_, ?_⟩
  · simp only [ActivePair.language, List.mem_cons, true_or]
  · rw [open_firing]
    exact List.mem_singleton_self _

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.ActivePairSourceSelectedReflection
