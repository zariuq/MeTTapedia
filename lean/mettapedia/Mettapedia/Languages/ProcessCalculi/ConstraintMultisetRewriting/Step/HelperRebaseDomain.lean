import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperRunRebase

/-!
# The aggregate domain of a local run placed in a helper context

Fresh helper definitions preserve joint solvability. The complete check is
therefore one initial joint-consistency condition for nonempty runs, together
with freshness of every produced identity against the context. Existing
resource overlap and guard-blindness conditions are unnecessary here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {O : Type} [DecidableEq O]

namespace ContextPlacement

theorem after_left_solvable_iff {left right : State S O} (placed : ContextPlacement left right)
    (f : Firing left) :
    (Frames.contextual S).Solvable (placed.afterLeft f).state.knowledge ↔
      (Frames.contextual S).Solvable placed.state.knowledge := by
  have information : (Frames.contextual S).Solvable (placed.leftFiring f).information ↔
      (Frames.contextual S).Solvable placed.state.knowledge := by
    constructor
    · rintro ⟨target, mapping, solved⟩
      exact ⟨target, Assignment.compose mapping (incl placed.frame f.helper),
        helperStep.models_knowledge (placed.leftFiring f) mapping solved⟩
    · exact information_solvable (placed.leftFiring f)
  exact (placed.left_result_iso f).solvable_iff.symm.trans information

end ContextPlacement

def OutputsAvoid {left : State S O} (run : helperStep.Run left) (context : Finset O) : Prop :=
  ∀ entry ∈ run.word, entry.2.made ∉ context

theorem outputsAvoid_cons {left : State S O} (f : Firing left) (allowed : helperStep.Admits f)
    (rest : helperStep.Run f.after) (context : Finset O) :
    OutputsAvoid (.cons f allowed rest) context ↔ f.made ∉ context ∧ OutputsAvoid rest context := by
  simp only [OutputsAvoid, Step.Run.word, List.forall_mem_cons]

theorem rebase_checks_iff_aggregate : ∀ {left right : State S O} (placed : ContextPlacement left right)
    (run : helperStep.Run left), RebaseChecks placed run ↔
      (run.word = [] ∨ (Frames.contextual S).Solvable placed.state.knowledge) ∧ OutputsAvoid run right.present
  | _, _, placed, .nil _ => by simp [rebaseChecks_nil placed, OutputsAvoid, Step.Run.word]
  | _, _, placed, .cons f allowed rest => by
      rw [rebaseChecks_cons, rebase_checks_iff_aggregate (placed.afterLeft f) rest,
        placed.after_left_solvable_iff f, outputsAvoid_cons]
      simp only [Step.Run.word, List.cons_ne_nil, false_or]
      tauto

theorem rebase_plan_iff_aggregate {left right : State S O} (placed : ContextPlacement left right)
    (run : helperStep.Run left) : Nonempty (RebasePlan S O placed run) ↔
      (run.word = [] ∨ (Frames.contextual S).Solvable placed.state.knowledge) ∧ OutputsAvoid run right.present :=
  (rebase_plan_iff_checks placed run).trans (rebase_checks_iff_aggregate placed run)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers
