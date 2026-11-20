import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreTimedOutcomes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStorePathControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreDisciplineControls

/-! # Ground closure and unique ambiguity with the timing-dependent quantifiers -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreTimedPathControls

open Mettapedia.Logic.LP
open SetStoreSyntax
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls (atoms)

theorem all_six_profiles_finish_at_paths (discipline : Discipline) (notUnique : discipline ≠ .unique)
    (timing : SetStore.AskTiming) :
    ∃ after, Relation.ReflTransGen (QuantifiedStep discipline timing SetStorePathControls.program)
        SetStorePathControls.seed after ∧
      QuantifiedTerminal discipline timing SetStorePathControls.program after ∧
      after = SetStorePathControls.paths := by
  have silent := fun rule inside => (SetStorePathControls.program_pure rule inside).noTell
  obtain ⟨after, run, terminal, result⟩ :=
    SetStorePathControls.all_six_profiles_finish_at_paths discipline notUnique timing
  exact ⟨after, (quantified_run_iff_of_no_tells silent).mpr run,
    (quantified_terminal_iff_of_no_tells silent).mpr terminal, result⟩

theorem unique_makes_progress (timing : SetStore.AskTiming) :
    ∃ after, QuantifiedStep .unique timing SetStoreDisciplineControls.singleProgram
      SetStoreDisciplineControls.seed after := by
  obtain ⟨after, step⟩ := SetStoreDisciplineControls.unique_makes_progress timing
  exact ⟨after, (quantified_iff_of_no_tells
    (fun rule inside => (SetStoreDisciplineControls.single_pure rule inside).noTell)).mpr step⟩

theorem ambiguous_unique_refuses (timing : SetStore.AskTiming) (after : Finset (Term atoms)) :
    ¬ QuantifiedStep .unique timing SetStoreOpenControls.program
      SetStoreDisciplineControls.ambiguousSeed after := by
  intro stepped
  have old := (quantified_iff_of_no_tells
    (fun rule inside => (SetStoreOpenControls.program_propagates rule inside).noTell)).mp stepped
  obtain ⟨bag, _, _, unique, _⟩ := old
  exact SetStoreDisciplineControls.no_complete_unique_bag bag unique

/-- The concrete finite carrier satisfies the hypotheses of the termination theorem. -/
theorem finite_paths_no_infinite_run (discipline : Discipline) (timing : SetStore.AskTiming)
    (run : ℕ → Finset (Term atoms)) (initial : run 0 = SetStorePathControls.seed) :
    ¬ ∀ n, QuantifiedStep discipline timing SetStorePathControls.program (run n) (run (n + 1)) := by
  apply quantified_no_infinite_run discipline timing SetStorePathControls.program_pure
    SetStorePathControls.paths SetStorePathControls.paths_closed run
  · rw [initial]
    decide +kernel
  · rw [initial]
    exact SetStorePathControls.rows_ground _

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreTimedPathControls
