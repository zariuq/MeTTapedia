import Mettapedia.Logic.LinearLogic.KnowledgeTensorControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.Grades

/-!
# Controls: counting and absence interchange only within their grade

* **Counting** (`counting`): `checker` asks that at most one `c` lies in its frame; `eater` takes a
  `c`. At one `c` the two run in both orders to one state and form a cell
  (`counting_square`, `counting_cell`). Beside one more `c`, `eater` then `checker` still runs
  (`counting_target_runs_beside`) and `checker` then `eater` does not
  (`counting_source_refused_beside`), so the cell is not placed there (`counting_cell_not_placed`)
  and no cell joins the two words there (`counting_no_cell_beside`). The grade is a property of a
  run, not of its trace (`grade_not_trace_invariant`).
* **Absence** (`absent`): `adds` makes a `c`, `removes` takes it, `unless` asks that no `c` lies in its
  frame. From nothing, `adds`, `removes`, `unless` runs and `unless`, `adds`, `removes` runs
  (`absence_left_runs`, `absence_right_runs`); no cell joins them (`absence_no_cell`), even with the
  most permissive sound admissibility, two orders that run to one state. This is the one-frame form
  of the failure of the interchange law for absence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.GradeControls

open Mettapedia.Logic.LinearLogic.KnowledgeTensor
open Mettapedia.Logic.LinearLogic.KnowledgeTensorControls (Item Knowledge)
open Mettapedia.Logic.LinearLogic.KnowledgeTensorControls.Item

/-! ## Counting -/

/-- A counting check and a taker of the counted atom. -/
inductive Counted where
  | checker | eater
  deriving DecidableEq

open Counted

/-- `checker` asks for at most one `c` in its frame; `eater` takes a `c`. -/
def counting : CheckedSystem Knowledge Item Counted where
  take := fun
    | checker => 0
    | eater => {c}
  read := fun _ => 0
  make := fun _ => 0
  tell := fun _ => Set.univ
  check := fun
    | checker => fun _ frame => frame.count c ≤ 1
    | eater => fun _ _ => True
  check_mono := by
    intro declaration _ _ _ _ holds
    cases declaration <;> exact holds

theorem checker_fires (k : Knowledge) (Γ : Multiset Item) (few : Γ.count c ≤ 1) :
    checkedFires counting (k, Γ) checker (k ⊓ Set.univ, Γ) :=
  ⟨Γ, by simp [CheckedSystem.premises, counting], few, rfl,
    by simp [CheckedSystem.conclusions, counting]⟩

theorem eater_fires (k : Knowledge) (Γ : Multiset Item) :
    checkedFires counting (k, {c} + Γ) eater (k ⊓ Set.univ, Γ) :=
  ⟨Γ, by simp [CheckedSystem.premises, counting], True.intro, rfl,
    by simp [CheckedSystem.conclusions, counting]⟩

/-- **At one `c`, the checker and the eater run in both orders to one state.** -/
theorem counting_square : Square (checkedFires counting) (Set.univ, {c}) checker eater := by
  have checkFirst := checker_fires Set.univ {c} (by simp)
  have eatAfter := eater_fires (Set.univ ⊓ Set.univ) 0
  rw [add_zero] at eatAfter
  have eatFirst := eater_fires Set.univ 0
  rw [add_zero] at eatFirst
  have checkAfter := checker_fires (Set.univ ⊓ Set.univ) 0 (by simp)
  exact ⟨_, Runs.cons checkFirst (Runs.cons eatAfter (Runs.nil _)),
    Runs.cons eatFirst (Runs.cons checkAfter (Runs.nil _))⟩

/-- **The counting cell**, at one `c`. -/
def counting_cell : SemanticCell counting (Set.univ, {c}) [checker, eater] [eater, checker] :=
  Rearrangement.swap [] (Set.univ, {c}) checker eater [] (Runs.nil _) counting_square
    (Rearrangement.refl _ _)

/-- Beside one more `c`, the eater then the checker still runs. -/
theorem counting_target_runs_beside :
    ∃ t, Runs (checkedFires counting) (beside {c} (Set.univ, {c})) [eater, checker] t :=
  ⟨_, Runs.cons (eater_fires Set.univ {c})
    (Runs.cons (checker_fires (Set.univ ⊓ Set.univ) {c} (by simp)) (Runs.nil _))⟩

/-- Beside one more `c`, the checker then the eater does not run. -/
theorem counting_source_refused_beside :
    ¬ ∃ t, Runs (checkedFires counting) (beside {c} (Set.univ, {c})) [checker, eater] t := by
  rintro ⟨t, run⟩
  cases run with
  | cons step _ =>
      obtain ⟨frame, source, checked, _, _⟩ := step
      have whole : ({c} + {c} : Multiset Item) = frame := by
        simpa [CheckedSystem.premises, counting, beside] using source
      have few : frame.count c ≤ 1 := checked
      rw [← whole] at few
      simp at few

/-- **The counting cell is not placed beside one more `c`.** -/
theorem counting_cell_not_placed : ¬ counting_cell.Survives (beside {c}) := by
  rintro ⟨⟨t, straight, _⟩, _⟩
  exact counting_source_refused_beside ⟨t, straight⟩

/-- **No cell joins the two words beside one more `c`.** -/
theorem counting_no_cell_beside :
    IsEmpty (SemanticCell counting (beside {c} (Set.univ, {c})) [checker, eater] [eater, checker]) := by
  refine ⟨fun cell => ?_⟩
  obtain ⟨before, mid, x, y, after, shape, reach, square⟩ := cell.first_swap (by decide)
  obtain ⟨rfl, rfl, rfl, rfl⟩ := Rearrangement.split_two shape.symm
  cases reach
  obtain ⟨t, straight, _⟩ := square
  exact counting_source_refused_beside ⟨t, straight⟩

/-- **The grade is a property of a run, not of its trace**: two words joined by a cell, of which
beside one more `c` one runs and the other does not. -/
theorem grade_not_trace_invariant :
    Nonempty (SemanticCell counting (Set.univ, {c}) [checker, eater] [eater, checker]) ∧
      (∃ t, Runs (checkedFires counting) (beside {c} (Set.univ, {c})) [eater, checker] t) ∧
      ¬ ∃ t, Runs (checkedFires counting) (beside {c} (Set.univ, {c})) [checker, eater] t :=
  ⟨⟨counting_cell⟩, counting_target_runs_beside, counting_source_refused_beside⟩

/-! ## Absence -/

/-- A maker of `c`, a taker of `c`, and an absence check. -/
inductive Guarded where
  | adds | removes | vetoed
  deriving DecidableEq

open Guarded

/-- `adds` makes a `c`, `removes` takes one, `vetoed` asks that no `c` lies in its frame. -/
def absent : CheckedSystem Knowledge Item Guarded where
  take := fun
    | adds => 0
    | removes => {c}
    | vetoed => 0
  read := fun _ => 0
  make := fun
    | adds => {c}
    | removes => 0
    | vetoed => 0
  tell := fun _ => Set.univ
  check := fun
    | adds => fun _ _ => True
    | removes => fun _ _ => True
    | vetoed => fun _ frame => c ∉ frame
  check_mono := by
    intro declaration _ _ _ _ holds
    cases declaration <;> exact holds

theorem adds_fires (k : Knowledge) (Γ : Multiset Item) :
    checkedFires absent (k, Γ) adds (k ⊓ Set.univ, {c} + Γ) :=
  ⟨Γ, by simp [CheckedSystem.premises, absent], True.intro, rfl,
    by simp [CheckedSystem.conclusions, absent]⟩

theorem removes_fires (k : Knowledge) (Γ : Multiset Item) :
    checkedFires absent (k, {c} + Γ) removes (k ⊓ Set.univ, Γ) :=
  ⟨Γ, by simp [CheckedSystem.premises, absent], True.intro, rfl,
    by simp [CheckedSystem.conclusions, absent]⟩

theorem vetoed_fires (k : Knowledge) (Γ : Multiset Item) (clear : c ∉ Γ) :
    checkedFires absent (k, Γ) vetoed (k ⊓ Set.univ, Γ) :=
  ⟨Γ, by simp [CheckedSystem.premises, absent], clear, rfl,
    by simp [CheckedSystem.conclusions, absent]⟩

/-- `adds`, `removes`, `vetoed` runs from nothing. -/
theorem absence_left_runs :
    ∃ t, Runs (checkedFires absent) (Set.univ, 0) [adds, removes, vetoed] t := by
  have first := adds_fires Set.univ 0
  rw [add_zero] at first
  have second := removes_fires (Set.univ ⊓ Set.univ) 0
  rw [add_zero] at second
  exact ⟨_, Runs.cons first (Runs.cons second
    (Runs.cons (vetoed_fires _ 0 (Multiset.notMem_zero c)) (Runs.nil _)))⟩

/-- `vetoed`, `adds`, `removes` runs from nothing. -/
theorem absence_right_runs :
    ∃ t, Runs (checkedFires absent) (Set.univ, 0) [vetoed, adds, removes] t := by
  have second := adds_fires (Set.univ ⊓ Set.univ) 0
  rw [add_zero] at second
  have third := removes_fires (Set.univ ⊓ Set.univ ⊓ Set.univ) 0
  rw [add_zero] at third
  exact ⟨_, Runs.cons (vetoed_fires Set.univ 0 (Multiset.notMem_zero c))
    (Runs.cons second (Runs.cons third (Runs.nil _)))⟩

/-- **No cell joins the two runs**, with the most permissive sound admissibility. -/
theorem absence_no_cell :
    IsEmpty (SemanticCell absent (Set.univ, 0) [adds, removes, vetoed] [vetoed, adds, removes]) := by
  refine ⟨fun cell => ?_⟩
  obtain ⟨before, mid, x, y, after, shape, reach, square⟩ := cell.first_swap (by decide)
  rcases Rearrangement.split_three shape.symm with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · cases reach
    obtain ⟨t, _, swapped⟩ := square
    cases swapped with
    | cons step _ =>
        obtain ⟨frame, source, _, _, _⟩ := step
        have bare : (0 : Multiset Item) = {c} + 0 + frame := source
        have sizes := congrArg Multiset.card bare
        simp at sizes
  · have here : mid = (Set.univ ⊓ Set.univ, {c} + 0) :=
      Runs.unique (step := checkedFires absent) checkedFires_deterministic reach
        (Runs.cons (adds_fires Set.univ 0) (Runs.nil _))
    subst here
    obtain ⟨t, _, swapped⟩ := square
    cases swapped with
    | cons step _ =>
        obtain ⟨frame, source, checked, _, _⟩ := step
        have seen : ({c} + 0 : Multiset Item) = 0 + 0 + frame := source
        simp only [add_zero, zero_add] at seen
        have clear : c ∉ frame := checked
        rw [← seen] at clear
        exact clear (Multiset.mem_singleton_self c)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns.GradeControls
