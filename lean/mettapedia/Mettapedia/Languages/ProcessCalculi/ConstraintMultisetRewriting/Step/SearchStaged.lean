import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SearchStep

/-!
# The staged-effects driver as a certificate search

A computed-source block is executable when each instruction is valid at the configuration the
earlier ones produce, and the final equations are consistent (`StagedSourceEffects.Executable`).
Where those checks are decided, the block is a search (`stagedSpace`): a state is the remaining
code at the configuration reached so far; it passes to the next instruction when the first is
valid, and the empty code is an answer when its equations are consistent.

* It is a certificate search for executability (`stagedSpace_certifies`): this constructs the
  hypothesis of `staged_commit` and `staged_refuted`.
* It is finished at the budget of one more than the code's length (`stagedSpace_finished`), so a
  driver with that budget reports commit or refuted, each a `SourceResult` (`staged_driver`).
* With a smaller budget it may report suspended (zero budget always does,
  `Certifies.zero_suspended`); that report is not a refusal (`staged_suspended_not_refusal`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Search

open StagedSourceEffects

universe u v w

section Staged

variable {T : Type u} {S : Type v} {O : Type w} [DecidableEq O]
  (action : SubstitutionAction T S) (label : O → T)
  [∀ (i : Instruction T S O) (c : Configuration T O),
    Decidable (PredicateQueryAdmission.Valid action label i.rule i.observations c i.selection)]
  [∀ store : EquationStore T, Decidable (action.Consistent store)]

/-- **The staged block as a search**: the remaining code at the configuration reached so far. -/
def stagedSpace : Space (List (Instruction T S O) × Configuration T O) Unit where
  unfold
    | ([], c) => if action.Consistent c.equations then [.inl ()] else []
    | (i :: rest, c) =>
        if PredicateQueryAdmission.Valid action label i.rule i.observations c i.selection then
          [.inr (rest, i.selection.result label i.rule c)]
        else []

/-- A state reaches an answer exactly when its remaining code is executable from it. -/
theorem stagedSpace_reach : ∀ (code : List (Instruction T S O)) (c : Configuration T O),
    (∃ w u, (stagedSpace action label).item (.inr (code, c)) w = some (.inl u)) ↔
      Executable action label c code
  | [], c => by
      constructor
      · rintro ⟨w, u, h⟩
        cases w with
        | nil => simp at h
        | cons k w =>
            rw [Space.item_inr_cons] at h
            by_contra fails
            simp [stagedSpace, show ¬ action.Consistent c.equations from fails] at h
      · intro consistent
        refine ⟨[0], (), ?_⟩
        rw [Space.item_inr_cons]
        have : action.Consistent c.equations := consistent
        simp [stagedSpace, this]
  | i :: rest, c => by
      have next := stagedSpace_reach rest (i.selection.result label i.rule c)
      constructor
      · rintro ⟨w, u, h⟩
        cases w with
        | nil => simp at h
        | cons k w =>
            rw [Space.item_inr_cons] at h
            by_cases valid : PredicateQueryAdmission.Valid action label i.rule i.observations c i.selection
            · simp only [stagedSpace, valid, if_true, Option.bind_eq_some_iff] at h
              obtain ⟨z, get, h⟩ := h
              cases k with
              | zero =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at get
                  subst get
                  exact ⟨valid, next.mp ⟨w, u, h⟩⟩
              | succ k => simp at get
            · simp [stagedSpace, valid] at h
      · rintro ⟨valid, later⟩
        obtain ⟨w, u, h⟩ := next.mpr later
        refine ⟨0 :: w, u, ?_⟩
        rw [Space.item_inr_cons]
        have unfold : (stagedSpace action label).unfold (i :: rest, c) =
            [.inr (rest, i.selection.result label i.rule c)] := by
          simp [stagedSpace, valid]
        rw [unfold]
        exact h

/-- **The staged search certifies executability.** -/
theorem stagedSpace_certifies (code : List (Instruction T S O)) (before : Configuration T O) :
    Certifies (stagedSpace action label) (.inr (code, before)) (Executable action label before code) where
  sound p h := (stagedSpace_reach action label code before).mp ⟨p.1, p.2, h⟩
  complete ready := by
    obtain ⟨w, u, h⟩ := (stagedSpace_reach action label code before).mpr ready
    exact ⟨(w, u), h⟩

/-- States lie no deeper than the code is long. -/
theorem stagedSpace_state : ∀ (code : List (Instruction T S O)) (c : Configuration T O) (w : List ℕ)
    (t : List (Instruction T S O) × Configuration T O),
    (stagedSpace action label).item (.inr (code, c)) w = some (.inr t) → w.length ≤ code.length
  | _, _, [], _, _ => Nat.zero_le _
  | [], c, k :: w, t, h => by
      rw [Space.item_inr_cons] at h
      by_cases consistent : action.Consistent c.equations
      · simp only [stagedSpace, consistent, if_true, Option.bind_eq_some_iff] at h
        obtain ⟨z, get, h⟩ := h
        cases k with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at get
            subst get
            cases w <;> simp at h
        | succ k => simp at get
      · simp [stagedSpace, consistent] at h
  | i :: rest, c, k :: w, t, h => by
      rw [Space.item_inr_cons] at h
      by_cases valid : PredicateQueryAdmission.Valid action label i.rule i.observations c i.selection
      · simp only [stagedSpace, valid, if_true, Option.bind_eq_some_iff] at h
        obtain ⟨z, get, h⟩ := h
        cases k with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at get
            subst get
            have := stagedSpace_state rest _ w t h
            simp only [List.length_cons]
            omega
        | succ k => simp at get
      · simp [stagedSpace, valid] at h

/-- **The staged search is finished at one more than the code's length.** -/
theorem stagedSpace_finished (code : List (Instruction T S O)) (before : Configuration T O) :
    ((stagedSpace action label).run (code.length + 1) (.inr (code, before))).status = .finished := by
  rw [Space.status_run_eq_finished_iff]
  intro w t h
  have := stagedSpace_state action label code before w t h
  omega

/-- **The driver with enough budget reports commit or refuted, each a source result.** -/
theorem staged_driver (code : List (Instruction T S O)) (before : Configuration T O) :
    let report := ((stagedSpace action label).approx (code.length + 1) (.inr (code, before))).verdict
    (report = .commit ∧ SourceResult action label code before
        (ConditionalSchedule.follow label before (code.map Instruction.raw))) ∨
      (report = .refuted ∧ SourceResult action label code before before) := by
  intro report
  have certifies := stagedSpace_certifies action label code before
  have definite : report ≠ .suspended :=
    Certifies.not_suspended_of_finished (stagedSpace_finished action label code before)
  cases h : report with
  | commit => exact .inl ⟨rfl, staged_commit certifies h⟩
  | refuted => exact .inr ⟨rfl, staged_refuted certifies h⟩
  | suspended => exact absurd h definite

end Staged

#print axioms stagedSpace_reach
#print axioms stagedSpace_certifies
#print axioms stagedSpace_state
#print axioms stagedSpace_finished
#print axioms staged_driver

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Search
