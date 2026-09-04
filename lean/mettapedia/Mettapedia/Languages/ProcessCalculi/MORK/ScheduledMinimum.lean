import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveExecution

/-!
# Selecting a proved strict scheduler minimum

The least-key scheduler is list implemented, but language instances usually
know their authority inventory by membership rather than by one enumeration.
This module shows that a present strict minimum is selected independently of
the surrounding list order.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK

private theorem foldl_keeps_strict_scheduler_minimum
    {α : Type} [SchedulerKey α] [DecidableEq α]
    (minimum : α) (remaining inventory : List α)
    (within : ∀ candidate ∈ remaining, candidate ∈ inventory)
    (strict : ∀ candidate ∈ inventory, candidate ≠ minimum →
      lexLt (SchedulerKey.key minimum) (SchedulerKey.key candidate) = true) :
    remaining.foldl (fun best candidate =>
        match best with
        | none => some candidate
        | some current =>
            if lexLt (SchedulerKey.key candidate) (SchedulerKey.key current)
            then some candidate
            else some current)
        (some minimum) = some minimum := by
  induction remaining with
  | nil => rfl
  | cons candidate remaining induction =>
      have candidateWithin : candidate ∈ inventory :=
        within candidate (by simp)
      by_cases equal : candidate = minimum
      · subst candidate
        simp only [List.foldl_cons, lexLt_irrefl, Bool.false_eq_true,
          ↓reduceIte]
        exact induction
          (fun later member => within later (List.mem_cons_of_mem _ member))
      · have minimumPreempts := strict candidate candidateWithin equal
        have candidateDoesNotPreempt :
            lexLt (SchedulerKey.key candidate)
              (SchedulerKey.key minimum) = false :=
          lexLt_asymm _ _ minimumPreempts
        simp only [List.foldl_cons, candidateDoesNotPreempt,
          Bool.false_eq_true, ↓reduceIte]
        exact induction
          (fun later member => within later (List.mem_cons_of_mem _ member))

/-- A present candidate that is strictly earlier than every distinct member
is the exact result of least-key scheduling.  No list-order assumption is
needed. -/
theorem selectNextScheduled_eq_some_of_mem_of_strict_minimum
    {α : Type} [SchedulerKey α] [DecidableEq α]
    (facts : List α) (minimum : α) (present : minimum ∈ facts)
    (strict : ∀ candidate ∈ facts, candidate ≠ minimum →
      lexLt (SchedulerKey.key minimum) (SchedulerKey.key candidate) = true) :
    selectNextScheduled facts = some minimum := by
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp present
  subst facts
  cases beforeSelected : selectNextScheduled before with
  | none =>
      unfold selectNextScheduled at beforeSelected ⊢
      rw [List.foldl_append, beforeSelected]
      simp only [List.foldl_cons]
      exact foldl_keeps_strict_scheduler_minimum minimum after
        (before ++ minimum :: after)
        (fun candidate member => by simp [member]) strict
  | some incumbent =>
      have incumbentBefore : incumbent ∈ before :=
        selectNextScheduled_mem beforeSelected
      have incumbentWithin : incumbent ∈ before ++ minimum :: after := by
        simp [incumbentBefore]
      unfold selectNextScheduled at beforeSelected ⊢
      rw [List.foldl_append, beforeSelected]
      simp only [List.foldl_cons]
      by_cases equal : incumbent = minimum
      · subst incumbent
        simp only [lexLt_irrefl, Bool.false_eq_true, ↓reduceIte]
        exact foldl_keeps_strict_scheduler_minimum minimum after
          (before ++ minimum :: after)
          (fun candidate member => by simp [member]) strict
      · rw [strict incumbent incumbentWithin equal]
        exact foldl_keeps_strict_scheduler_minimum minimum after
          (before ++ minimum :: after)
          (fun candidate member => by simp [member]) strict

#print axioms selectNextScheduled_eq_some_of_mem_of_strict_minimum

end Mettapedia.Languages.ProcessCalculi.MORK
