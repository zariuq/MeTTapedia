import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ValueWorkerRank

/-! # Every actual value-worker step lowers the syntactic potential -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueWorkerRank

open SourceLanguage.Elaboration
open ValueContinuation ValueWorker

theorem advance (cursor : Cursor) {next : MClosed} (edge : ValueWorker.Step cursor.view next) :
    ∃ after : Cursor, next = after.view ∧ after.potential < cursor.potential := by
  cases cursor with
  | checking datum stack =>
      rcases step_cases edge with one | two | three | four | five | six | seven
      · obtain ⟨k, same, rfl⟩ := one
        obtain ⟨sameDatum, sameStack⟩ := (value_eq_iff _ _ _ _).mp same
        subst datum
        subst k
        refine ⟨.returning zero stack, rfl, ?_⟩
        simp only [Cursor.potential]
        omega
      · obtain ⟨k, same, rfl⟩ := two
        obtain ⟨sameDatum, sameStack⟩ := (value_eq_iff _ _ _ _).mp same
        subst datum
        subst k
        refine ⟨.returning unit stack, rfl, ?_⟩
        simp only [Cursor.potential]
        omega
      · obtain ⟨t, k, same, rfl⟩ := three
        obtain ⟨sameDatum, sameStack⟩ := (value_eq_iff _ _ _ _).mp same
        subst datum
        subst k
        refine ⟨.checking t (.succ stack), rfl, ?_⟩
        simp only [Cursor.potential, stackWeight, successor_weight]
        omega
      · obtain ⟨t, k, same, _⟩ := four
        exact False.elim (value_ne_resume _ _ _ _ same)
      · obtain ⟨a, b, k, same, rfl⟩ := five
        obtain ⟨sameDatum, sameStack⟩ := (value_eq_iff _ _ _ _).mp same
        subst datum
        subst k
        refine ⟨.checking a (.first b stack), rfl, ?_⟩
        simp only [Cursor.potential, stackWeight, pair_weight]
        omega
      · obtain ⟨a, b, k, same, _⟩ := six
        exact False.elim (value_ne_resume _ _ _ _ same)
      · obtain ⟨b, a, k, same, _⟩ := seven
        exact False.elim (value_ne_resume _ _ _ _ same)
  | returning datum stack =>
      rcases step_cases edge with one | two | three | four | five | six | seven
      · obtain ⟨k, same, _⟩ := one
        exact False.elim (value_ne_resume _ _ _ _ same.symm)
      · obtain ⟨k, same, _⟩ := two
        exact False.elim (value_ne_resume _ _ _ _ same.symm)
      · obtain ⟨t, k, same, _⟩ := three
        exact False.elim (value_ne_resume _ _ _ _ same.symm)
      · obtain ⟨t, k, same, rfl⟩ := four
        obtain ⟨sameDatum, sameStack⟩ := (resume_eq_iff _ _ _ _).mp same
        subst t
        obtain ⟨tail, rfl, sameTail⟩ := (succ_iff stack k).mp sameStack
        subst k
        refine ⟨.returning (successor datum) tail, rfl, ?_⟩
        simp only [Cursor.potential, stackWeight]
        omega
      · obtain ⟨a, b, k, same, _⟩ := five
        exact False.elim (value_ne_resume _ _ _ _ same.symm)
      · obtain ⟨a, b, k, same, rfl⟩ := six
        obtain ⟨sameDatum, sameStack⟩ := (resume_eq_iff _ _ _ _).mp same
        subst a
        obtain ⟨tail, rfl, sameTail⟩ := (first_iff stack b k).mp sameStack
        subst k
        refine ⟨.checking b (.second datum tail), rfl, ?_⟩
        simp only [Cursor.potential, stackWeight]
        omega
      · obtain ⟨b, a, k, same, rfl⟩ := seven
        obtain ⟨sameDatum, sameStack⟩ := (resume_eq_iff _ _ _ _).mp same
        subst b
        obtain ⟨tail, rfl, sameTail⟩ := (second_iff stack a k).mp sameStack
        subst k
        refine ⟨.returning (pair a datum) tail, rfl, ?_⟩
        simp only [Cursor.potential, stackWeight]
        omega

theorem accessible (cursor : Cursor) : Acc (fun after before => ValueWorker.Step before after) cursor.view := by
  have all : ∀ bound : Nat, ∀ cursor : Cursor, cursor.potential = bound →
      Acc (fun after before => ValueWorker.Step before after) cursor.view := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound smaller =>
        intro cursor atBound
        refine .intro cursor.view ?_
        intro next edge
        obtain ⟨after, rfl, lower⟩ := advance cursor edge
        exact smaller after.potential (atBound ▸ lower) after rfl
  exact all cursor.potential cursor rfl

theorem initialized_normalizes (datum : MClosed) :
    Acc (fun after before => ValueWorker.Step before after) (valueC datum finishContinuation) :=
  accessible (.checking datum .base)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueWorkerRank

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueWorkerRank.initialized_normalizes
