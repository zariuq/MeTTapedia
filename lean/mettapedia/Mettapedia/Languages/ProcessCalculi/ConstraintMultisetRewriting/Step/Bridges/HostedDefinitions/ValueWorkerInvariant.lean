import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ValueWorkerCases

/-!
# Reconstruction invariant for successful value-worker executions

The invariant retains the initial literal datum while the actual worker walks
its successors and pairs. A return carries a proof of the source value grammar.
It concerns the seven worker rules; isolation from other program phases is a
separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueWorker

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Normalization
open SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing.DirectedAnswers (Value)
open ValueContinuation

def Checking (original current : MClosed) : Prop :=
  ∃ datum stack, current = valueC datum (code stack) ∧ Valid stack ∧ plug datum stack = original

def Returning (original current : MClosed) : Prop :=
  ∃ datum : Tower.Tm 0, ∃ stack, Value datum ∧
    current = resumeC (encodeTm datum) (code stack) ∧ Valid stack ∧
      plug (encodeTm datum) stack = original

def Invariant (original current : MClosed) : Prop :=
  Checking original current ∨ Returning original current

theorem step_preserves {original first last : MClosed}
    (step : Step first last) (before : Invariant original first) : Invariant original last := by
  rcases step_cases step with one | two | three | four | five | six | seven
  · obtain ⟨k, rfl, rfl⟩ := one
    rcases before with checking | returning
    · obtain ⟨datum, stack, same, valid, restored⟩ := checking
      obtain ⟨sameDatum, sameStack⟩ := (value_eq_iff _ _ _ _).mp same
      subst datum
      subst k
      exact .inr ⟨TowerVectorsModel.zeroC, stack, .zero, rfl, valid, restored⟩
    · obtain ⟨datum, stack, _, same, _, _⟩ := returning
      exact False.elim (value_ne_resume _ _ _ _ same)
  · obtain ⟨k, rfl, rfl⟩ := two
    rcases before with checking | returning
    · obtain ⟨datum, stack, same, valid, restored⟩ := checking
      obtain ⟨sameDatum, sameStack⟩ := (value_eq_iff _ _ _ _).mp same
      subst datum
      subst k
      exact .inr ⟨TowerVectorsModel.ttC, stack, .tt, rfl, valid, restored⟩
    · obtain ⟨datum, stack, _, same, _, _⟩ := returning
      exact False.elim (value_ne_resume _ _ _ _ same)
  · obtain ⟨t, k, rfl, rfl⟩ := three
    rcases before with checking | returning
    · obtain ⟨datum, stack, same, valid, restored⟩ := checking
      obtain ⟨sameDatum, sameStack⟩ := (value_eq_iff _ _ _ _).mp same
      subst datum
      subst k
      exact .inl ⟨t, .succ stack, rfl, valid, restored⟩
    · obtain ⟨datum, stack, _, same, _, _⟩ := returning
      exact False.elim (value_ne_resume _ _ _ _ same)
  · obtain ⟨t, k, rfl, rfl⟩ := four
    rcases before with checking | returning
    · obtain ⟨datum, stack, same, _, _⟩ := checking
      exact False.elim (value_ne_resume _ _ _ _ same.symm)
    · obtain ⟨datum, stack, isValue, same, valid, restored⟩ := returning
      obtain ⟨sameDatum, sameStack⟩ := (resume_eq_iff _ _ _ _).mp same
      subst t
      obtain ⟨tail, rfl, sameTail⟩ := (succ_iff stack k).mp sameStack.symm
      subst k
      refine .inr ⟨TowerVectorsModel.succC datum, tail, .succ isValue, ?_, valid, ?_⟩
      · rw [successor_encoded]
      · simpa only [plug, successor_encoded] using restored
  · obtain ⟨a, b, k, rfl, rfl⟩ := five
    rcases before with checking | returning
    · obtain ⟨datum, stack, same, valid, restored⟩ := checking
      obtain ⟨sameDatum, sameStack⟩ := (value_eq_iff _ _ _ _).mp same
      subst datum
      subst k
      exact .inl ⟨a, .first b stack, rfl, valid, restored⟩
    · obtain ⟨datum, stack, _, same, _, _⟩ := returning
      exact False.elim (value_ne_resume _ _ _ _ same)
  · obtain ⟨a, b, k, rfl, rfl⟩ := six
    rcases before with checking | returning
    · obtain ⟨datum, stack, same, _, _⟩ := checking
      exact False.elim (value_ne_resume _ _ _ _ same.symm)
    · obtain ⟨datum, stack, isValue, same, valid, restored⟩ := returning
      obtain ⟨sameDatum, sameStack⟩ := (resume_eq_iff _ _ _ _).mp same
      subst a
      obtain ⟨tail, rfl, sameTail⟩ := (first_iff stack b k).mp sameStack.symm
      subst k
      exact .inl ⟨b, .second (encodeTm datum) tail, rfl,
        ⟨⟨datum, isValue, rfl⟩, valid⟩, restored⟩
  · obtain ⟨b, a, k, rfl, rfl⟩ := seven
    rcases before with checking | returning
    · obtain ⟨datum, stack, same, _, _⟩ := checking
      exact False.elim (value_ne_resume _ _ _ _ same.symm)
    · obtain ⟨datum, stack, isValue, same, valid, restored⟩ := returning
      obtain ⟨sameDatum, sameStack⟩ := (resume_eq_iff _ _ _ _).mp same
      subst b
      obtain ⟨tail, rfl, sameTail⟩ := (second_iff stack a k).mp sameStack.symm
      subst k
      obtain ⟨⟨first, firstValue, rfl⟩, tailValid⟩ := valid
      refine .inr ⟨.pair first datum, tail, .pair firstValue isValue, ?_, tailValid, ?_⟩
      · rw [pair_encoded]
      · simpa only [plug, pair_encoded] using restored

theorem runs_preserve {original first last : MClosed}
    (run : Runs first last) (before : Invariant original first) : Invariant original last := by
  induction run with
  | refl => exact before
  | tail _ edge ih => exact step_preserves edge ih

theorem initialized (datum : MClosed) : Invariant datum (valueC datum finishContinuation) :=
  .inl ⟨datum, .base, rfl, trivial, rfl⟩

/-- A successful public worker call returns its identical initial literal
datum, and that datum encodes an actual source value. -/
theorem success_reflects (datum result : MClosed)
    (run : Runs (valueC datum finishContinuation) (resumeC result finishContinuation)) :
    result = datum ∧ ∃ value : Tower.Tm 0, Value value ∧ result = encodeTm value := by
  have invariant := runs_preserve run (initialized datum)
  rcases invariant with checking | returning
  · obtain ⟨term, stack, same, _, _⟩ := checking
    exact False.elim (value_ne_resume _ _ _ _ same.symm)
  · obtain ⟨term, stack, isValue, same, _, restored⟩ := returning
    obtain ⟨sameResult, sameStack⟩ := (resume_eq_iff _ _ _ _).mp same
    have stackBase := (base_iff stack).mp sameStack.symm
    subst stack
    exact ⟨sameResult.trans restored, term, isValue, sameResult⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueWorker

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueWorker.success_reflects
