import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersAbsence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersCached

/-!
# Unmatched calls under binders return themselves

MeTTa returns a call that no equation matches as itself (`metta_call`: when `(= atom $X)` has no
answer, the result is the atom). On the binder-bearing core this is one firing of the guarded
contextual step: the unmatched rule of `ProgramBindersAbsence`, whose absence checks ask, over every
future solution, that no equation's left-hand side is the call.

**The reference semantics** is defined from the equations alone (`ProgramBinders.Rewrites`,
`Unmatched`): `Evaluates program call value` holds when rewriting reaches `value` and no equation
matches it.

**On the step**, equation firings are the firings of `ProgramBindersStep` for the program's own
equations (`EquationTransition`); the unmatched firing is the return rule with its checks
(`UnmatchedTransition`).

- `returns_iff`, `unmatched_reads_iff`: at a call that every solution reads the same way, the
  unmatched firing is admitted exactly when the call is unmatched, and its result reads exactly as the
  call itself.
- `returned_readings_iff`: in general the result reads exactly as the call did, unknowns included.
- `returned_is_final`: after a call is returned, no equation fires on it, at any later binding.
- `evaluates_of_run`, `run_of_evaluates`, `evaluates_iff`: runs of equation firings followed by the
  unmatched firing reach exactly the values of the reference semantics. The direction from runs needs
  no hypothesis; the converse needs determinate equations, as for R98's runs with solvers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {Γ : Ctx S} {sort : S.Srt} {ι : Type} {program : ι → Equation S Γ sort}

variable (program) in
/-- **The reference semantics with unmatched calls returned.** Rewriting reaches `value`, and no
equation matches it, so it is returned as itself. -/
def Evaluates (call value : Term S Γ sort) : Prop :=
  Relation.ReflTransGen (Rewrites program) call value ∧ Unmatched program value

variable [DecidableEq ι]

variable (program) in
/-- The firings of the program's own equations; the return rule is never one of them. -/
def EquationTransition (before after : State (withReturn program)) : Prop :=
  ∃ (index : ι) (valid : Admitted (withReturn program) before (some index)),
    after = destination (withReturn program) before (some index) valid

variable [ClosedTerms S]

/-! ## One firing -/

/-- **The result of a return reads exactly as the call did.** -/
theorem returned_readings_iff [Fintype ι] (state : State (withReturn program))
    (value : Term (signature S state.1.declarations) Γ sort) (holds : Holds (withReturn program) state value)
    (valid : UnmatchedAdmitted program state) (answer : Term S Γ sort) :
    Reads (withReturn program) (unmatchedDestination program state valid) answer ↔
      Reads (withReturn program) state answer := by
  constructor
  · rintro ⟨Future, future, solution, reads⟩
    obtain ⟨old, call, readsCall, answered⟩ := destination_reflected state none valid.toReturn value holds
      solution answer ((unmatched_reads_as_return state valid solution answer).mp reads)
    rw [(return_answers call answer).mp answered]
    exact ⟨_, _, old, readsCall⟩
  · rintro ⟨Future, future, solution, reads⟩
    exact ⟨_, _, _, (unmatched_reads_as_return state valid _ answer).mpr
      (destination_reads state none valid.toReturn solution answer reads (fun _ => answer) (return_matches answer)
        answer (return_matches answer))⟩

/-- **Admission is unmatchedness.** At a call that every solution reads the same way, the unmatched
firing is admitted exactly when no equation matches the call. -/
theorem returns_iff [Fintype ι] (state : State (withReturn program)) (call : Term S Γ sort)
    (determined : Determines (withReturn program) state call) :
    UnmatchedAdmitted program state ↔ Unmatched program call := by
  obtain ⟨⟨Future, future, solution, reads⟩, unique⟩ := determined
  obtain ⟨value, holds, _, _⟩ := reads
  rw [unmatched_admitted_iff state value holds]
  constructor
  · rintro ⟨_, absent⟩
    exact absent future solution call ⟨value, holds, by assumption, by assumption⟩
  · intro unmatched
    refine ⟨⟨call, Future, future, solution, ⟨value, holds, by assumption, by assumption⟩⟩, ?_⟩
    intro Later later other otherCall readsOther
    rw [unique later other otherCall readsOther]
    exact unmatched

/-- **An unmatched call returns itself.** At a call that every solution reads the same way, the
result of the unmatched firing reads exactly as the call. -/
theorem unmatched_reads_iff [Fintype ι] (state : State (withReturn program)) (call : Term S Γ sort)
    (determined : Determines (withReturn program) state call) (valid : UnmatchedAdmitted program state)
    (answer : Term S Γ sort) :
    Reads (withReturn program) (unmatchedDestination program state valid) answer ↔ answer = call := by
  obtain ⟨⟨Future, future, solution, reads⟩, unique⟩ := determined
  obtain ⟨value, holds, solved, observed⟩ := reads
  rw [returned_readings_iff state value holds valid answer]
  constructor
  · rintro ⟨Later, later, other, readsOther⟩
    exact unique later other answer readsOther
  · intro same
    rw [same]
    exact ⟨Future, future, solution, value, holds, solved, observed⟩

/-- **A returned call is final.** After the unmatched firing, no equation of the program fires on the
returned call, at any solution: the absence observed at the cut persists. -/
theorem returned_is_final [Fintype ι] (state : State (withReturn program))
    (value : Term (signature S state.1.declarations) Γ sort) (holds : Holds (withReturn program) state value)
    (valid : UnmatchedAdmitted program state) (index : ι) :
    ¬ Admitted (withReturn program) (unmatchedDestination program state valid) (some index) := by
  intro admitted
  obtain ⟨Later, later, candidate, solved⟩ := admitted.solvable
  have holdsAfter := (unmatched_holds_as_return state valid _).mpr
    (destination_holds state none valid.toReturn holds.1)
  obtain ⟨old, call, θ, reads, matched, _⟩ :=
    model_recovers (unmatchedDestination program state valid) (some index) _ holdsAfter candidate solved
  obtain ⟨Future, future, solution, readsBefore⟩ :=
    (returned_readings_iff state value holds valid call).mp ⟨_, _, old, reads⟩
  exact ((unmatched_admitted_iff state value holds).mp valid).2 future solution call readsBefore index θ matched

/-! ## Runs -/

/-- Every reading after a run of equation firings is reached by source rewriting. -/
theorem equation_runs_backward {call : Term S Γ sort} {after : State (withReturn program)}
    (path : Relation.ReflTransGen (EquationTransition program) (initial call) after) :
    (∃ value, Holds (withReturn program) after value) ∧
      ∀ answer, Reads (withReturn program) after answer → Relation.ReflTransGen (Rewrites program) call answer := by
  induction path with
  | refl =>
      refine ⟨⟨_, initial_holds call⟩, ?_⟩
      rintro answer ⟨Future, future, solution, reads⟩
      obtain rfl := (initial_determines call).2 future solution answer reads
      exact .refl
  | tail _ transition ih =>
      obtain ⟨⟨value, holds⟩, earlier⟩ := ih
      obtain ⟨index, valid, rfl⟩ := transition
      refine ⟨⟨_, destination_holds _ (some index) valid holds.1⟩, ?_⟩
      rintro answer ⟨Future, future, solution, reads⟩
      obtain ⟨old, middle, readsMiddle, answered⟩ :=
        destination_reflected _ (some index) valid value holds solution answer reads
      exact (earlier middle ⟨_, _, old, readsMiddle⟩).tail ⟨index, answered⟩

/-- For determinate equations, every source run is a run of equation firings ending at a state that
fixes its answer. -/
theorem equation_runs_fixes (determinate : ∀ index, Determinate (program index)) {call answer : Term S Γ sort}
    (runs : Relation.ReflTransGen (Rewrites program) call answer) :
    ∃ after, Relation.ReflTransGen (EquationTransition program) (initial call) after ∧
      Fixes (withReturn program) after answer := by
  induction runs with
  | refl => exact ⟨initial call, .refl, initial_fixes call⟩
  | tail _ rewriting ih =>
      obtain ⟨middle, path, fixes⟩ := ih
      obtain ⟨index, θ, matched, answered⟩ := rewriting
      obtain ⟨⟨Future, future, solution, reads⟩, _⟩ := fixes.determines
      have valid := admitted_of_match middle (some index) solution _ reads θ matched
      obtain ⟨next, nextAnswers, nextFixes⟩ := fixes_destination middle _ fixes (some index) valid (determinate index)
      have same := Determinate.answer_unique (determinate index) nextAnswers ⟨θ, matched, answered⟩
      subst same
      exact ⟨_, path.tail ⟨index, valid, rfl⟩, nextFixes⟩

/-- **From the step to the reference.** A run of equation firings followed by the unmatched firing
reads only values of the reference semantics. -/
theorem evaluates_of_run [Fintype ι] {call value : Term S Γ sort} {before after : State (withReturn program)}
    (path : Relation.ReflTransGen (EquationTransition program) (initial call) before)
    (returned : UnmatchedTransition program before after) (reads : Reads (withReturn program) after value) :
    Evaluates program call value := by
  obtain ⟨⟨current, holds⟩, earlier⟩ := equation_runs_backward path
  obtain ⟨valid, rfl⟩ := returned
  have readsBefore := (returned_readings_iff before current holds valid value).mp reads
  obtain ⟨Future, future, solution, readsAt⟩ := readsBefore
  exact ⟨earlier value ⟨_, _, solution, readsAt⟩,
    ((unmatched_admitted_iff before current holds).mp valid).2 future solution value readsAt⟩

/-- **From the reference to the step**, for determinate equations. -/
theorem run_of_evaluates [Fintype ι] (determinate : ∀ index, Determinate (program index))
    {call value : Term S Γ sort} (evaluated : Evaluates program call value) :
    ∃ before after, Relation.ReflTransGen (EquationTransition program) (initial call) before ∧
      UnmatchedTransition program before after ∧ Reads (withReturn program) after value := by
  obtain ⟨runs, unmatched⟩ := evaluated
  obtain ⟨before, path, fixes⟩ := equation_runs_fixes determinate runs
  have valid := (returns_iff before value fixes.determines).mpr unmatched
  exact ⟨before, unmatchedDestination program before valid, path, ⟨valid, rfl⟩,
    (unmatched_reads_iff before value fixes.determines valid value).mpr rfl⟩

/-- **Adequacy for evaluation with unmatched calls returned.** -/
theorem evaluates_iff [Fintype ι] (determinate : ∀ index, Determinate (program index)) (call value : Term S Γ sort) :
    Evaluates program call value ↔
      ∃ before after, Relation.ReflTransGen (EquationTransition program) (initial call) before ∧
        UnmatchedTransition program before after ∧ Reads (withReturn program) after value :=
  ⟨run_of_evaluates determinate, fun ⟨_, _, path, returned, reads⟩ => evaluates_of_run path returned reads⟩

#print axioms returned_readings_iff
#print axioms returns_iff
#print axioms unmatched_reads_iff
#print axioms returned_is_final
#print axioms equation_runs_backward
#print axioms equation_runs_fixes
#print axioms evaluates_of_run
#print axioms run_of_evaluates
#print axioms evaluates_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders
