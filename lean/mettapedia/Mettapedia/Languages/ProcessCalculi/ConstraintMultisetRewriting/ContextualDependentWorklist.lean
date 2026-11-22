import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUpdate
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SearchOutcome

/-!
# The worklist driver: soundness, no lost solution, progress and fragment completeness

A **solver** inspects the residual store of the current state and reports one round
(`Round`): progress by a solver update whose rank is lexicographically smaller, a certified
refutation, or stuck (only residual or postponed equations remain for it). The rank is chosen by
the solver; the intended reading is the number of unsolved metavariables, then the size of the
pattern equations.

The **driver** (`drive`) keeps one solver update from the original store to the current residual
store, composes each round's update onto it, and stops when the store is empty, when the solver
refutes or is stuck, or when its budget of rounds is spent. Because the state is an update of
the original store:

* **soundness**: every solution of the reported residual store, composed with the reported
  answer, solves the original store (`Outcome.sound`);
* **no solution lost**: every original solution factors through the reported answer and a
  solution of the reported residual store, and a refutation is reported only for a store without
  solutions (`drive_no_loss`, `drive_refuted`);
* a solved outcome carries a **principal answer** (`drive_solved_principal`);
* **progress**: every round lowers a well-founded rank or ends the run, so the driver reaches a
  finished outcome at some finite budget (`drive_finishes`), and a finished outcome is the same at
  every larger budget (`drive_mono`);
* **fragment completeness**: on any class of stores that the solver's updates preserve and on
  which it is never stuck before the store is empty, the driver reaches a principal answer or a
  certified refutation at some budget and at every larger budget (`Fragment.decided`);
* **incomplete is never none**: the existence readout of a cut-off or stuck run is `suspended`,
  never `refuted`, and a solvable store, in particular one whose non-pattern equations have
  solutions, is never refuted (`readout_eq_refuted`, `drive_not_refuted_of_solvable`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentWorklist

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}

/-- The order of ranks: lexicographic on pairs of natural numbers. -/
def Below (first second : Nat × Nat) : Prop :=
  Prod.Lex (· < ·) (· < ·) first second

theorem below_wf : WellFounded Below := (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf

/-! ## Solvers -/

variable (levels : LevelModel rules L)

/-- **The outcome of one round** on a residual store. Progress carries the decrease of the
rank; refutation carries the absence of solutions; stuck claims nothing. -/
inductive Round (rank : {Γ : Context rules} → EquationStore (TotalTerm Γ) → Nat × Nat)
    {Γ : Context rules} (problem : EquationStore (TotalTerm Γ)) : Type where
  | progress (update : Update levels problem) (smaller : Below (rank update.remaining) (rank problem))
  | refuted (absent : ¬ (frames levels).Solvable problem)
  | stuck

/-- **A solver step**: a rank of stores and one round at every store. -/
structure Solver where
  rank : {Γ : Context rules} → EquationStore (TotalTerm Γ) → Nat × Nat
  round : {Γ : Context rules} → (problem : EquationStore (TotalTerm Γ)) → Round levels rank problem

/-! ## The driver -/

/-- **The outcome of a run** from an original store. Every outcome but a refutation carries the
update from the original store to the reported residual store. -/
inductive Outcome {Γ : Context rules} (original : EquationStore (TotalTerm Γ)) : Type where
  | solved (state : Update levels original) (finished : state.remaining = [])
  | refuted (absent : ¬ (frames levels).Solvable original)
  | stuck (state : Update levels original)
  | cutoff (state : Update levels original)

variable {levels}

/-- What one round does to the driver's state: finish the run, or continue from a new state. -/
inductive Decision {Γ : Context rules} (original : EquationStore (TotalTerm Γ)) : Type where
  | done (outcome : Outcome levels original)
  | next (state : Update levels original)

/-- One round of the driver. -/
def advance (solver : Solver levels) {Γ : Context rules} {original : EquationStore (TotalTerm Γ)}
    (state : Update levels original) : Decision (levels := levels) original :=
  match finished : state.remaining with
  | [] => .done (.solved state finished)
  | _ :: _ =>
      match solver.round state.remaining with
      | .progress update _ => .next (state.then update)
      | .refuted absent => .done (.refuted fun solvable => absent (state.solvable_iff.mp solvable))
      | .stuck => .done (.stuck state)

/-- **The driver** with a budget of rounds. -/
def drive (solver : Solver levels) {Γ : Context rules} {original : EquationStore (TotalTerm Γ)} :
    Nat → Update levels original → Outcome levels original
  | 0, state => .cutoff state
  | fuel + 1, state =>
      match advance solver state with
      | .done outcome => outcome
      | .next next => drive solver fuel next

/-- A run from the original store itself. -/
def run (solver : Solver levels) {Γ : Context rules} (original : EquationStore (TotalTerm Γ))
    (fuel : Nat) : Outcome levels original :=
  drive solver fuel (Update.pending levels original)

namespace Outcome

variable {Γ : Context rules} {original : EquationStore (TotalTerm Γ)}

/-- The reported update, unless the run refuted the store. -/
def state? : Outcome levels original → Option (Update levels original)
  | .solved state _ => some state
  | .refuted _ => none
  | .stuck state => some state
  | .cutoff state => some state

/-- The run ended for a reason other than its budget. -/
def Finished : Outcome levels original → Prop
  | .cutoff _ => False
  | _ => True

/-- The run reached a principal answer or a refutation. -/
def Decided : Outcome levels original → Prop
  | .solved _ _ => True
  | .refuted _ => True
  | _ => False

theorem Decided.finished {outcome : Outcome levels original} (decided : outcome.Decided) :
    outcome.Finished := by
  cases outcome <;> simp_all [Decided, Finished]

/-- **Soundness**: a solution of the reported residual store, composed with the reported answer,
solves the original store. -/
theorem sound (outcome : Outcome levels original) :
    ∀ state ∈ outcome.state?, ∀ (Δ : Context rules) (residual : Δ ⟶ state.target),
      (frames levels).Models residual state.remaining →
        (frames levels).Models (residual ≫ state.answer) original :=
  fun state _ Δ residual solved => state.sound Δ residual solved

/-- **The existence readout** of a run: a principal answer commits, a refutation refutes, and
every other outcome is suspended. -/
def readout : Outcome levels original → Search.Outcome.Verdict
  | .solved _ _ => .commit
  | .refuted _ => .refuted
  | .stuck _ => .suspended
  | .cutoff _ => .suspended

/-- **Incomplete is never none**: only a certified refutation reads `refuted`. -/
theorem readout_eq_refuted {outcome : Outcome levels original}
    (refuted : outcome.readout = .refuted) : ¬ (frames levels).Solvable original := by
  cases outcome with
  | refuted absent => exact absent
  | solved _ _ => cases refuted
  | stuck _ => cases refuted
  | cutoff _ => cases refuted

theorem readout_cutoff (state : Update levels original) :
    (Outcome.cutoff state).readout = Search.Outcome.Verdict.suspended := rfl

end Outcome

section Driver

variable (solver : Solver levels) {Γ : Context rules} {original : EquationStore (TotalTerm Γ)}

theorem drive_zero (state : Update levels original) : drive solver 0 state = .cutoff state := rfl

theorem drive_succ (fuel : Nat) (state : Update levels original) :
    drive solver (fuel + 1) state =
      match advance solver state with
      | .done outcome => outcome
      | .next next => drive solver fuel next := rfl

/-- A round that continues lowers the rank. -/
theorem advance_next {state next : Update levels original}
    (continued : advance solver state = .next next) :
    Below (solver.rank next.remaining) (solver.rank state.remaining) := by
  unfold advance at continued
  split at continued
  · cases continued
  · split at continued
    · rename_i update smaller _
      cases continued
      exact smaller
    · cases continued
    · cases continued

/-- A round that ends the run ends it for a reason other than the budget. -/
theorem advance_done_finished {state : Update levels original} {outcome : Outcome levels original}
    (ended : advance solver state = .done outcome) : outcome.Finished := by
  unfold advance at ended
  split at ended
  · cases ended
    trivial
  · split at ended
    · cases ended
    · cases ended
      trivial
    · cases ended
      trivial

/-- A round ends the run with a stuck outcome only for a nonempty store at which the solver is
stuck. -/
theorem advance_done_stuck {state : Update levels original} {outcome : Outcome levels original}
    (ended : advance solver state = .done outcome) (undecided : ¬ outcome.Decided) :
    state.remaining ≠ [] ∧ solver.round state.remaining = .stuck := by
  unfold advance at ended
  split at ended
  · cases ended
    exact absurd trivial undecided
  · rename_i first rest nonempty
    split at ended
    · cases ended
    · cases ended
      exact absurd trivial undecided
    · rename_i isStuck
      exact ⟨by rw [nonempty]; exact List.cons_ne_nil first rest, isStuck⟩

/-- A round that continues continues with the solver's update. -/
theorem advance_next_progress {state next : Update levels original}
    (continued : advance solver state = .next next) :
    ∃ update smaller, solver.round state.remaining = .progress update smaller ∧
      next = state.then update := by
  unfold advance at continued
  split at continued
  · cases continued
  · split at continued
    · rename_i update smaller isProgress
      cases continued
      exact ⟨update, smaller, isProgress, rfl⟩
    · cases continued
    · cases continued

/-- **Budget monotonicity**: a finished outcome is the outcome at every larger budget. -/
theorem drive_mono : ∀ (fuel : Nat) (state : Update levels original),
    (drive solver fuel state).Finished → ∀ larger, fuel ≤ larger →
      drive solver larger state = drive solver fuel state
  | 0, _, finished, _, _ => False.elim finished
  | _ + 1, _, _, 0, enough => absurd enough (Nat.not_succ_le_zero _)
  | fuel + 1, state, finished, larger + 1, enough => by
      rw [drive_succ, drive_succ]
      rw [drive_succ] at finished
      cases decided : advance solver state with
      | done _ => rfl
      | next next =>
          rw [decided] at finished
          exact drive_mono fuel next finished larger (Nat.le_of_succ_le_succ enough)

/-- **Progress**: every run reaches a finished outcome at some finite budget. -/
theorem drive_finishes (state : Update levels original) :
    ∃ fuel, (drive solver fuel state).Finished := by
  suffices key : ∀ rank (state : Update levels original), solver.rank state.remaining = rank →
      ∃ fuel, (drive solver fuel state).Finished from key _ state rfl
  intro rank
  refine below_wf.induction (C := fun rank => ∀ state : Update levels original,
    solver.rank state.remaining = rank → ∃ fuel, (drive solver fuel state).Finished) rank ?_
  intro rank ih state ranked
  cases decided : advance solver state with
  | done _ =>
      refine ⟨1, ?_⟩
      rw [drive_succ, decided]
      exact advance_done_finished solver decided
  | next next =>
      have smaller := advance_next solver decided
      rw [ranked] at smaller
      obtain ⟨fuel, finished⟩ := ih _ smaller next rfl
      refine ⟨fuel + 1, ?_⟩
      rw [drive_succ, decided]
      exact finished

/-- **No solution is lost**: an original solution is never refuted, and it factors through the
reported answer and a solution of the reported residual store. -/
theorem drive_no_loss (fuel : Nat) (start : Update levels original) {Δ : Context rules}
    (solution : Δ ⟶ Γ) (solved : (frames levels).Models solution original) :
    ∃ state, (drive solver fuel start).state? = some state ∧
      ∃ residual : Δ ⟶ state.target, (frames levels).Models residual state.remaining ∧
        ∀ term : TotalTerm Γ,
          (frames levels).E (term.reindex solution) (term.reindex (residual ≫ state.answer)) := by
  cases outcome : drive solver fuel start with
  | refuted absent => exact absurd ⟨Δ, solution, solved⟩ absent
  | solved state _ => exact ⟨state, rfl, state.complete Δ solution solved⟩
  | stuck state => exact ⟨state, rfl, state.complete Δ solution solved⟩
  | cutoff state => exact ⟨state, rfl, state.complete Δ solution solved⟩

/-- **A refutation is certified.** -/
theorem drive_refuted (fuel : Nat) (start : Update levels original)
    (refuted : (drive solver fuel start).readout = .refuted) :
    ¬ (frames levels).Solvable original :=
  Outcome.readout_eq_refuted refuted

/-- A solvable store, whatever its non-pattern residual equations, is never refuted. -/
theorem drive_not_refuted_of_solvable (solvable : (frames levels).Solvable original)
    (fuel : Nat) (start : Update levels original) :
    (drive solver fuel start).readout ≠ .refuted :=
  fun refuted => drive_refuted solver fuel start refuted solvable

/-- **A solved run carries a principal answer** for the original store. -/
theorem drive_solved_principal {fuel : Nat} {start state : Update levels original}
    {finished : state.remaining = []} (_ : drive solver fuel start = .solved state finished) :
    (frames levels).Principal original state.answer :=
  state.completed finished

end Driver

/-! ## Fragment completeness -/

variable (solver : Solver levels)

/-- **A fragment for a solver**: a class of stores preserved by its updates, on which it is
never stuck before the store is empty. -/
structure Fragment where
  holds : {Γ : Context rules} → EquationStore (TotalTerm Γ) → Prop
  stable : ∀ {Γ : Context rules} {problem : EquationStore (TotalTerm Γ)}
    {update : Update levels problem}
    {smaller : Below (solver.rank update.remaining) (solver.rank problem)},
    holds problem → solver.round problem = .progress update smaller → holds update.remaining
  decisive : ∀ {Γ : Context rules} {problem : EquationStore (TotalTerm Γ)},
    holds problem → problem ≠ [] → solver.round problem ≠ .stuck

namespace Fragment

variable {solver} (fragment : Fragment solver)
variable {Γ : Context rules} {original : EquationStore (TotalTerm Γ)}

/-- From every state in the fragment, the driver decides the original store at some budget. -/
theorem decides (state : Update levels original) (inside : fragment.holds state.remaining) :
    ∃ fuel, (drive solver fuel state).Decided := by
  suffices key : ∀ rank (state : Update levels original), solver.rank state.remaining = rank →
      fragment.holds state.remaining → ∃ fuel, (drive solver fuel state).Decided from
    key _ state rfl inside
  intro rank
  refine below_wf.induction (C := fun rank => ∀ state : Update levels original,
    solver.rank state.remaining = rank → fragment.holds state.remaining →
      ∃ fuel, (drive solver fuel state).Decided) rank ?_
  intro rank ih state ranked inside
  cases decided : advance solver state with
  | done _ =>
      refine ⟨1, ?_⟩
      rw [drive_succ, decided]
      by_contra undecided
      obtain ⟨nonempty, isStuck⟩ := advance_done_stuck solver decided undecided
      exact fragment.decisive inside nonempty isStuck
  | next next =>
      have smaller := advance_next solver decided
      rw [ranked] at smaller
      obtain ⟨update, _, isProgress, rfl⟩ := advance_next_progress solver decided
      obtain ⟨fuel, reached⟩ := ih _ smaller (state.then update) rfl
        (fragment.stable (update := update) inside isProgress)
      refine ⟨fuel + 1, ?_⟩
      rw [drive_succ, decided]
      exact reached

/-- **Fragment completeness**: on the fragment, the run from the original store reaches either
a principal answer or a certified refutation at some finite budget, and the same outcome at
every larger budget. -/
theorem decided (inside : fragment.holds original) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run solver original larger = run solver original fuel ∧
      ((∃ state finished, run solver original larger = .solved state finished ∧
          (frames levels).Principal original state.answer) ∨
        (∃ absent, run solver original larger = .refuted absent)) := by
  obtain ⟨fuel, reached⟩ := fragment.decides (Update.pending levels original) inside
  refine ⟨fuel, fun larger enough => ?_⟩
  have same := drive_mono solver fuel _ reached.finished larger enough
  refine ⟨same, ?_⟩
  unfold run
  rw [same]
  cases outcome : drive solver fuel (Update.pending levels original) with
  | solved state finished => exact .inl ⟨state, finished, rfl, state.completed finished⟩
  | refuted absent => exact .inr ⟨absent, rfl⟩
  | stuck _ => rw [outcome] at reached; exact False.elim reached
  | cutoff _ => rw [outcome] at reached; exact False.elim reached

end Fragment

/-! ## The stores the solver decides -/

/-- **The stores a solver decides**: the empty store, a store it refutes, and a store from which
one of its rounds progresses to a store it decides. -/
inductive Reaches : {Γ : Context rules} → EquationStore (TotalTerm Γ) → Prop where
  | empty {Γ : Context rules} : Reaches (Γ := Γ) []
  | refuted {Γ : Context rules} {problem : EquationStore (TotalTerm Γ)}
      {absent : ¬ (frames levels).Solvable problem} :
      solver.round problem = .refuted absent → Reaches problem
  | progress {Γ : Context rules} {problem : EquationStore (TotalTerm Γ)}
      {update : Update levels problem}
      {smaller : Below (solver.rank update.remaining) (solver.rank problem)} :
      solver.round problem = .progress update smaller → Reaches update.remaining → Reaches problem

/-- **The decided stores form a fragment** for every solver that does nothing at the empty
store. -/
def Reaches.fragment
    (nil : ∀ {Γ : Context rules}, solver.round ([] : EquationStore (TotalTerm Γ)) = .stuck) :
    Fragment solver where
  holds := Reaches solver
  stable := by
    intro Γ problem update smaller inside isProgress
    cases inside with
    | empty => rw [nil] at isProgress; cases isProgress
    | refuted isRefuted => rw [isRefuted] at isProgress; cases isProgress
    | progress isProgress' next =>
        rw [isProgress'] at isProgress
        cases isProgress
        exact next
  decisive := by
    intro Γ problem inside nonempty isStuck
    cases inside with
    | empty => exact nonempty rfl
    | refuted isRefuted => rw [isRefuted] at isStuck; cases isStuck
    | progress isProgress _ => rw [isProgress] at isStuck; cases isStuck

/-- An executable check that the solver decides a store within a number of rounds. -/
def decidesWithin : Nat → (Γ : Context rules) → EquationStore (TotalTerm Γ) → Bool
  | _, _, [] => true
  | 0, _, _ :: _ => false
  | fuel + 1, _, first :: rest =>
      match solver.round (first :: rest) with
      | .progress update _ => decidesWithin fuel update.target update.remaining
      | .refuted _ => true
      | .stuck => false

/-- **A successful check certifies membership in the decided stores.** -/
theorem Reaches.of_decidesWithin : ∀ (fuel : Nat) (Γ : Context rules)
    (problem : EquationStore (TotalTerm Γ)), decidesWithin solver fuel Γ problem = true →
      Reaches solver problem
  | _, _, [], _ => .empty
  | 0, _, _ :: _, decided => by simp [decidesWithin] at decided
  | fuel + 1, _, first :: rest, decided => by
      simp only [decidesWithin] at decided
      split at decided
      · rename_i _ _ isProgress
        exact .progress isProgress (Reaches.of_decidesWithin fuel _ _ decided)
      · rename_i _ isRefuted
        exact .refuted isRefuted
      · cases decided

end ContextualDependentWorklist
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
