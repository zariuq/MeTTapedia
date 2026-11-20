import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Authored
import Mathlib.Order.WellFounded

/-!
# Termination and infinite execution at the executable machine boundary

The authored partial-recursive machine is deterministic on the encoded image.
A bounded answer therefore makes every execution from that image terminate.
Conversely, failure to answer at every finite budget produces an explicit
infinite execution by iterating the existing frame step. These are statements
about the actual authored reduction, not a scheduler or a normalization
assumption supplied by a caller.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Progress

open Mettapedia.Languages.PartrecMachine
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Turing.ToPartrec

def Normalizing (term : Pattern) : Prop :=
  Acc (fun after before => machineTheory.Step before after) term

/-- An answer reached by a finite observation bounds all authored execution
from the same encoded state. -/
theorem normalizing_of_answer : ∀ (budget : Nat) (state : FrameState) (output : List Nat),
    SourceBudget.run budget state = .answer output → Normalizing (encFrameState state)
  | 0, state, output, answered => by
      have halted := (SourceBudget.observe_answer_iff state output).mp answered
      rw [halted]
      exact .intro _ fun _ step => False.elim (halt_irreducible output _
        ((reduces_iff_generatedStep _ _).mpr step))
  | budget + 1, state, output, answered => by
      refine .intro _ fun next stepped => ?_
      obtain ⟨_, rfl⟩ := (Authored.generated_step_iff state next).mp stepped
      apply normalizing_of_answer budget (frameStep state) output
      simpa only [SourceBudget.run, Function.iterate_succ_apply] using answered

/-- Every finite prefix that has not answered ends in a nonterminal frame. -/
theorem not_halted_of_no_answer (state : FrameState)
    (none : ∀ budget output, SourceBudget.run budget state ≠ .answer output) (budget : Nat) :
    isHalted (frameStep^[budget] state) = false := by
  generalize endpoint : frameStep^[budget] state = current
  rcases current with _ | _ | output
  · rfl
  · rfl
  · exact False.elim (none budget output (by simp [SourceBudget.run, endpoint, SourceBudget.observe]))

/-- The infinite execution is the sequence of actual frame-step iterates;
each edge is justified by the authored machine's existing adequacy law. -/
theorem infinite_of_no_answer (state : FrameState)
    (none : ∀ budget output, SourceBudget.run budget state ≠ .answer output) :
    ∃ states : Nat → Pattern, states 0 = encFrameState state ∧
      ∀ n, machineTheory.Step (states n) (states (n + 1)) := by
  refine ⟨fun n => encFrameState (frameStep^[n] state), rfl, ?_⟩
  intro n
  exact (Authored.generated_step_iff _ _).mpr
    ⟨not_halted_of_no_answer state none n,
      congrArg encFrameState (Function.iterate_succ_apply' frameStep n state)⟩

theorem normalizing_iff_eventually_answer (state : FrameState) :
    Normalizing (encFrameState state) ↔ ∃ budget output, SourceBudget.run budget state = .answer output := by
  constructor
  · intro normalizes
    by_contra noAnswer
    have none : ∀ budget output, SourceBudget.run budget state ≠ .answer output :=
      fun budget output answer => noAnswer ⟨budget, output, answer⟩
    exact (not_acc_iff_exists_descending_chain.mpr (infinite_of_no_answer state none)) normalizes
  · rintro ⟨budget, output, answered⟩
    exact normalizing_of_answer budget state output answered

/-- There is no additional normalization premise at this machine boundary:
termination is exactly definedness of the partial-recursive evaluation. -/
theorem normalizing_iff_defined (code : Code) (input : List Nat) :
    Normalizing (normalTerm code .halt input) ↔ (code.eval input).Dom := by
  rw [show normalTerm code .halt input = encFrameState (SourceBudget.start code input) from rfl,
    normalizing_iff_eventually_answer, Part.dom_iff_mem]
  constructor
  · rintro ⟨budget, output, answered⟩
    exact ⟨output, (SourceBudget.eventually_answer_iff code input output).mp ⟨budget, answered⟩⟩
  · rintro ⟨output, member⟩
    obtain ⟨budget, answered⟩ := (SourceBudget.eventually_answer_iff code input output).mpr member
    exact ⟨budget, output, answered⟩

/-- Divergence has an actual infinite sequence of authored steps, and no
infinite sequence is introduced for a code whose evaluation is defined. -/
theorem divergence_iff_infinite (code : Code) (input : List Nat) :
    code.eval input = Part.none ↔
      ∃ states : Nat → Pattern, states 0 = normalTerm code .halt input ∧
        ∀ n, machineTheory.Step (states n) (states (n + 1)) := by
  have negative : code.eval input = Part.none ↔ ¬ Normalizing (normalTerm code .halt input) :=
    Part.eq_none_iff'.trans (not_congr (normalizing_iff_defined code input).symm)
  exact negative.trans not_acc_iff_exists_descending_chain

namespace Controls

theorem successor_normalizes : Normalizing (normalTerm .succ .halt []) :=
  normalizing_of_answer 2 (SourceBudget.start .succ []) [1] rfl

/-- An explicit partial-recursive loop: its test always returns a nonzero
head, so the fixpoint resumes on the empty tail. -/
def loopCode : Code := .fix .succ

def loopReady : FrameState :=
  .inl (.succ, [.inr (.inr (.inr .succ))], [])

def loopReturned : FrameState :=
  .inr (.inl ([.inr (.inr (.inr .succ))], [1]))

theorem loop_entry : frameStep (SourceBudget.start loopCode []) = loopReady := rfl

theorem loop_cycle : frameStep loopReady = loopReturned ∧ frameStep loopReturned = loopReady :=
  ⟨rfl, rfl⟩

theorem loop_prefix (budget : Nat) :
    frameStep^[budget] loopReady = loopReady ∨ frameStep^[budget] loopReady = loopReturned := by
  induction budget with
  | zero => exact .inl rfl
  | succ budget ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with same | same
      · rw [same, loop_cycle.1]
        exact .inr rfl
      · rw [same, loop_cycle.2]
        exact .inl rfl

theorem loop_no_answer (budget : Nat) (output : List Nat) :
    SourceBudget.run budget (SourceBudget.start loopCode []) ≠ .answer output := by
  cases budget with
  | zero => intro impossible; cases impossible
  | succ budget =>
      change SourceBudget.observe (frameStep^[budget] loopReady) ≠ .answer output
      rcases loop_prefix budget with same | same
      · rw [same]
        intro impossible
        cases impossible
      · rw [same]
        intro impossible
        cases impossible

theorem loop_eval_none : loopCode.eval [] = Part.none := by
  apply Part.eq_none_iff.mpr
  intro output member
  obtain ⟨budget, answered⟩ := (SourceBudget.eventually_answer_iff loopCode [] output).mpr member
  exact loop_no_answer budget output answered

theorem loop_infinite :
    ∃ states : Nat → Pattern, states 0 = normalTerm loopCode .halt [] ∧
      ∀ n, machineTheory.Step (states n) (states (n + 1)) :=
  (divergence_iff_infinite loopCode []).mp loop_eval_none

/-- Starting the code again repeats its first prefix; resuming uses the
saved continuation and completes the second prefix. -/
theorem resuming_is_not_restarting :
    SourceBudget.resume 1 (SourceBudget.run 1 (SourceBudget.start .succ [])) = .answer [1] ∧
      SourceBudget.run 1 (SourceBudget.start .succ []) ≠ .answer [1] := by
  exact ⟨rfl, fun impossible => by cases impossible⟩

theorem silent_has_infinite_execution (input : List Nat) :
    ∃ states : Nat → Pattern, states 0 = normalTerm silent .halt input ∧
      ∀ n, machineTheory.Step (states n) (states (n + 1)) :=
  (divergence_iff_infinite silent input).mp (silent_eval input)

end Controls

#print axioms normalizing_of_answer
#print axioms infinite_of_no_answer
#print axioms normalizing_iff_defined
#print axioms divergence_iff_infinite
#print axioms Controls.loop_eval_none
#print axioms Controls.loop_infinite
#print axioms Controls.silent_has_infinite_execution

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Progress
