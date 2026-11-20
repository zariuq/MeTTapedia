import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Progress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Transitions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Execution

/-!
# Bounded actual firing runs from a local machine correspondence

The hypotheses are local: an existing strong transition comparison between
the executable continuation-frame machine and an actual `Interface.Step`,
and agreement of the declared output observation at related states.

Induction on actual firing runs gives exact prefix readback. Induction on
the observation budget gives both directions of bounded acceptance, with
unused budget retained at a halted state. Resumption begins at the supplied
native prefix's literal endpoint and keeps its firing word. Termination and
infinite execution follow from the concrete frame-machine progress theorem.

These are transport laws. A concrete compiler must still supply the local
comparison, initialization relation and output law; no compiler instance is
asserted by this module.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.NativeBudget

open Mettapedia.Languages.PartrecMachine
open Turing.ToPartrec
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational Mettapedia.GSLT.Ultrainfinite
open FragmentsOfTheStep.TransitionMaps
open LogicOverTheStep.StepSpan (Succ)
open Interface (Frames)
open Interface.Bridges

universe uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  (P : Interface.Step X O State Firing)
  {related : FrameState → State → Prop}
  (comparison : IsBisimulation Authored.frames.Step (Succ P) related)

include comparison

/-- Every admitted native event advances the executable frame machine
once and relates the literal native result to that computed successor. -/
theorem read_firing {frame : FrameState} {state : State} (atFrame : related frame state)
    (firing : Firing state) (admitted : P.Admits firing) :
    isHalted frame = false ∧ related (frameStep frame) (P.result firing admitted) := by
  obtain ⟨after, sourceStep, atAfter⟩ := comparison.2 atFrame ⟨firing, admitted, rfl⟩
  obtain ⟨notHalted, rfl⟩ := sourceStep
  exact ⟨notHalted, atAfter⟩

/-- Every nonterminal frame step has an actual admitted native firing. -/
theorem fire_frame {frame : FrameState} {state : State} (atFrame : related frame state)
    (notHalted : isHalted frame = false) :
    ∃ firing : Firing state, ∃ admitted : P.Admits firing,
      related (frameStep frame) (P.result firing admitted) := by
  obtain ⟨after, ⟨firing, admitted, endpoint⟩, atAfter⟩ :=
    comparison.1 atFrame (show Authored.frames.Step frame (frameStep frame) from ⟨notHalted, rfl⟩)
  subst endpoint
  exact ⟨firing, admitted, atAfter⟩

/-- Arbitrary supplied native runs, including unfinished prefixes, have
the endpoint of exactly as many executable frame steps as native events. -/
theorem run_endpoint {frame : FrameState} {state : State} (atFrame : related frame state)
    (run : P.Run state) : related (frameStep^[run.word.length] frame) run.last := by
  induction run generalizing frame with
  | nil => exact atFrame
  | cons firing admitted rest ih =>
      have next := (read_firing P comparison atFrame firing admitted).2
      simpa only [Interface.Step.Run.word, Interface.Step.Run.last, List.length_cons,
        Function.iterate_succ_apply] using ih next

/-- The source path is derived from the actual native event sequence;
no extra source transition is supplied as a premise. -/
def sourcePath : ∀ {state : State} (frame : FrameState), related frame state →
    (run : P.Run state) → ExecutionPath Authored.frames frame (frameStep^[run.word.length] frame)
  | _, frame, _, .nil _ => .refl frame
  | _, frame, atFrame, .cons firing admitted rest => by
      have facts := read_firing P comparison atFrame firing admitted
      have tail := sourcePath (frameStep frame) facts.2 rest
      simpa only [Interface.Step.Run.word, List.length_cons, Function.iterate_succ_apply] using
        (Route.cons (PLift.up (show Authored.frames.Step frame (frameStep frame) from ⟨facts.1, rfl⟩)) tail)

theorem sourcePath_length {frame : FrameState} {state : State} (atFrame : related frame state)
    (run : P.Run state) : (sourcePath P comparison frame atFrame run).length = run.word.length := by
  induction run generalizing frame with
  | nil => rfl
  | cons firing admitted rest ih =>
      simpa only [sourcePath, id_eq, Route.length, Interface.Step.Run.word, List.length_cons] using
        congrArg (· + 1) (ih (read_firing P comparison atFrame firing admitted).2)

/-- Every supplied finite frame path lifts to an actual native run with
exactly as many events, including paths that have not reached an answer. -/
theorem lift_path : ∀ {first last : FrameState} (path : ExecutionPath Authored.frames first last)
    {state : State}, related first state →
      ∃ run : P.Run state, related last run.last ∧ run.word.length = path.length
  | _, _, .refl _, state, atFrame => ⟨.nil state, atFrame, rfl⟩
  | _, _, .cons edge rest, _, atFrame => by
      obtain ⟨after, ⟨firing, admitted, endpoint⟩, atAfter⟩ := comparison.1 atFrame edge.down
      subst endpoint
      obtain ⟨run, relatedEnd, length⟩ := lift_path rest atAfter
      exact ⟨.cons firing admitted run, relatedEnd, congrArg (· + 1) length⟩

section Answers

variable (observes : List Nat → State → Prop)
  (observation : ∀ {frame : FrameState} {state : State}, related frame state → ∀ output,
    observes output state ↔ SourceBudget.observe frame = .answer output)

def AnswersWithin (budget : Nat) (state : State) (output : List Nat) : Prop :=
  ∃ run : P.Run state, run.word.length ≤ budget ∧ observes output run.last

include observation

/-- The bound concerns actual events; a halted iterator's padding never
becomes additional native work. -/
theorem bounded_answer_iff (budget : Nat) {frame : FrameState} {state : State}
    (atFrame : related frame state) (output : List Nat) :
    AnswersWithin P observes budget state output ↔ SourceBudget.run budget frame = .answer output := by
  constructor
  · rintro ⟨run, short, answered⟩
    have exactAnswer : SourceBudget.run run.word.length frame = .answer output :=
      (observation (run_endpoint P comparison atFrame run) output).mp answered
    have longer := SourceBudget.answer_persists exactAnswer (budget - run.word.length)
    simpa only [Nat.add_sub_of_le short] using longer
  · intro answered
    induction budget generalizing frame state with
    | zero =>
        exact ⟨.nil state, Nat.le_refl 0, (observation atFrame output).mpr answered⟩
    | succ budget ih =>
        by_cases halted : isHalted frame = true
        · have observed : SourceBudget.observe frame = .answer output := by
            simpa only [SourceBudget.run, Function.iterate_fixed (frameStep_halted halted)] using answered
          exact ⟨.nil state, Nat.zero_le _, (observation atFrame output).mpr observed⟩
        · have notHalted : isHalted frame = false := Bool.eq_false_iff.mpr halted
          obtain ⟨firing, admitted, atAfter⟩ := fire_frame P comparison atFrame notHalted
          have remaining : SourceBudget.run budget (frameStep frame) = .answer output := by
            simpa only [SourceBudget.run, Function.iterate_succ_apply] using answered
          obtain ⟨run, short, result⟩ := ih atAfter remaining
          exact ⟨.cons firing admitted run, Nat.succ_le_succ short, result⟩

/-- Resumption observes the literal endpoint of the supplied native
prefix. Re-starting the source program is not used by this theorem. -/
theorem resume_answer_iff {frame : FrameState} {state : State} (atFrame : related frame state)
    (earlier : P.Run state) (later : Nat) (output : List Nat) :
    AnswersWithin P observes later earlier.last output ↔
      SourceBudget.run (earlier.word.length + later) frame = .answer output := by
  rw [bounded_answer_iff P comparison observes observation later
    (run_endpoint P comparison atFrame earlier) output]
  have resumed := SourceBudget.resume_run earlier.word.length later frame
  have same : SourceBudget.run later (frameStep^[earlier.word.length] frame) =
      SourceBudget.run (earlier.word.length + later) frame := by
    simpa only [SourceBudget.resume, SourceBudget.run, SourceBudget.state_observe] using resumed
  rw [same]

theorem resumed_word {frame : FrameState} {state : State} (atFrame : related frame state)
    (earlier : P.Run state) (later : Nat) (output : List Nat)
    (answer : SourceBudget.run (earlier.word.length + later) frame = .answer output) :
    ∃ suffix : P.Run earlier.last, suffix.word.length ≤ later ∧ observes output suffix.last ∧
      (earlier.append suffix).word = earlier.word ++ suffix.word := by
  obtain ⟨suffix, short, observed⟩ :=
    (resume_answer_iff P comparison observes observation atFrame earlier later output).mpr answer
  exact ⟨suffix, short, observed, earlier.word_append suffix⟩

/-- The all-code result follows from finite bounds and the independent
source adequacy theorem, not from an assumed native halting equivalence. -/
theorem eventual_answer_iff (code : Code) (input output : List Nat) {state : State}
    (atStart : related (SourceBudget.start code input) state) :
    (∃ run : P.Run state, observes output run.last) ↔ output ∈ code.eval input := by
  rw [← SourceBudget.eventually_answer_iff]
  constructor
  · rintro ⟨run, observed⟩
    exact ⟨run.word.length,
      (bounded_answer_iff P comparison observes observation _ atStart output).mp ⟨run, le_rfl, observed⟩⟩
  · rintro ⟨budget, answered⟩
    obtain ⟨run, _, observed⟩ :=
      (bounded_answer_iff P comparison observes observation budget atStart output).mpr answered
    exact ⟨run, observed⟩

/-- Exhausting a prefix is compatible with a later native answer. -/
theorem zero_budget_not_refusal {state : State}
    (atStart : related (SourceBudget.start .succ []) state) :
    ¬ AnswersWithin P observes 0 state [1] ∧ ∃ run : P.Run state, observes [1] run.last := by
  constructor
  · intro within
    have impossible := (bounded_answer_iff P comparison observes observation 0 atStart [1]).mp within
    cases impossible
  · exact (eventual_answer_iff P comparison observes observation .succ [] [1] atStart).mpr
      (by simp [Code.eval])

/-- The same finite exhaustion also occurs for the explicit looping code;
no budget may turn that status into an asserted answer. -/
theorem loop_has_no_bounded_answer {state : State}
    (atStart : related (SourceBudget.start Progress.Controls.loopCode []) state)
    (budget : Nat) (output : List Nat) : ¬ AnswersWithin P observes budget state output := by
  intro within
  exact Progress.Controls.loop_no_answer budget output
    ((bounded_answer_iff P comparison observes observation budget atStart output).mp within)

end Answers

omit comparison in
private theorem frames_authored :
    FunctionalBisimulation Authored.frames.Step machineTheory.Step encFrameState where
  zig := Authored.translation.mapStep
  zag := by
    intro frame target moved
    obtain ⟨notHalted, result⟩ := (Authored.generated_step_iff frame target).mp moved
    exact ⟨frameStep frame, ⟨notHalted, rfl⟩, result.symm⟩

/-- Strong normalization of the actual native relation is equivalent to
defined evaluation at a represented start, with no added silent divergence. -/
theorem normalizing_iff_defined (code : Code) (input : List Nat) {state : State}
    (atStart : related (SourceBudget.start code input) state) :
    Acc (fun after before => Succ P before after) state ↔ (code.eval input).Dom := by
  have native := (Transitions.normalization_iff comparison atStart).symm
  have authored := Transitions.normalization_iff (graph_isBisimulation_iff.mpr frames_authored)
    (origin := SourceBudget.start code input) rfl
  exact native.trans (authored.trans (Progress.normalizing_iff_defined code input))

theorem divergence_iff_infinite (code : Code) (input : List Nat) {state : State}
    (atStart : related (SourceBudget.start code input) state) :
    code.eval input = Part.none ↔
      ∃ states : Nat → State, states 0 = state ∧ ∀ n, Succ P (states n) (states (n + 1)) := by
  have negative : code.eval input = Part.none ↔
      ¬ Acc (fun after before => Succ P before after) state :=
    Part.eq_none_iff'.trans (not_congr (normalizing_iff_defined P comparison code input atStart).symm)
  exact negative.trans not_acc_iff_exists_descending_chain

/-- The infinite correspondence can retain an actual admitted event at
every index, including its original firing data. -/
theorem divergence_iff_events (code : Code) (input : List Nat) {state : State}
    (atStart : related (SourceBudget.start code input) state) :
    code.eval input = Part.none ↔
      ∃ states : Nat → State, states 0 = state ∧
        Nonempty ((n : Nat) → P.toEffectCore.Event P.eventAdmission (states n) (states (n + 1))) := by
  constructor
  · intro diverges
    obtain ⟨states, initial, steps⟩ := (divergence_iff_infinite P comparison code input atStart).mp diverges
    have events : ∀ n, Nonempty (P.toEffectCore.Event P.eventAdmission (states n) (states (n + 1))) := by
      intro n
      obtain ⟨firing, admitted, endpoint⟩ := steps n
      exact ⟨⟨firing, P.prepares admitted, admitted, endpoint⟩⟩
    exact ⟨states, initial, ⟨fun n => Classical.choice (events n)⟩⟩
  · rintro ⟨states, initial, ⟨events⟩⟩
    apply (divergence_iff_infinite P comparison code input atStart).mpr
    exact ⟨states, initial, fun n => ⟨(events n).firing, (events n).permitted, (events n).target_eq⟩⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.NativeBudget

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.NativeBudget.run_endpoint
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.NativeBudget.bounded_answer_iff
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.NativeBudget.resume_answer_iff
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.NativeBudget.normalizing_iff_defined
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.NativeBudget.divergence_iff_events
