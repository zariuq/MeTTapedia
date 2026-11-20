import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.PartialRecursive
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.RunBounds

/-!
# Actual run controls for the finite machine program

The nested program uses its captured input twice before returning the tail.
Its actual firing runs answer after exactly ten events, and a five-event
prefix resumes from its saved native state. The negative compiler variant
omits the empty-input successor rule and therefore cannot satisfy even the
forward local comparison at that initialized state.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.PartialRecursive.Controls

open Mettapedia.Languages.PartrecMachine
open Turing.ToPartrec
open Mettapedia.GSLT.IndexedOperational
open FragmentsOfTheStep.TransitionMaps
open LogicOverTheStep.StepSpan (Succ)
open RuleSyntax.Presentation.Schematic (SState schematicStep)
open RuleSyntax.Machines.PartialRecursive (HaltedWith)

def nested : Code := .cons .succ (.cons .succ .tail)
def nestedInput : List Nat := [2, 4, 9]
def nestedOutput : List Nat := [3, 3, 4, 9]

theorem nested_source_ten :
    SourceBudget.run 10 (SourceBudget.start nested nestedInput) = .answer nestedOutput := rfl

theorem nested_source_not_nine (output : List Nat) :
    SourceBudget.run 9 (SourceBudget.start nested nestedInput) ≠ .answer output := by
  intro impossible
  cases impossible

theorem nested_every_prefix_bounded (run : native.Run (start nested nestedInput)) :
    run.word.length ≤ 10 :=
  NativeBudget.length_le_of_answer native comparison 10 (initial nested nestedInput) nested_source_ten run

theorem nested_no_short_answer (run : native.Run (start nested nestedInput))
    (short : run.word.length ≤ 9) (output : List Nat) : ¬ HaltedWith output run.last := by
  intro answered
  exact nested_source_not_nine output
    ((bounded_answer_iff 9 nested nestedInput output).mp ⟨run, short, answered⟩)

theorem nested_actual_ten :
    ∃ run : native.Run (start nested nestedInput), run.word.length = 10 ∧ HaltedWith nestedOutput run.last := by
  obtain ⟨run, short, answered⟩ := (bounded_answer_iff 10 nested nestedInput nestedOutput).mpr nested_source_ten
  refine ⟨run, ?_, answered⟩
  by_contra different
  have shorter : run.word.length ≤ 9 := by omega
  exact nested_no_short_answer run shorter nestedOutput answered

def fiveSteps : ExecutionPath Authored.frames (SourceBudget.start nested nestedInput)
    (frameStep^[5] (SourceBudget.start nested nestedInput)) :=
  .cons ⟨⟨rfl, rfl⟩⟩ (.cons ⟨⟨rfl, rfl⟩⟩ (.cons ⟨⟨rfl, rfl⟩⟩
    (.cons ⟨⟨rfl, rfl⟩⟩ (.cons ⟨⟨rfl, rfl⟩⟩ (.refl _)))))

/-- Resumption keeps the actual five-event prefix and its native endpoint,
including the bindings and fresh identities acquired while executing it. -/
theorem nested_resumes :
    ∃ earlier : native.Run (start nested nestedInput), ∃ later : native.Run earlier.last,
      earlier.word.length = 5 ∧ later.word.length = 5 ∧ HaltedWith nestedOutput later.last ∧
        (earlier.append later).word = earlier.word ++ later.word := by
  obtain ⟨earlier, _, length⟩ := NativeBudget.lift_path native comparison fiveSteps (initial nested nestedInput)
  have earlierLength : earlier.word.length = 5 := length
  have future : SourceBudget.run (earlier.word.length + 5) (SourceBudget.start nested nestedInput) =
      .answer nestedOutput := by simpa only [earlierLength] using nested_source_ten
  obtain ⟨later, short, answered, word⟩ := NativeBudget.resumed_word native comparison HaltedWith observation
    (initial nested nestedInput) earlier 5 nestedOutput future
  refine ⟨earlier, later, earlierLength, ?_, answered, word⟩
  by_contra different
  have smaller : later.word.length ≤ 4 := by omega
  have wholeShort : (earlier.append later).word.length ≤ 9 := by
    rw [word, List.length_append, earlierLength]
    omega
  have wholeAnswer : HaltedWith nestedOutput (earlier.append later).last := by
    rw [Interface.Step.Run.last_append]
    exact answered
  exact nested_no_short_answer (earlier.append later) wholeShort nestedOutput wholeAnswer

theorem explicit_loop_native_events :
    ∃ states : Nat → SState Nat, states 0 = start Progress.Controls.loopCode [] ∧
      Nonempty ((n : Nat) → native.toEffectCore.Event native.eventAdmission (states n) (states (n + 1))) :=
  (divergence_iff_events Progress.Controls.loopCode []).mp Progress.Controls.loop_eval_none

/-- The missing-rule variant is a real positive rule program, but the
local forward licence cannot hold at the missing input. -/
theorem missing_rule_breaks_comparison :
    ¬ ∃ related : FrameState → SState Nat → Prop,
      IsBisimulation Authored.frames.Step
        (Succ (schematicStep Nat RuleSyntax.Machines.PartialRecursive.withoutSuccOnEmpty).toStep) related ∧
      related (SourceBudget.start .succ []) (start .succ []) := by
  rintro ⟨related, compared, atStart⟩
  obtain ⟨after, ⟨firing, admitted, _⟩, _⟩ := compared.1 atStart
    (show Authored.frames.Step (SourceBudget.start .succ [])
      (frameStep (SourceBudget.start .succ [])) from ⟨rfl, rfl⟩)
  exact RuleSyntax.Machines.PartialRecursive.withoutSuccOnEmpty_stuck.2 firing admitted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.PartialRecursive.Controls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.PartialRecursive.Controls.nested_actual_ten
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.PartialRecursive.Controls.nested_resumes
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.PartialRecursive.Controls.missing_rule_breaks_comparison
