import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.Driver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.PartialRecursive

/-!
# Executing the actual nineteen-schema table

The runtime functions here are `Table.applySchema`, `successors`, `next?`
and `drive`. They read the compiled table and use the existing matcher.
The source machine's successor function appears only in proofs of agreement.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.Program

open Mettapedia.Languages.PartrecMachine
open Turing.ToPartrec
open NamesOnTheStep (Expr)
open RuleSyntax.Machines (unknowns RootStep)
open RuleSyntax.Machines.PartialRecursive
  (Point names lhs rhs range mem_names successor successor_of_instance fires_of_successor eCfg eNats_injective)

def schemas : List Schema := names.map (fun name => (lhs name, rhs name))

theorem nineteen : schemas.length = 19 := rfl

theorem closed : ∀ schema ∈ schemas, ∀ name ∈ unknowns schema.2, name ∈ unknowns schema.1 := by
  intro schema member
  obtain ⟨name, _, rfl⟩ := List.mem_map.mp member
  exact range name

theorem root_step_point (point : Point) (result : Expr) :
    RootStep schemas point.row result ↔ ∃ after, successor point = some after ∧ result = after.row := by
  constructor
  · rintro ⟨schema, member, assignment, matched, output⟩
    obtain ⟨name, _, rfl⟩ := List.mem_map.mp member
    obtain ⟨after, stepped, made⟩ := successor_of_instance matched
    exact ⟨after, stepped, output.symm.trans made⟩
  · rintro ⟨after, stepped, rfl⟩
    obtain ⟨name, assignment, matched, made⟩ := fires_of_successor stepped
    exact ⟨_, List.mem_map_of_mem (mem_names name), assignment, matched, made⟩

theorem next_point (point : Point) : next? schemas point.row = (successor point).map Point.row := by
  cases step : successor point with
  | none =>
      cases selected : next? schemas point.row with
      | none => rfl
      | some result =>
          have rooted := (mem_successors_iff schemas closed point.row result).mp (next?_mem selected)
          obtain ⟨after, stepped, _⟩ := (root_step_point point result).mp rooted
          simp [step] at stepped
  | some after =>
      cases selected : next? schemas point.row with
      | none =>
          have member := (mem_successors_iff schemas closed point.row after.row).mpr
            ((root_step_point point after.row).mpr ⟨after, step, rfl⟩)
          rw [(next?_none_iff schemas point.row).mp selected] at member
          cases member
      | some result =>
          have rooted := (mem_successors_iff schemas closed point.row result).mp (next?_mem selected)
          obtain ⟨actual, stepped, same⟩ := (root_step_point point result).mp rooted
          have equal : actual = after := Option.some.inj (stepped.symm.trans step)
          subst actual
          simp only [same, Option.map_some]

theorem point_successor (frame : FrameState) :
    successor (PartialRecursive.point frame) =
      if isHalted frame then none else some (PartialRecursive.point (frameStep frame)) := by
  cases halted : isHalted frame with
  | false =>
      have reduced : Reduces (PartialRecursive.point frame).pattern
          (PartialRecursive.point (frameStep frame)).pattern := by
        rw [PartialRecursive.point_pattern, PartialRecursive.point_pattern]
        exact (reduces_frameState_iff frame _).mpr ⟨halted, rfl⟩
      obtain ⟨after, stepped, same⟩ :=
        (RuleSyntax.Machines.PartialRecursive.reduces_iff_successor _ _).mp reduced
      have equal : after = PartialRecursive.point (frameStep frame) :=
        PartialRecursive.pattern_injective same.symm
      simpa only [equal, halted, Bool.false_eq_true, ↓reduceIte] using stepped
  | true =>
      rcases frame with _ | _ | output <;>
        simp_all [isHalted, PartialRecursive.point, successor]

theorem next_frame (frame : FrameState) :
    next? schemas (PartialRecursive.point frame).row =
      if isHalted frame then none else some (PartialRecursive.point (frameStep frame)).row := by
  rw [next_point, point_successor]
  cases isHalted frame <;> rfl

def render : SourceBudget.Result → Result
  | .answer output => .stopped (eCfg (.halt output))
  | .exhausted frame => .exhausted (PartialRecursive.point frame).row

theorem render_observe (frame : FrameState) :
    render (SourceBudget.observe frame) =
      if isHalted frame then .stopped (PartialRecursive.point frame).row
      else .exhausted (PartialRecursive.point frame).row := by
  rcases frame with _ | _ | _ <;> rfl

/-- The equality compares two independently implemented computations:
actual target-table matching and the existing executable source step. -/
theorem drive_agrees (budget : Nat) (frame : FrameState) :
    drive schemas budget (PartialRecursive.point frame).row = render (SourceBudget.run budget frame) := by
  induction budget generalizing frame with
  | zero =>
      simp only [drive, next_frame, SourceBudget.run, Function.iterate_zero_apply, render_observe]
      cases isHalted frame <;> rfl
  | succ budget ih =>
      cases halted : isHalted frame with
      | true =>
          simp only [drive, next_frame, halted, ↓reduceIte, SourceBudget.run,
            Function.iterate_fixed (frameStep_halted halted), render_observe]
      | false =>
          simpa only [drive, next_frame, halted, Bool.false_eq_true, ↓reduceIte, SourceBudget.run,
            Function.iterate_succ_apply] using ih (frameStep frame)

theorem render_stopped_iff (result : SourceBudget.Result) (output : List Nat) :
    render result = .stopped (eCfg (.halt output)) ↔ result = .answer output := by
  cases result with
  | answer value =>
      constructor
      · intro same
        have rows : eCfg (.halt value) = eCfg (.halt output) := Result.stopped.inj same
        have equal : value = output := eNats_injective (Expr.app.inj rows).2
        exact congrArg SourceBudget.Result.answer equal
      · intro same
        cases same
        rfl
  | exhausted frame => constructor <;> intro impossible <;> cases impossible

/-- The executable table's bounded result agrees with an actual admitted
firing run under the same event budget, for all codes and inputs. -/
theorem stopped_iff_native (budget : Nat) (code : Code) (input output : List Nat) :
    drive schemas budget (RuleSyntax.Machines.PartialRecursive.eNormal code .halt input) =
        .stopped (eCfg (.halt output)) ↔
      ∃ run : PartialRecursive.native.Run (PartialRecursive.start code input),
        run.word.length ≤ budget ∧ RuleSyntax.Machines.PartialRecursive.HaltedWith output run.last := by
  change drive schemas budget (PartialRecursive.point (SourceBudget.start code input)).row = _ ↔ _
  rw [drive_agrees, render_stopped_iff]
  exact (PartialRecursive.bounded_answer_iff budget code input output).symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.Program

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.Program.next_point
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.Program.drive_agrees
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.Program.stopped_iff_native
