import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.PartialRecursive

/-!
# Existing Mathlib macro paths as actual firing runs

The authored machine expands an eager Mathlib step into a finite path.
These paths lift to actual runs of the nineteen-rule program with exactly
the same number of events. The structural bounds from `MacroCost` therefore
apply to these native runs. They count firings, not matching time or bytes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.PartialRecursive

open Mettapedia.Languages.PartrecMachine
open Turing.ToPartrec
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open RuleSyntax.Presentation.Schematic (SState)
open RuleSyntax.Machines (ReadsBag)
open RuleSyntax.Machines.PartialRecursive (Point eCfg)

def frameOfCfg : Cfg → FrameState
  | .halt output => .inr (.inr output)
  | .ret continuation input => .inr (.inl (framesOf continuation, input))

theorem point_frameOfCfg (cfg : Cfg) : point (frameOfCfg cfg) = .config cfg := by
  cases cfg <;> simp [frameOfCfg, point, contOf_framesOf]

theorem enc_frameOfCfg (cfg : Cfg) : encFrameState (frameOfCfg cfg) = encCfg cfg := by
  rw [← point_pattern, point_frameOfCfg]
  rfl

/-- This lifts a supplied authored path; every target event comes from
the actual compiler's local firing theorem. -/
theorem lift_authored {first last : Pattern} (path : ExecutionPath machineTheory first last)
    {frame : FrameState} {state : SState Nat} (same : encFrameState frame = first)
    (atFrame : Represents frame state) :
    ∃ run : native.Run state, ∃ final : FrameState,
      Represents final run.last ∧ encFrameState final = last ∧ run.word.length = path.length := by
  obtain ⟨final, framePath, atEnd, length⟩ := Authored.read_path path frame same
  obtain ⟨run, represents, nativeLength⟩ := NativeBudget.lift_path native comparison framePath atFrame
  exact ⟨run, final, represents, atEnd, nativeLength.trans length⟩

theorem reads_cfg_of_encoded {frame : FrameState} {state : SState Nat} (atFrame : Represents frame state)
    {cfg : Cfg} (encoded : encFrameState frame = encCfg cfg) : ReadsBag state {eCfg cfg} := by
  have pointEq : point frame = Point.config cfg :=
    pattern_injective ((point_pattern frame).trans encoded)
  change ReadsBag state {(point frame).row} at atFrame
  simpa only [pointEq, Point.row] using atFrame

/-- Initial eager setup has a positive, code-dependent finite firing
bound, even when the complete program will later diverge. -/
theorem initialization_run (code : Code) (input : List Nat) :
    ∃ run : native.Run (start code input),
      ReadsBag run.last {eCfg (stepNormal code .halt input)} ∧
      0 < run.word.length ∧ run.word.length ≤ MacroCost.setupBound code := by
  obtain ⟨run, final, represents, encoded, length⟩ :=
    lift_authored (normalPath code .halt input) rfl (initial code input)
  refine ⟨run, reads_cfg_of_encoded represents encoded, ?_, ?_⟩
  · rw [length]
    exact (MacroCost.normalPath_cost code .halt input).1
  · rw [length]
    exact (MacroCost.normalPath_cost code .halt input).2

/-- One actual Mathlib step is implemented by a positive actual native
run, with the structural continuation bound and the correct decoded end. -/
theorem mathlib_step_run {before after : Cfg} (stepped : after ∈ step before)
    {state : SState Nat} (reads : ReadsBag state {eCfg before}) :
    ∃ run : native.Run state, ReadsBag run.last {eCfg after} ∧
      0 < run.word.length ∧ run.word.length ≤ MacroCost.stepBound before := by
  have represented : Represents (frameOfCfg before) state := by
    change ReadsBag state {(point (frameOfCfg before)).row}
    simpa only [point_frameOfCfg, Point.row] using reads
  obtain ⟨run, final, represents, encoded, length⟩ :=
    lift_authored (machineStepPath stepped) (enc_frameOfCfg before) represented
  refine ⟨run, reads_cfg_of_encoded represents encoded, ?_, ?_⟩
  · rw [length]
    exact (MacroCost.machineStepPath_cost stepped).1
  · rw [length]
    exact (MacroCost.machineStepPath_cost stepped).2

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.PartialRecursive

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.PartialRecursive.lift_authored
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.PartialRecursive.initialization_run
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.PartialRecursive.mathlib_step_run
