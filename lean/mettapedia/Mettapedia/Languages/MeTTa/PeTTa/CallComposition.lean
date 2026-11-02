import Mettapedia.Languages.MeTTa.PeTTa.Eval

/-!
# Reusing completed original calls after argument evaluation

These laws remove only empty sequencing frames introduced by argument capture.
They retain the original evaluator, resulting state, answer occurrences and I/O.
A completed captured call can therefore be reused at its actual function stage
when an enclosing source operation has computed one of the arguments.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Eval

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open SpaceSemantics (Program)
open _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects (State)

private theorem empty_sequence_frames_path (program : Program) (state : State)
    (answers input output : List Atom) (count : Nat) :
    (theory program).MultiStep
      (withFrames (finished state answers input output) (List.replicate count (.sequence [] [])))
      (finished state answers input output) := by
  induction count with
  | zero => exact .refl _
  | succ count ih =>
      let middle : Configuration :=
        {state := state, control := .sequence [] answers, frames := List.replicate count (.sequence [] []), input := input, output := output}
      have first : step program (withFrames (finished state answers input output)
          (List.replicate (count + 1) (.sequence [] []))) = some middle := by
        simp [withFrames, finished, List.replicate_succ, step, middle]
      have second : step program middle = some (withFrames (finished state answers input output)
          (List.replicate count (.sequence [] []))) := rfl
      exact .step (step_transition first) (.step (step_transition second) ih)

private theorem step_none_terminal (program : Program) (source : Configuration)
    (stopped : step program source = none) :
    (∃ fault, source.control = .fault fault) ∨ (∃ answers, source.control = .returned answers ∧ source.frames = []) := by
  cases source with
  | mk state control frames input output =>
      cases control <;> cases frames
      all_goals simp only [step] at stopped
      all_goals try solve | simp_all
      all_goals repeat' first
        | contradiction
        | split at stopped

/-- Empty sequencing frames only collect the already computed answers. Their
presence cannot create an otherwise absent completed result. -/
theorem completed_empty_sequence_frames_reflect (program : Program) (fuel : Nat)
    (source : Configuration) (count : Nat) (after : State) (answers input output : List Atom)
    (completed : run program fuel (withFrames source (List.replicate count (.sequence [] []))) =
      .complete after answers input output) :
    ∃ fuel, run program fuel source = .complete after answers input output := by
  induction fuel generalizing source with
  | zero =>
      cases source with
      | mk state control frames pending printed =>
          cases control <;> cases frames <;> cases count <;> simp_all [withFrames, run]
          exact ⟨0, rfl⟩
  | succ fuel ih =>
      cases advanced : step program source with
      | some next =>
          have stepped := step_with_caller_frames program source next
            (List.replicate count (.sequence [] [])) advanced
          have later := (run_succ_of_step program fuel _ _ stepped).symm.trans completed
          obtain ⟨enough, computed⟩ := ih next later
          exact ⟨enough + 1, (run_succ_of_step program enough source next advanced).trans computed⟩
      | none =>
          rcases step_none_terminal program source advanced with faulted | returned
          · obtain ⟨fault, shaped⟩ := faulted
            simp [withFrames, shaped, run] at completed
          · obtain ⟨values, shaped, empty⟩ := returned
            have sameSource : source = finished source.state values source.input source.output := by
              cases source
              simp_all [finished]
            rw [sameSource] at completed
            obtain ⟨expectedFuel, expected⟩ := path_has_sufficient_fuel program _
              source.state values source.input source.output (empty_sequence_frames_path program _ _ _ _ count)
            have same := completed_result_unique program expectedFuel (fuel + 1) _
              source.state after values source.input source.output answers input output expected completed
            exact ⟨0, by rw [sameSource]; simpa only [same.1, same.2.1, same.2.2.1, same.2.2.2] using
              run_finished program 0 source.state values source.input source.output⟩

private theorem captured_call_stage_path_of_shape (program : Program) (caller : Subst)
    (state : State) (head : String) (arguments : List Atom) (fuel : Nat)
    (dispatch : (ioHead head || StdLib.known head || program.equations.any (·.head == head)) = true)
    (notControl : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false)
    (admitted : ∀ offset argument, arguments[offset]? = some argument →
      argumentIsRaw program head offset = true ∨ passiveArgument argument = true) :
    run program (fuel + argumentCaptureCost program head 0 arguments.length + 1)
      {state, control := .evaluate caller (.expression (.symbol head :: arguments))} =
    run program fuel
      {state, control := .arguments caller (.function head) [] (arguments.map (applySubst caller)) arguments.length,
        frames := List.replicate arguments.length (.sequence [] [])} := by
  have entered : step program
      {state, control := .evaluate caller (.expression (.symbol head :: arguments))} =
      some {state, control := .arguments caller (.function head) arguments [] 0} :=
    transition_step (.call_enter rfl notControl dispatch)
  rw [run_succ_of_step program _ _ _ entered]
  simpa using captured_arguments_stage program caller state head arguments [] 0 fuel []
    (by simpa using admitted)

/-- The actual completed function stage is independent of the caller's
bindings and physical argument cursor after all values have been obtained. The
application must not be control syntax; `captured_function_arguments_returns`
states this by the head alone. -/
theorem captured_function_arguments_returns_of_shape (program : Program) (first caller : Subst)
    (before after : State) (head : String) (arguments : List Atom) (index : Nat) (answer : Atom)
    (dispatch : (ioHead head || StdLib.known head || program.equations.any (·.head == head)) = true)
    (notControl : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false)
    (admitted : ∀ offset argument, arguments[offset]? = some argument →
      argumentIsRaw program head offset = true ∨ passiveArgument argument = true)
    (returned : PureReturns program first before (.expression (.symbol head :: arguments)) after answer) :
    (theory program).MultiStep
      {state := before, control := .arguments caller (.function head) [] (arguments.map (applySubst first)) index}
      (finished after [answer] [] []) := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program first before after _ _ returned
  have enough := completed_run_more_fuel program fuel
    (argumentCaptureCost program head 0 arguments.length + 1) _ after [answer] [] [] completed
  rw [show fuel + (argumentCaptureCost program head 0 arguments.length + 1) =
      fuel + argumentCaptureCost program head 0 arguments.length + 1 by omega,
    captured_call_stage_path_of_shape program first before head arguments fuel dispatch notControl
      admitted] at enough
  obtain ⟨stageFuel, computed⟩ := completed_empty_sequence_frames_reflect program fuel
    {state := before, control := .arguments first (.function head) [] (arguments.map (applySubst first)) arguments.length}
    arguments.length after [answer] [] [] enough
  have increased := completed_run_more_fuel program stageFuel 1 _ after [answer] [] [] computed
  let initial : Configuration :=
    {state := before, control := .arguments first (.function head) [] (arguments.map (applySubst first)) arguments.length}
  let target : Configuration :=
    {state := before, control := .arguments caller (.function head) [] (arguments.map (applySubst first)) index}
  have sameStep : step program initial = step program target := by rfl
  cases advanced : step program initial with
  | none => simp [initial, run, advanced] at increased
  | some next =>
      have targetStep : step program target = some next := sameStep.symm.trans advanced
      have sameResult := (run_succ_of_step program stageFuel initial next advanced).symm.trans increased
      exact completed_run_has_path program (stageFuel + 1) target after [answer] [] []
        ((run_succ_of_step program stageFuel target next targetStep).trans sameResult)

/-- The completed function stage of an application whose head is no special
form. -/
theorem captured_function_arguments_returns (program : Program) (first caller : Subst)
    (before after : State) (head : String) (arguments : List Atom) (index : Nat) (answer : Atom)
    (dispatch : (ioHead head || StdLib.known head || program.equations.any (·.head == head)) = true)
    (ordinary : head ∉
      ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "match"])
    (admitted : ∀ offset argument, arguments[offset]? = some argument →
      argumentIsRaw program head offset = true ∨ passiveArgument argument = true)
    (returned : PureReturns program first before (.expression (.symbol head :: arguments)) after answer) :
    (theory program).MultiStep
      {state := before, control := .arguments caller (.function head) [] (arguments.map (applySubst first)) index}
      (finished after [answer] [] []) :=
  captured_function_arguments_returns_of_shape program first caller before after head arguments index
    answer dispatch (controlForm_of_ordinary ordinary) admitted returned

end Mettapedia.Languages.MeTTa.PeTTa.Eval
