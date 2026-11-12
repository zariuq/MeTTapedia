import Mettapedia.Languages.MeTTa.PeTTa.UnifyingReturns

/-!
# Actual source calls above retained caller frames

Appending a caller's saved frame suffix lifts each existing source step.
An isolated source execution therefore reaches the same answer packets,
state, effects and freshness counter just above that retained suffix, before
the caller consumes those packets. No invariant of sibling branch bindings
is inferred from the current child's substitution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Unifying

def appendFrames (configuration : Configuration) (suffix : List Frame) : Configuration :=
  { configuration with frames := configuration.frames ++ suffix }

theorem Transition.append_frames {registry : SpaceSemantics.Program} {source target : Configuration}
    (derivation : Transition registry source target) (suffix : List Frame) :
    Transition registry (appendFrames source suffix) (appendFrames target suffix) := by
  apply step_transition
  cases derivation
  all_goals try solve | simp_all [appendFrames, step, sourceControlForm, Eval.ioHead]
  case raw_argument bindings destination first rest values index control raw =>
    cases destination <;> simp_all [appendFrames, step]
  case evaluated_argument bindings destination first rest values index control demanded =>
    cases destination <;> simp_all [appendFrames, step]
  case call_enter bindings head arguments control notControl callable =>
    simp only [appendFrames, step, control]
    split <;> simp_all [sourceControlForm] <;> aesop
  case data_enter bindings head arguments control notControl notCallable =>
    simp only [appendFrames, step, control]
    split <;> simp_all [sourceControlForm]
    all_goals aesop
  case equations bindings head index held selected used control ordinary notRemove notNative chosen =>
    have notMatch : head ≠ "match" := by
      rintro rfl
      cases notNative
    simp [appendFrames, step, control, ordinary, notRemove, notMatch, notNative, chosen]
  case dynamic_native bindings callee supplied head control resolved native =>
    simp [appendFrames, step, control, resolved, partial?, native]
  case dynamic_equations bindings callee supplied head selected used control resolved notNative registered chosen =>
    simp [appendFrames, step, control, resolved, partial?, notNative, registered, chosen,
      invocationFrames_append]
  case dynamic_data bindings callee supplied control notPartial notCallable =>
    cases resolved : resolve bindings callee <;> simp_all [appendFrames, step, runtimeCallable]
  case partial_value bindings head captured control =>
    simp [appendFrames, step, control, Eval.partialValue, Eval.partialTag, partial?]
  case fault_caught reason earned rest control recovered =>
    have extended := recoverDynamic_append source.frames suffix [] earned rest recovered
    simp [appendFrames, step, control, extended]
  case remove_bad bindings index held control invalid =>
    cases held with
    | nil => simp [appendFrames, step, control, Eval.ioHead]
    | cons first rest =>
        cases rest with
        | nil => simp [appendFrames, step, control, Eval.ioHead]
        | cons second rest =>
            cases rest with
            | nil => exact absurd rfl (invalid first second)
            | cons third rest => simp [appendFrames, step, control, Eval.ioHead]

theorem step_append_frames {registry : SpaceSemantics.Program} {source target : Configuration}
    (computed : step registry source = some target) (suffix : List Frame) :
    step registry (appendFrames source suffix) = some (appendFrames target suffix) :=
  transition_step (((step_iff_transition registry source target).mp computed).append_frames suffix)

/-- Along an earned source step, the retained caller permits no different
next step. Crossing the eventual caller boundary is deliberately separate. -/
theorem step_append_frames_exact {registry : SpaceSemantics.Program} {source target : Configuration}
    (computed : step registry source = some target) (suffix : List Frame) (next : Configuration) :
    step registry (appendFrames source suffix) = some next ↔ next = appendFrames target suffix := by
  rw [step_append_frames computed suffix]
  simp only [Option.some.injEq, eq_comm]

theorem steps_append_frames {registry : SpaceSemantics.Program} {source target : Configuration}
    (steps : Relation.ReflTransGen (Transition registry) source target) (suffix : List Frame) :
    Relation.ReflTransGen (Transition registry) (appendFrames source suffix) (appendFrames target suffix) := by
  induction steps with
  | refl => exact .refl
  | tail previous taken ih => exact .tail ih (taken.append_frames suffix)

/-- The caller frames are still present at the reached endpoint; this is
not a claim that running onward through the caller leaves them unchanged. -/
theorem completed_run_above_caller {registry : SpaceSemantics.Program} {source : Configuration}
    {fuel : Nat} {state : Effects.State} {values input output : List Mettapedia.Languages.MeTTa.OSLFCore.Atom}
    (completed : run registry fuel source = .complete state values input output) (suffix : List Frame) :
    ∃ final answers, Relation.ReflTransGen (Transition registry) (appendFrames source suffix) final ∧
      final.control = .returned answers ∧ final.frames = suffix ∧
      final.state = state ∧ final.input = input ∧ final.output = output ∧
      values = answers.map (fun answer => resolve answer.bindings answer.value) := by
  have derived := (completed_run_iff_derivation registry source state values input output).mp ⟨fuel, completed⟩
  obtain ⟨final, answers, steps, returned, frames, finalState, finalInput, finalOutput, valuesEq⟩ :=
    derived.completed_endpoint
  exact ⟨appendFrames final suffix, answers, steps_append_frames steps suffix, returned,
    by simp [appendFrames, frames], finalState, finalInput, finalOutput, valuesEq⟩

namespace RetainedFrameControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi

def num (n : Int) : Atom := .grounded (.int n)
def child : MORK.Subst := [("protected", num 7)]
def caller : MORK.Subst := [("protected", num 1)]
def registry : SpaceSemantics.Program := { equations := [], declarations := [] }
def source : Configuration := { state := Effects.empty, control := .evaluate child (.var "protected") }
def suffix : List Frame := [.bind (.var "ignored") (num 99)]

theorem isolated_child_returns_seven : observed (run registry 30 source) = .answers [num 7] := by decide +kernel

theorem resuming_the_caller_is_a_distinct_phase :
    observed (run registry 30 (appendFrames source suffix)) = .answers [num 99] := by decide +kernel

theorem caller_record_need_not_refine_child : ¬ Refines child caller := by
  intro refined
  have impossible := refined (.var "protected")
  change num 7 = num 1 at impossible
  cases impossible

theorem resetting_global_refinement_to_child_is_wrong :
    ¬ ConfigurationRefines child (appendFrames source [.collect caller]) := by
  intro good
  have saved := good.2 (.collect caller) (by simp [appendFrames, source])
  exact caller_record_need_not_refine_child saved.2

end RetainedFrameControls

end Mettapedia.Languages.MeTTa.PeTTa.Unifying
