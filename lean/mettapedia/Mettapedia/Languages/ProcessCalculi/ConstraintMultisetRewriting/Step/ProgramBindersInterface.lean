import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventCategory

/-!
# Contextual equation execution through the shared event interface

The existing contextual program supplies the actual frame extension, equation
store, selected occurrences and target inventory. Candidates remain equation
indices; admission is the existing contextual validity judgment. This profile
has no source guards, so preparation suffices for its admission. No source
rewrite is used to define the effect or its permission.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Interface
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

variable {S : Signature} {Γ : Ctx S} {sort : S.Srt} {ι : Type} [DecidableEq ι]
  (program : ι → Equation S Γ sort)

namespace InterfaceProfile

def frame (state : State program) : Frames.Frame S := ⟨state.1.Names, state.1.declarations⟩

def infoFrame (state : State program) : Frames.Frame S :=
  ⟨_, active program state.1.declarations⟩

def information (state : State program) (index : ι) :=
  ContextualResidual.observeProblem
    (ContextualActivatedStep.problem (locals program) state.1.declarations state.1.occupied
      (selection state.2) (rule program state.1.declarations index)
      state.1.inventory.rows state.1.inventory.configuration)

def Shapes (state : State program) (index : ι) : Prop :=
  (selection state.2).taken.Nodup ∧ (selection state.2).made.Nodup ∧
  (rule program state.1.declarations index).take.length = (selection state.2).taken.length ∧
  (rule program state.1.declarations index).read.length = (selection state.2).read.length ∧
  (selection state.2).made.map (fun _ => output program state.1.declarations index state.1.occupied state.2) =
    (ContextualActivatedStep.prepared (locals program) state.1.declarations state.1.occupied
      (selection state.2) (rule program state.1.declarations index) state.1.inventory.rows).rule.produce

def Prepared (state : State program) (index : ι) : Prop :=
  Shapes program state index ∧
    Enabled (fun _ : Nat => ()) state.1.inventory.configuration.present
      ((selection state.2).commit (T := Unit)) ∧
    (Frames.contextual S).Solvable (a := infoFrame program state) (information program state index)

omit [DecidableEq ι] in
theorem prepared_iff (state : State program) (index : ι) :
    Prepared program state index ↔ Admitted program state index := by
  constructor
  · rintro ⟨⟨taken, made, takeLength, readLength, outputs⟩, enabled, ⟨future, solution, solved⟩⟩
    refine ⟨⟨taken, made, takeLength, readLength, outputs, ?_, ?_⟩, ?_⟩
    · exact ⟨enabled.taken_subset, enabled.kept_subset, enabled.apart, enabled.fresh,
        fun check member => by simp [Selection.commit] at member⟩
    · intro check member
      simp [ContextualActivatedStep.prepared, ContextualSelectionViews.prepare,
        ContextualFreshening.ruleAt, rule, baseRule, RuleInstance.map] at member
    · exact ⟨future.Names, future.arity, solution,
        (ContextualResidual.models_observeProblem solution _).mp solved⟩
  · intro admitted
    refine ⟨⟨admitted.take_distinct, admitted.output_distinct, admitted.take_length,
      admitted.read_length, admitted.outputs⟩, ?_, ?_⟩
    · exact ⟨admitted.occurrences.taken_subset, admitted.occurrences.kept_subset,
        admitted.occurrences.apart, admitted.occurrences.fresh,
        fun check member => by simp [Selection.commit] at member⟩
    · obtain ⟨Future, future, solution, solved⟩ := admitted.solvable
      exact ⟨⟨Future, future⟩, solution,
        (ContextualResidual.models_observeProblem solution _).mpr solved⟩

def step : Interface.Step (Frames.contextual S) Nat (State program) (fun _ => ι) where
  frame := frame program
  knowledge state := ContextualResidual.observeProblem state.1.inventory.configuration.equations
  present state := state.1.inventory.configuration.present
  selection {state} _ := selection state.2
  target {state} _ := infoFrame program state
  extension {state} _ := ContextualSelectionViews.capturedTarget (locals program) state.1.declarations
  information {state} index := information program state index
  information_refines := by
    intro state index future solution solved
    exact (ContextualResidual.models_observeProblem _ _).mpr
      (ContextualActivatedStep.models_refine_old_frame (locals program) state.1.declarations
        future.arity state.1.occupied (selection state.2) (rule program state.1.declarations index)
        state.1.inventory.rows state.1.inventory.configuration solution
        ((ContextualResidual.models_observeProblem solution _).mp solved))
  Shapes {state} index := Shapes program state index
  preparedResult {state} index prepared :=
    destination program state index ((prepared_iff program state index).mp prepared)
  present_preparedResult _ _ := rfl
  preparedSettle {state} _ _ := generator (active program state.1.declarations)
  result_refines := by
    intro state index prepared future solution solved
    change ContextualResidual.Models solution (information program state index) at solved
    change ContextualResidual.Models (Assignment.compose solution (generator _))
      (information program state index)
    simpa only [Assignment.compose_identity_right] using solved
  Admits {state} index := Admitted program state index
  admitted_prepares index admitted := (prepared_iff program _ index).mpr admitted

instance step_literalKnowledge : (step program).LiteralKnowledge where
  knowledge {state} index prepared := by
    change information program state index =
      (Frames.contextual S).applyStore ((Frames.contextual S).id (infoFrame program state))
        (information program state index)
    exact (Frames.applyStore_id (X := Frames.contextual S)
      (a := infoFrame program state) (information program state index)).symm

theorem admission_iff (state : State program) (index : ι) :
    (step program).Admits (s := state) index ↔ Admitted program state index := Iff.rfl

theorem result_eq (state : State program) (index : ι) (admitted : Admitted program state index) :
    (step program).result index admitted = destination program state index admitted := rfl

theorem event_iff (before after : State program) :
    Nonempty ((step program).effectCore.Event (step program).eventAdmission before after) ↔
      Transition program before after := by
  constructor
  · rintro ⟨event⟩
    exact ⟨event.firing, event.permitted, event.target_eq.symm⟩
  · rintro ⟨index, admitted, rfl⟩
    exact ⟨(step program).event index admitted⟩

theorem run_transition {before : State program} (run : (step program).Run before) :
    Relation.ReflTransGen (Transition program) before run.last := by
  induction run with
  | nil => exact .refl
  | cons index admitted rest ih => exact ih.head ⟨index, admitted, rfl⟩

theorem run_cursor {before : State program} (run : (step program).Run before) :
    run.last.2 = before.2 + run.word.length := by
  induction run with
  | nil => simp [Interface.Step.Run.last, Interface.Step.Run.word]
  | @cons state index admitted rest ih =>
      change rest.last.2 = _
      rw [ih]
      change state.2 + 1 + rest.word.length = state.2 + (rest.word.length + 1)
      omega

theorem transition_run {before after : State program}
    (execution : Relation.ReflTransGen (Transition program) before after) :
    ∃ run : (step program).Run before, run.last = after := by
  induction execution with
  | refl => exact ⟨.nil _, rfl⟩
  | tail earlier last ih =>
      obtain ⟨run, rfl⟩ := ih
      obtain ⟨index, admitted, rfl⟩ := last
      refine ⟨run.append (.cons index admitted (.nil _)), ?_⟩
      rw [Interface.Step.Run.last_append]
      rfl

theorem run_iff (before after : State program) :
    (∃ run : (step program).Run before, run.last = after) ↔
      Relation.ReflTransGen (Transition program) before after := by
  constructor
  · rintro ⟨run, rfl⟩
    exact run_transition program run
  · exact transition_run program

variable [ClosedTerms S]

theorem admitted_has_answer (call : Term S Γ sort) (index : ι)
    (admitted : (step program).Admits (s := initial call) index) :
    ∃ answer, Rewrites program call answer := by
  obtain ⟨solution, matched⟩ := (valid_iff (initial call) call (initial_determines call) index).mp admitted
  obtain ⟨answer, read⟩ := holeFree (instantiate ((program index).assign solution (ground S)) (program index).rhs)
  exact ⟨answer, index, solution, matched, read⟩

theorem rewrite_has_event {call answer : Term S Γ sort} (rewritten : Rewrites program call answer) :
    ∃ after, Nonempty ((step program).effectCore.Event (step program).eventAdmission (initial call) after) ∧
      Reads program after answer := by
  obtain ⟨index, solution, matched, read⟩ := rewritten
  have admitted := (valid_iff (initial call) call (initial_determines call) index).mpr ⟨solution, matched⟩
  exact ⟨_, ⟨(step program).event index admitted⟩,
    (reads_iff (initial call) call (initial_determines call) index admitted answer).mpr
      ⟨solution, matched, read⟩⟩

/-- The existing source-adequacy theorem now targets admitted event runs of
the common interface. It retains all program equations and their scopes. -/
theorem source_execution_iff (call answer : Term S Γ sort) :
    Relation.ReflTransGen (Rewrites program) call answer ↔
      ∃ run : (step program).Run (initial call), Reads program run.last answer := by
  rw [execution_iff]
  constructor
  · rintro ⟨after, execution, reads⟩
    obtain ⟨run, rfl⟩ := transition_run program execution
    exact ⟨run, reads⟩
  · rintro ⟨run, reads⟩
    exact ⟨run.last, run_transition program run, reads⟩

end InterfaceProfile

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders
