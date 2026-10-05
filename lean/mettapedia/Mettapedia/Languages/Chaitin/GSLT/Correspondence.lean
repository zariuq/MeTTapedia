import Mettapedia.Languages.Chaitin.GSLT.CompiledSteps
import Mettapedia.Languages.Chaitin.GSLT.PurePaths

/-!
# Preservation and reflection of the authored evaluator's execution

The grammar's generated steps stay in the image of well-formed pure
configurations. Both single steps and complete paths correspond to the
explicit continuation rules. Every such step is an action of the historical
evaluator, preserving input and output observations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Chaitin.GSLT

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Computability.StreamingInput

theorem CoreStep.compiled {configuration next : Configuration} (step : CoreStep configuration next) :
    theory.Step (encodeConfiguration configuration) (encodeConfiguration next) := by
  rw [theory_step_iff, step_iff_reduct]
  change encodeConfiguration next ∈ reducts configuration
  cases step with
  | atom atomic => simp only [reducts_atom _ _ _ atomic, List.mem_singleton]
  | call => simp only [reducts_call, List.mem_singleton]
  | quote => simp [reducts_function]
  | conditional => simp [reducts_function]
  | function notQuote notIf => simp [reducts_function, notQuote, notIf]
  | branch => simp only [reducts_branch, List.mem_singleton]
  | argument => simp only [reducts_argument, List.mem_singleton]
  | primitive computed =>
      rw [reducts_apply]
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_map.mpr
      exact ⟨_, by simp [computed], rfl⟩
  | eval =>
      rw [reducts_apply]
      apply List.mem_append_left
      apply List.mem_append_right
      simp
  | lambda dispatch =>
      rw [reducts_apply]
      apply List.mem_append_right
      simp only [if_pos ((lambdaCondition_iff _ _).mpr dispatch), List.mem_singleton]

theorem step_reflected (configuration : Configuration) (target : Pattern)
    (step : theory.Step (encodeConfiguration configuration) target) :
    ∃ next : Configuration, CoreStep configuration next ∧ encodeConfiguration next = target := by
  rw [theory_step_iff, step_iff_reduct] at step
  change target ∈ reducts configuration at step
  cases configuration with
  | eval expression environment continuation =>
      cases expression with
      | symbol word =>
          rw [reducts_atom _ _ _ rfl] at step
          cases List.mem_singleton.mp step
          exact ⟨_, .atom rfl, rfl⟩
      | number number =>
          rw [reducts_atom _ _ _ rfl] at step
          cases List.mem_singleton.mp step
          exact ⟨_, .atom rfl, rfl⟩
      | list values =>
          cases values with
          | nil =>
              rw [reducts_atom _ _ _ rfl] at step
              cases List.mem_singleton.mp step
              exact ⟨_, .atom rfl, rfl⟩
          | cons first rest =>
              rw [reducts_call] at step
              cases List.mem_singleton.mp step
              exact ⟨_, .call, rfl⟩
  | returned value continuation =>
      cases continuation with
      | done => simp only [reducts_returned, List.not_mem_nil] at step
      | function operands environment rest =>
          rw [reducts_function] at step
          by_cases quotation : value = .symbol "'"
          · subst value
            simp only [↓reduceIte] at step
            cases List.mem_singleton.mp step
            exact ⟨_, .quote, rfl⟩
          · simp only [if_neg quotation] at step
            by_cases conditional : value = .symbol "if"
            · subst value
              simp only [↓reduceIte] at step
              cases List.mem_singleton.mp step
              exact ⟨_, .conditional, rfl⟩
            · simp only [if_neg conditional] at step
              cases List.mem_singleton.mp step
              exact ⟨_, .function quotation conditional, rfl⟩
      | conditional positive negative environment rest =>
          rw [reducts_branch] at step
          cases List.mem_singleton.mp step
          exact ⟨_, .branch, rfl⟩
      | argument function reversed remaining environment rest =>
          rw [reducts_argument] at step
          cases List.mem_singleton.mp step
          exact ⟨_, .argument, rfl⟩
  | apply function arguments environment continuation =>
      rw [reducts_apply] at step
      rcases List.mem_append.mp step with primitiveOrEval | lambda
      · rcases List.mem_append.mp primitiveOrEval with primitive | eval
        · obtain ⟨value, computed, same⟩ := List.mem_map.mp primitive
          have computation : purePrimitive function arguments = some value := by
            simpa only [Option.mem_toList, Option.mem_def] using computed
          exact ⟨_, .primitive computation, same⟩
        · by_cases evalFunction : function = .symbol "eval"
          · subst function
            simp only [↓reduceIte] at eval
            cases List.mem_singleton.mp eval
            exact ⟨_, .eval, rfl⟩
          · simp only [if_neg evalFunction, List.not_mem_nil] at eval
      · by_cases enabled : LambdaCondition function arguments
        · simp only [if_pos enabled] at lambda
          cases List.mem_singleton.mp lambda
          exact ⟨_, .lambda ((lambdaCondition_iff _ _).mp enabled), rfl⟩
        · simp only [if_neg enabled, List.not_mem_nil] at lambda

theorem step_iff (configuration next : Configuration) :
    theory.Step (encodeConfiguration configuration) (encodeConfiguration next) ↔ CoreStep configuration next := by
  constructor
  · intro step
    obtain ⟨other, core, same⟩ := step_reflected configuration _ step
    cases encodeConfiguration_injective same
    exact core
  · exact CoreStep.compiled

theorem CorePath.compiled {configuration next : Configuration} (path : CorePath configuration next) :
    theory.MultiStep (encodeConfiguration configuration) (encodeConfiguration next) := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl _
  | head first rest ih => exact .step first.compiled ih

private theorem multiStep_relation {system : Mettapedia.GSLT.GSLT}
    {source target : system.Term} (path : system.MultiStep source target) :
    Relation.ReflTransGen system.Step source target := by
  induction path with
  | refl _ => exact .refl
  | step first rest ih => exact (Relation.ReflTransGen.single first).trans ih

theorem path_reflected (configuration : Configuration) (target : Pattern)
    (path : theory.MultiStep (encodeConfiguration configuration) target) :
    ∃ final : Configuration, CorePath configuration final ∧ target = encodeConfiguration final := by
  have related : Relation.ReflTransGen (fun source target : Pattern => theory.Step source target)
      (encodeConfiguration configuration) target := multiStep_relation path
  clear path
  induction related with
  | refl => exact ⟨configuration, .refl, rfl⟩
  | tail previous last ih =>
      obtain ⟨current, earlier, same⟩ := ih
      have actual := last
      rw [same] at actual
      obtain ⟨next, core, encoded⟩ := step_reflected current _ actual
      exact ⟨next, earlier.tail core, encoded.symm⟩

theorem path_iff (configuration final : Configuration) :
    theory.MultiStep (encodeConfiguration configuration) (encodeConfiguration final) ↔
      CorePath configuration final := by
  constructor
  · intro path
    obtain ⟨other, core, same⟩ := path_reflected configuration _ path
    cases encodeConfiguration_injective same
    exact core
  · exact CorePath.compiled

def start (expression : SExpr) (environment : Environment := cleanEnvironment) : Pattern :=
  encodeConfiguration (.eval expression environment .done)

def result (value : SExpr) : Pattern := encodeConfiguration (.returned value .done)

theorem pureEval_generated {environment expression value}
    (derivation : PureEvaluation.PureEval environment expression value) :
    theory.MultiStep (start expression environment) (result value) :=
  (pureEval_corePath derivation .done).compiled

theorem generated_observed {expression value : SExpr} {environment : Environment}
    (path : theory.MultiStep (start expression environment) (result value)) (input : List Bool) :
    Evaluates expression input ⟨.success value, [], []⟩ input .unlimited environment := by
  have core := (path_iff (.eval expression environment .done) (.returned value .done)).mp path
  apply (core.observed.runs_iff input _ input).mpr
  exact .halt (returned_observe value)

theorem result_normal (value : SExpr) : theory.IsNormalForm (result value) := by
  rintro ⟨target, step⟩
  have raw := (theory_step_iff (result value) target).mp step
  have compiled := (step_iff_reduct (result value) target).mp raw
  change target ∈ reducts (.returned value .done) at compiled
  simp only [reducts_returned] at compiled
  cases compiled

def decodeFrames : List Frame → Option Continuation
  | [] => some .done
  | .function operands environment .unlimited :: rest =>
      (.function operands environment) <$> decodeFrames rest
  | .conditional positive negative environment .unlimited :: rest =>
      (.conditional positive negative environment) <$> decodeFrames rest
  | .argument function reversed remaining environment .unlimited :: rest =>
      (.argument function reversed remaining environment) <$> decodeFrames rest
  | _ => none

@[simp] theorem decodeFrames_frames (continuation : Continuation) :
    decodeFrames continuation.frames = some continuation := by
  induction continuation <;> simp [Continuation.frames, decodeFrames, *]

def decodeState (state : State) : Option Configuration := do
  let continuation ← decodeFrames state.frames
  match state.control with
  | .eval expression environment .unlimited => pure (.eval expression environment continuation)
  | .apply function arguments environment .unlimited => pure (.apply function arguments environment continuation)
  | .returned value => pure (.returned value continuation)
  | _ => none

@[simp] theorem decodeState_state (configuration : Configuration) :
    decodeState configuration.state = some configuration := by
  cases configuration <;> simp [decodeState, Configuration.state]

theorem state_injective : Function.Injective Configuration.state := by
  intro first second same
  simpa only [decodeState_state, Option.some.injEq] using congrArg decodeState same

theorem core_deterministic {configuration first second : Configuration}
    (left : CoreStep configuration first) (right : CoreStep configuration second) : first = second := by
  exact state_injective (Action.step.inj (left.observed.symm.trans right.observed))

end Mettapedia.Languages.Chaitin.GSLT
