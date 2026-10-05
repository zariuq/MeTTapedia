import Mettapedia.Languages.Chaitin.TuringInterpreter.Prefixes
import Mettapedia.Languages.TuringMachine.MathlibBridge

/-!
# Termination and output correspondence for the historical Lisp interpreter

The table and input are quoted data in one fixed recursive interpreter.
Forward simulation follows the source's finite run. Reflection follows a
strictly decreasing successful Lisp execution budget, so divergence cannot
be replaced by a timeout or by a spurious returned value. All outer input
and output observations are retained.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Chaitin.TuringInterpreter

open TuringPrograms PureEvaluation Expressions Mettapedia.Computability.StreamingInput

def callState (machine : TuringMachine.Machine) (configuration : TuringMachine.Configuration)
    (environment : Environment) : State :=
  { initial SExpr.nil with control := (.apply loopFunction
    [encodeTable machine.transitions, encodeConfiguration configuration] environment .unlimited) }

theorem eval_preserved (source : TuringMachine.Machine)
    {configuration final : TuringMachine.Configuration}
    (computed : final ∈ StateTransition.eval source.next? configuration) :
    ∀ (environment : Environment), EnvironmentContract environment → ∀ context : State,
      InternalSteps
        { context with control := (.apply loopFunction
          [encodeTable source.transitions, encodeConfiguration configuration] environment .unlimited) }
        { context with control := .returned (encodeConfiguration final) } := by
  refine StateTransition.evalInduction computed ?_
  intro configuration computed recurse environment contract context
  cases selected : source.entryFor configuration with
  | none =>
      have stopped : source.next? configuration = none := by
        simp only [TuringMachine.Machine.next?, selected, Option.map_none]
      have current : configuration ∈ StateTransition.eval source.next? configuration :=
        StateTransition.mem_eval.mpr ⟨.refl, stopped⟩
      have same := Part.mem_unique computed current
      subst final
      exact (lambda_prefix _ _ _ _ context).trans
        ((body_halted source configuration environment contract selected).steps context)
  | some entry =>
      have next : source.next? configuration = some (configuration.after entry) := by
        simp only [TuringMachine.Machine.next?, selected, Option.map_some]
      exact (lambda_prefix _ _ _ _ context).trans
        ((body_next_prefix source configuration entry environment contract selected context).trans
          (recurse (configuration.after entry) next
            (iterationEnvironment environment source configuration (encodeTransition entry))
            (contract.iterationEnvironment _ _ _) context))

theorem loop_fuel_reflected (source : TuringMachine.Machine) (fuel : Nat) :
    ∀ (configuration : TuringMachine.Configuration) (environment : Environment),
      EnvironmentContract environment → ∀ (input rest : List Bool) (observation : Observation),
      runFuel machine fuel (callState source configuration environment) input = some (observation, rest) →
      ∃ final, final ∈ StateTransition.eval source.next? configuration ∧
        observation = ⟨.success (encodeConfiguration final), [], []⟩ ∧ rest = input := by
  induction fuel using Nat.strong_induction_on with
  | h fuel recurse =>
      intro configuration environment contract input rest observation computed
      cases selected : source.entryFor configuration with
      | none =>
          have stopped : source.next? configuration = none := by
            simp only [TuringMachine.Machine.next?, selected, Option.map_none]
          have steps := (lambda_prefix
            (.list [.symbol "table", .symbol "configuration"]) interpreterBody
            [encodeTable source.transitions, encodeConfiguration configuration]
            environment (initial SExpr.nil)).trans
            ((body_halted source configuration environment contract selected).steps (initial SExpr.nil))
          have returned := (steps.runs_iff input observation rest).mp (runFuel_sound computed)
          have exactResult := (runs_halt_iff (machine := machine) (by rfl)).mp returned
          exact ⟨configuration, StateTransition.mem_eval.mpr ⟨.refl, stopped⟩, exactResult⟩
      | some entry =>
          have iterationPrefix := body_next_prefix source configuration entry environment contract selected
            (initial SExpr.nil)
          obtain ⟨remaining, smaller, later⟩ := internal_prefix_fuel_lt
            (state := callState source configuration environment) (by rfl) iterationPrefix computed
          obtain ⟨final, sourceRun, returned, sameRest⟩ := recurse remaining smaller
            (configuration.after entry)
            (iterationEnvironment environment source configuration (encodeTransition entry))
            (contract.iterationEnvironment _ _ _) input rest observation later
          have next : source.next? configuration = some (configuration.after entry) := by
            simp only [TuringMachine.Machine.next?, selected, Option.map_some]
          have same := StateTransition.reaches_eval (Relation.ReflTransGen.single next)
          exact ⟨final, same ▸ sourceRun, returned, sameRest⟩

/-- The complete closed program has exactly the source machine's terminal
configurations, with no input consumption or output/debug effects. -/
theorem evaluates_iff (source : TuringMachine.Machine)
    (configuration : TuringMachine.Configuration) (input rest : List Bool)
    (observation : Observation) :
    Evaluates (machineProgram source configuration) input observation rest ↔
      ∃ final, final ∈ StateTransition.eval source.next? configuration ∧
        observation = ⟨.success (encodeConfiguration final), [], []⟩ ∧ rest = input := by
  have programPrefix := closed_program_prefix source configuration (initial SExpr.nil)
  constructor
  · intro run
    have later := (programPrefix.runs_iff input observation rest).mp run
    obtain ⟨fuel, computed⟩ := later.fuel
    exact loop_fuel_reflected source fuel configuration baseEnvironment
      baseEnvironment_contract input rest observation computed
  · rintro ⟨final, computed, sameObservation, sameInput⟩
    subst observation rest
    apply (programPrefix.runs_iff input _ input).mpr
    apply ((eval_preserved source computed baseEnvironment baseEnvironment_contract
      (initial SExpr.nil)).runs_iff input _ input).mpr
    exact .halt rfl

/-- Exact result correspondence, not merely preservation of halting. -/
theorem returns_iff (source : TuringMachine.Machine)
    (configuration final : TuringMachine.Configuration) (input : List Bool) :
    Evaluates (machineProgram source configuration) input
      ⟨.success (encodeConfiguration final), [], []⟩ input ↔
      final ∈ StateTransition.eval source.next? configuration := by
  rw [evaluates_iff]
  constructor
  · rintro ⟨other, computed, same, -⟩
    have encoded := Result.success.inj (congrArg Observation.result same)
    have sameFinal := encodeConfiguration_injective encoded
    exact sameFinal ▸ computed
  · exact fun computed => ⟨final, computed, rfl, rfl⟩

theorem execute_iff (source : TuringMachine.Machine)
    (configuration final : TuringMachine.Configuration) (input : List Bool) :
    (∃ fuel, execute fuel (machineProgram source configuration) input =
      some (⟨.success (encodeConfiguration final), [], []⟩, input)) ↔
      final ∈ StateTransition.eval source.next? configuration :=
  Chaitin.evaluates_iff_execute.symm.trans (returns_iff source configuration final input)

end Mettapedia.Languages.Chaitin.TuringInterpreter
