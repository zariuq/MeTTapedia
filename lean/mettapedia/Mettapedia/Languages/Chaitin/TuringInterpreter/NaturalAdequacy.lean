import Mettapedia.Languages.Chaitin.TuringInterpreter.Adequacy
import Mettapedia.Languages.TuringMachine.UniversalTable

/-!
# Finite natural derivations and universality of the ordinary Lisp program

The successful recursive derivation is constructed from the source run,
rather than assumed. First-match execution agrees with the authored Turing
language under its deterministic-table hypothesis. The universal table is
reused unchanged; its program and prepared input determine the Lisp source
before any computation takes place.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Chaitin.TuringInterpreter

open TuringPrograms PureEvaluation Expressions
open Mettapedia.Computability.StreamingInput

theorem body_recursive (source : TuringMachine.Machine)
    (configuration : TuringMachine.Configuration) (entry : TuringMachine.Transition)
    (environment : Environment) (contract : EnvironmentContract environment)
    (found : source.entryFor configuration = some entry) (value : SExpr)
    (recurse : PureApply
      (iterationEnvironment environment source configuration (encodeTransition entry))
      loopFunction [encodeTable source.transitions, encodeConfiguration (configuration.after entry)] value) :
    PureEval (loopScope environment (encodeTable source.transitions) (encodeConfiguration configuration))
      interpreterBody value := by
  let scope := loopScope environment (encodeTable source.transitions) (encodeConfiguration configuration)
  let nextScope := iterationEnvironment environment source configuration (encodeTransition entry)
  have localContract := contract.loopScope (encodeTable source.transitions) (encodeConfiguration configuration)
  have nextContract := contract.iterationEnvironment source configuration (encodeTransition entry)
  have selectedRun : PureEval scope selectionExpression (encodeTransition entry) := by
    simpa only [found, Option.map_some, Option.getD_some] using
      selection_eval source configuration environment contract
  have selectedValue := eval_word (selectedScope_selected
    (loopScope environment (encodeTable source.transitions) (encodeConfiguration configuration))
    (encodeTransition entry))
  have configurationRun := eval_word (iteration_configuration environment source configuration
    (encodeTransition entry))
  have moveRun : PureEval nextScope
      (call "move-row" [.symbol "selected", .symbol "configuration"])
      (encodeConfiguration (configuration.after entry)) :=
    .application (eval_word nextContract.moveRow)
      (by intro same; cases same) (by intro same; cases same)
      (.cons selectedValue (.cons configurationRun (.nil nextScope)))
      (transition_encoded_apply entry configuration nextScope nextContract.toMoveEnvironment)
  have recursiveRun : PureEval nextScope
      (call "run-table" [.symbol "table",
        call "move-row" [.symbol "selected", .symbol "configuration"]]) value :=
    .application (eval_word nextContract.runTable)
      (by intro same; cases same) (by intro same; cases same)
      (.cons (eval_word (iteration_table environment source configuration (encodeTransition entry)))
        (.cons moveRun (.nil nextScope))) recurse
  have notNil : encodeTransition entry ≠ SExpr.nil := by simp [encodeTransition, SExpr.nil]
  apply eval_letValue localContract.quote selectedRun
  change PureEval nextScope continuationExpression value
  apply eval_if nextContract.conditional
    (eval_equal nextContract.equal selectedValue (eval_word nextContract.nil))
  simpa only [SExpr.truth_boolean, notNil, decide_false, Bool.false_eq_true, ↓reduceIte]
    using recursiveRun

theorem eval_pureApply (source : TuringMachine.Machine)
    {configuration final : TuringMachine.Configuration}
    (computed : final ∈ StateTransition.eval source.next? configuration) :
    ∀ environment : Environment, EnvironmentContract environment →
      PureApply environment loopFunction
        [encodeTable source.transitions, encodeConfiguration configuration] (encodeConfiguration final) := by
  refine StateTransition.evalInduction computed ?_
  intro configuration computed recurse environment contract
  apply apply_lambda
  cases selected : source.entryFor configuration with
  | none =>
      have stopped : source.next? configuration = none := by
        simp only [TuringMachine.Machine.next?, selected, Option.map_none]
      have current : configuration ∈ StateTransition.eval source.next? configuration :=
        StateTransition.mem_eval.mpr ⟨.refl, stopped⟩
      have same := Part.mem_unique computed current
      subst final
      exact body_halted source configuration environment contract selected
  | some entry =>
      have next : source.next? configuration = some (configuration.after entry) := by
        simp only [TuringMachine.Machine.next?, selected, Option.map_some]
      exact body_recursive source configuration entry environment contract selected _
        (recurse _ next _ (contract.iterationEnvironment _ _ _))

theorem eval_pure (source : TuringMachine.Machine)
    {configuration final : TuringMachine.Configuration}
    (computed : final ∈ StateTransition.eval source.next? configuration) :
    PureEval cleanEnvironment (machineProgram source configuration) (encodeConfiguration final) := by
  apply eval_letValue (by rfl) (eval_quote (by rfl) lookupFunction)
  apply eval_letValue rowBase_quote (eval_quote rowBase_quote transitionFunction)
  apply eval_letValue moveBase_quote (eval_quote moveBase_quote loopFunction)
  exact .application (eval_word baseEnvironment_contract.runTable)
    (by intro same; cases same) (by intro same; cases same)
    (.cons (eval_quote baseEnvironment_contract.quote (encodeTable source.transitions))
      (.cons (eval_quote baseEnvironment_contract.quote (encodeConfiguration configuration))
        (.nil baseEnvironment)))
    (eval_pureApply source computed baseEnvironment baseEnvironment_contract)

/-- Halting in the actual authored Turing language is equivalent to a
successful execution of the historical Lisp source. -/
theorem halts_iff (source : TuringMachine.Machine) (deterministic : source.Deterministic)
    (configuration : TuringMachine.Configuration) (input : List Bool) :
    TuringMachine.HaltsFrom source configuration.term ↔
      ∃ value, Evaluates (machineProgram source configuration) input ⟨.success value, [], []⟩ input := by
  rw [← TuringMachine.MathlibBridge.next_eval_dom_iff_halts source deterministic configuration,
    Part.dom_iff_mem]
  constructor
  · rintro ⟨final, computed⟩
    exact ⟨encodeConfiguration final, (returns_iff source configuration final input).mpr computed⟩
  · rintro ⟨value, run⟩
    obtain ⟨final, computed, _, _⟩ := (evaluates_iff source configuration input input _).mp run
    exact ⟨final, computed⟩

noncomputable def universalProgram (index argument : Nat) : SExpr :=
  machineProgram TuringMachine.UniversalTable.machine
    (TuringMachine.UniversalTable.inputConfiguration index argument)

theorem universal_halts_iff (index argument : Nat) (input : List Bool) :
    (∃ value, Evaluates (universalProgram index argument) input ⟨.success value, [], []⟩ input) ↔
      ((Denumerable.ofNat Nat.Partrec.Code index).eval argument).Dom :=
  (halts_iff _ TuringMachine.UniversalTable.deterministic _ input).symm.trans
    (TuringMachine.UniversalTable.halts_iff index argument)

theorem universal_output_preserved (index argument output : Nat) (input : List Bool)
    (computed : output ∈ (Denumerable.ofNat Nat.Partrec.Code index).eval argument) :
    ∃ final, Evaluates (universalProgram index argument) input
      ⟨.success (encodeConfiguration final), [], []⟩ input ∧
      TuringMachine.PartrecBridge.Represents Mettapedia.Languages.PartrecMachine.universal
        (Turing.PartrecToTM2.halt [output]) final := by
  obtain ⟨final, run, represented⟩ := TuringMachine.UniversalTable.output_preserved
    index argument output computed
  exact ⟨final, (returns_iff _ _ _ input).mpr run, represented⟩

theorem universal_output_reflected (index argument : Nat) (final : TuringMachine.Configuration)
    (input : List Bool)
    (returned : Evaluates (universalProgram index argument) input
      ⟨.success (encodeConfiguration final), [], []⟩ input) :
    ∃ output, output ∈ (Denumerable.ofNat Nat.Partrec.Code index).eval argument ∧
      TuringMachine.PartrecBridge.Represents Mettapedia.Languages.PartrecMachine.universal
        (Turing.PartrecToTM2.halt [output]) final :=
  TuringMachine.UniversalTable.output_reflected index argument ((returns_iff _ _ _ input).mp returned)

theorem universal_halting_not_computable :
    ¬ ComputablePred fun index : Nat =>
      ∃ value, Evaluates (universalProgram index 0) [] ⟨.success value, [], []⟩ [] :=
  fun decided => Mettapedia.Languages.PartrecMachine.halting_family_not_computable
    (decided.of_eq (universal_halts_iff · 0 []))

end Mettapedia.Languages.Chaitin.TuringInterpreter
