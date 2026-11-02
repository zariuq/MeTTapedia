import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlContinuationCoverage
import Mettapedia.Languages.OCaml.MachineCompleteness

/-! Program-declared patterns remain available throughout source machine
execution. The invariant records only continuation references and is
preserved by the actual machine operations.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages

theorem continuation_covered_cons (pool : List OCaml.MatchPattern) (frame : OCaml.Frame) (rest : OCaml.Continuation)
    (headCovered : FrameCovered pool frame) (tailCovered : ContinuationCovered pool rest) :
    ContinuationCovered pool (frame :: rest) := by
  intro actual member
  rcases List.mem_cons.mp member with rfl | member
  · exact headCovered
  · exact tailCovered actual member

theorem continuation_covered_tail (pool : List OCaml.MatchPattern) (frame : OCaml.Frame) (rest : OCaml.Continuation)
    (covered : ContinuationCovered pool (frame :: rest)) : ContinuationCovered pool rest :=
  fun actual member => covered actual (List.mem_cons_of_mem frame member)

theorem enter_body_covered (pool : List OCaml.MatchPattern) (parameter : OCaml.MatchPattern) (argument : OCaml.Value)
    (body : OCaml.Code) (captured : OCaml.Environment) (rest : OCaml.Continuation)
    (covered : ContinuationCovered pool rest) : StateCovered pool (OCaml.enterBody parameter argument body captured rest) := by
  unfold OCaml.enterBody
  cases OCaml.matchPattern parameter argument <;> first | exact True.intro | exact covered

theorem apply_closure_covered (program : OCaml.Program) (pool : List OCaml.MatchPattern) (function argument : OCaml.Value)
    (rest : OCaml.Continuation) (next : OCaml.MachineState) (covered : ContinuationCovered pool rest)
    (step : OCaml.applyClosure program function argument rest = .ok next) : StateCovered pool next := by
  cases function with
  | closure function captured =>
      cases function with
      | lambda reference =>
          cases declared : program.instruction? reference with
          | none => simp [OCaml.applyClosure, declared] at step
          | some instruction =>
              cases instruction with
              | lambda parameter body =>
                  have same : OCaml.enterBody parameter argument body captured rest = next := by
                    simpa only [OCaml.applyClosure, declared, Except.ok.injEq] using step
                  rw [← same]
                  exact enter_body_covered pool parameter argument body captured rest covered
              | _ => simp [OCaml.applyClosure, declared] at step
      | recursive group slot =>
          cases declared : program.instruction? group with
          | none => simp [OCaml.applyClosure, declared] at step
          | some instruction =>
              cases instruction with
              | letRecursive definitions groupBody =>
                  cases indexed : definitions[slot]? with
                  | none => simp [OCaml.applyClosure, declared, indexed] at step
                  | some reference =>
                      cases callable : program.instruction? reference with
                      | none => simp [OCaml.applyClosure, declared, indexed, callable] at step
                      | some instruction =>
                          cases instruction with
                          | lambda parameter body =>
                              have same : OCaml.enterBody parameter argument body
                                  (OCaml.recursiveEnvironment group definitions captured) rest = next := by
                                simpa only [OCaml.applyClosure, declared, indexed, callable, pure, Except.pure, Except.ok.injEq] using step
                              rw [← same]
                              exact enter_body_covered pool parameter argument body _ rest covered
                          | _ => simp [OCaml.applyClosure, declared, indexed, callable] at step
              | _ => simp [OCaml.applyClosure, declared] at step
  | _ => simp [OCaml.applyClosure] at step

theorem finish_build_covered (program : OCaml.Program) (pool : List OCaml.MatchPattern) (kind : OCaml.Build)
    (items : List OCaml.Value) (rest : OCaml.Continuation) (next : OCaml.MachineState)
    (covered : ContinuationCovered pool rest) (step : OCaml.finishBuild program kind items rest = .ok next) :
    StateCovered pool next := by
  cases kind with
  | tuple =>
      simp only [OCaml.finishBuild] at step
      split at step
      · change Except.error _ = Except.ok next at step
        cases step
      · change Except.ok _ = Except.ok next at step
        cases Except.ok.inj step
        exact covered
  | variant typeId constructor =>
      simp only [OCaml.finishBuild] at step
      split at step
      · change Except.ok _ = Except.ok next at step
        cases Except.ok.inj step
        exact covered
      · cases step
  | primitive operator =>
      simp only [OCaml.finishBuild] at step
      cases evaluated : operator.eval items with
      | error error =>
          simp only [evaluated, bind, Except.bind] at step
          cases step
      | ok result =>
          cases result with
          | ok actual =>
              have same : OCaml.MachineState.returned actual rest = next := by simpa only [evaluated, bind, Except.bind, pure, Except.pure, Except.ok.injEq] using step
              rw [← same]
              exact covered
          | error error =>
              have same : OCaml.MachineState.halted (.error error) = next := by simpa only [evaluated, bind, Except.bind, pure, Except.pure, Except.ok.injEq] using step
              rw [← same]
              trivial

theorem start_arguments_covered (program : OCaml.Program) (pool : List OCaml.MatchPattern) (kind : OCaml.Build)
    (references : List OCaml.Code) (captured : OCaml.Environment) (rest : OCaml.Continuation) (next : OCaml.MachineState)
    (covered : ContinuationCovered pool rest) (step : OCaml.startArguments program kind references captured rest = .ok next) :
    StateCovered pool next := by
  unfold OCaml.startArguments at step
  cases reversed : references.reverse with
  | nil =>
      rw [reversed] at step
      exact finish_build_covered program pool kind [] rest next covered step
  | cons last remaining =>
      rw [reversed] at step
      cases Except.ok.inj step
      exact continuation_covered_cons pool (.gather kind remaining captured []) rest trivial covered

theorem evaluate_instruction_covered (program : OCaml.Program) (reference : OCaml.Code) (captured : OCaml.Environment)
    (rest : OCaml.Continuation) (next : OCaml.MachineState) (covered : ContinuationCovered (patterns program) rest)
    (step : OCaml.evaluateInstruction program reference captured rest = .ok next) : StateCovered (patterns program) next := by
  cases declared : program.instruction? reference with
  | none => simp [OCaml.evaluateInstruction, declared] at step
  | some instruction =>
      cases instruction with
      | literal datum =>
          have same : OCaml.MachineState.returned (.literal datum) rest = next := by
            simpa only [OCaml.evaluateInstruction, declared, pure, Except.pure, Except.ok.injEq] using step
          rw [← same]
          exact covered
      | «variable» index =>
          cases found : captured[index]? with
          | none => simp [OCaml.evaluateInstruction, declared, found] at step
          | some actual =>
              have same : OCaml.MachineState.returned actual rest = next := by
                simpa only [OCaml.evaluateInstruction, declared, found, pure, Except.pure, Except.ok.injEq] using step
              rw [← same]
              exact covered
      | lambda parameter body =>
          have same : OCaml.MachineState.returned (.closure (.lambda reference) captured) rest = next := by
            simpa only [OCaml.evaluateInstruction, declared, pure, Except.pure, Except.ok.injEq] using step
          rw [← same]
          exact covered
      | apply function argument =>
          have same : OCaml.MachineState.evaluate argument captured (.argument function captured :: rest) = next := by
            simpa only [OCaml.evaluateInstruction, declared, pure, Except.pure, Except.ok.injEq] using step
          rw [← same]
          exact continuation_covered_cons _ _ rest trivial covered
      | letValue parameter argument body =>
          have same : OCaml.MachineState.evaluate argument captured (.letValue parameter body captured :: rest) = next := by
            simpa only [OCaml.evaluateInstruction, declared, pure, Except.pure, Except.ok.injEq] using step
          rw [← same]
          exact continuation_covered_cons _ _ rest (let_pattern_member declared) covered
      | letRecursive definitions body =>
          have same : OCaml.MachineState.evaluate body (OCaml.recursiveEnvironment reference definitions captured) rest = next := by
            simpa only [OCaml.evaluateInstruction, declared, pure, Except.pure, Except.ok.injEq] using step
          rw [← same]
          exact covered
      | branch condition yes no =>
          have same : OCaml.MachineState.evaluate condition captured (.branch yes no captured :: rest) = next := by
            simpa only [OCaml.evaluateInstruction, declared, pure, Except.pure, Except.ok.injEq] using step
          rw [← same]
          exact continuation_covered_cons _ _ rest trivial covered
      | andThen left right =>
          have same : OCaml.MachineState.evaluate left captured (.andThen right captured :: rest) = next := by
            simpa only [OCaml.evaluateInstruction, declared, pure, Except.pure, Except.ok.injEq] using step
          rw [← same]
          exact continuation_covered_cons _ _ rest trivial covered
      | orElse left right =>
          have same : OCaml.MachineState.evaluate left captured (.orElse right captured :: rest) = next := by
            simpa only [OCaml.evaluateInstruction, declared, pure, Except.pure, Except.ok.injEq] using step
          rw [← same]
          exact continuation_covered_cons _ _ rest trivial covered
      | tuple fields =>
          apply start_arguments_covered program _ .tuple fields captured rest next covered
          simpa only [OCaml.evaluateInstruction, declared] using step
      | variant typeId constructor fields =>
          apply start_arguments_covered program _ (.variant typeId constructor) fields captured rest next covered
          simpa only [OCaml.evaluateInstruction, declared] using step
      | primitive operator arguments =>
          apply start_arguments_covered program _ (.primitive operator) arguments captured rest next covered
          simpa only [OCaml.evaluateInstruction, declared] using step
      | cons head tail =>
          have same : OCaml.MachineState.evaluate tail captured (.consTail head captured :: rest) = next := by
            simpa only [OCaml.evaluateInstruction, declared, pure, Except.pure, Except.ok.injEq] using step
          rw [← same]
          exact continuation_covered_cons _ _ rest trivial covered
      | matchValue scrutinee clauses =>
          have same : OCaml.MachineState.evaluate scrutinee captured (.matchValue clauses captured :: rest) = next := by
            simpa only [OCaml.evaluateInstruction, declared, pure, Except.pure, Except.ok.injEq] using step
          rw [← same]
          exact continuation_covered_cons _ _ rest (clause_pattern_member declared) covered

theorem return_value_covered (program : OCaml.Program) (actual : OCaml.Value) (rest : OCaml.Continuation)
    (next : OCaml.MachineState) (covered : ContinuationCovered (patterns program) rest)
    (step : OCaml.returnValue program actual rest = .ok next) : StateCovered (patterns program) next := by
  cases rest with
  | nil =>
      cases Except.ok.inj step
      trivial
  | cons frame rest =>
      have tailCovered := continuation_covered_tail (patterns program) frame rest covered
      cases frame with
      | argument function captured =>
          have same : OCaml.MachineState.evaluate function captured (.function actual :: rest) = next := by
            simpa only [OCaml.returnValue, pure, Except.pure, Except.ok.injEq] using step
          rw [← same]
          exact continuation_covered_cons _ _ rest trivial tailCovered
      | function argument => exact apply_closure_covered program _ actual argument rest next tailCovered step
      | letValue parameter body captured =>
          have same : OCaml.enterBody parameter actual body captured rest = next := by
            simpa only [OCaml.returnValue, pure, Except.pure, Except.ok.injEq] using step
          rw [← same]
          exact enter_body_covered _ parameter actual body captured rest tailCovered
      | branch yes no captured =>
          cases actual with
          | literal datum =>
              cases datum with
              | boolean choice =>
                  have same : OCaml.MachineState.evaluate (if choice then yes else no) captured rest = next := by
                    simpa only [OCaml.returnValue, pure, Except.pure, Except.ok.injEq] using step
                  rw [← same]
                  exact tailCovered
              | _ => simp [OCaml.returnValue] at step
          | _ => simp [OCaml.returnValue] at step
      | andThen right captured =>
          cases actual with
          | literal datum =>
              cases datum with
              | boolean choice =>
                  cases choice with
                  | false =>
                      have same : OCaml.MachineState.returned (.literal (.boolean false)) rest = next := by
                        simpa only [OCaml.returnValue, pure, Except.pure, Except.ok.injEq] using step
                      rw [← same]
                      exact tailCovered
                  | true =>
                      have same : OCaml.MachineState.evaluate right captured (.booleanResult :: rest) = next := by
                        simpa only [OCaml.returnValue, pure, Except.pure, Except.ok.injEq] using step
                      rw [← same]
                      exact continuation_covered_cons _ _ rest trivial tailCovered
              | _ => simp [OCaml.returnValue] at step
          | _ => simp [OCaml.returnValue] at step
      | orElse right captured =>
          cases actual with
          | literal datum =>
              cases datum with
              | boolean choice =>
                  cases choice with
                  | false =>
                      have same : OCaml.MachineState.evaluate right captured (.booleanResult :: rest) = next := by
                        simpa only [OCaml.returnValue, pure, Except.pure, Except.ok.injEq] using step
                      rw [← same]
                      exact continuation_covered_cons _ _ rest trivial tailCovered
                  | true =>
                      have same : OCaml.MachineState.returned (.literal (.boolean true)) rest = next := by
                        simpa only [OCaml.returnValue, pure, Except.pure, Except.ok.injEq] using step
                      rw [← same]
                      exact tailCovered
              | _ => simp [OCaml.returnValue] at step
          | _ => simp [OCaml.returnValue] at step
      | booleanResult =>
          cases actual with
          | literal datum =>
              cases datum with
              | boolean choice =>
                  have same : OCaml.MachineState.returned (.literal (.boolean choice)) rest = next := by
                    simpa only [OCaml.returnValue, pure, Except.pure, Except.ok.injEq] using step
                  rw [← same]
                  exact tailCovered
              | _ => simp [OCaml.returnValue] at step
          | _ => simp [OCaml.returnValue] at step
      | consTail head captured =>
          have same : OCaml.MachineState.evaluate head captured (.consHead actual :: rest) = next := by
            simpa only [OCaml.returnValue, pure, Except.pure, Except.ok.injEq] using step
          rw [← same]
          exact continuation_covered_cons _ _ rest trivial tailCovered
      | consHead tail =>
          have same : OCaml.MachineState.returned (.cons actual tail) rest = next := by
            simpa only [OCaml.returnValue, pure, Except.pure, Except.ok.injEq] using step
          rw [← same]
          exact tailCovered
      | gather kind remaining captured suffix =>
          cases remaining with
          | nil => exact finish_build_covered program _ kind (actual :: suffix) rest next tailCovered step
          | cons head later =>
              have same : OCaml.MachineState.evaluate head captured (.gather kind later captured (actual :: suffix) :: rest) = next := by
                simpa only [OCaml.returnValue, pure, Except.pure, Except.ok.injEq] using step
              rw [← same]
              exact continuation_covered_cons _ _ rest trivial tailCovered
      | matchValue clauses captured =>
          cases selected : OCaml.selectClause clauses actual with
          | none =>
              have same : OCaml.MachineState.halted (.error .matchFailure) = next := by
                simpa only [OCaml.returnValue, selected, pure, Except.pure, Except.ok.injEq] using step
              rw [← same]
              trivial
          | some result =>
              rcases result with ⟨body, bindings⟩
              have same : OCaml.MachineState.evaluate body (OCaml.extend captured bindings) rest = next := by
                simpa only [OCaml.returnValue, selected, pure, Except.pure, Except.ok.injEq] using step
              rw [← same]
              exact tailCovered

theorem machine_step_covered (program : OCaml.Program) (source target : OCaml.MachineState)
    (covered : StateCovered (patterns program) source)
    (step : OCaml.machineStep program source = .ok (some target)) : StateCovered (patterns program) target := by
  cases source with
  | halted result => cases step
  | evaluate reference captured rest =>
      cases result : OCaml.evaluateInstruction program reference captured rest with
      | error error => simp [OCaml.machineStep, result, Except.map] at step
      | ok next =>
          have same : next = target := by simpa only [OCaml.machineStep, result, Except.map, Except.ok.injEq, Option.some.injEq] using step
          subst next
          exact evaluate_instruction_covered program reference captured rest target covered result
  | returned actual rest =>
      cases result : OCaml.returnValue program actual rest with
      | error error => simp [OCaml.machineStep, result, Except.map] at step
      | ok next =>
          have same : next = target := by simpa only [OCaml.machineStep, result, Except.map, Except.ok.injEq, Option.some.injEq] using step
          subst next
          exact return_value_covered program actual rest target covered result

theorem machine_path_covered (program : OCaml.Program) (source target : OCaml.MachineState)
    (covered : StateCovered (patterns program) source) (path : OCaml.MachinePath program source target) :
    StateCovered (patterns program) target := by
  induction path with
  | refl => exact covered
  | tail path step ih => exact machine_step_covered program _ _ ih step

theorem reachable_state_encodable (program : OCaml.Program) (state : OCaml.MachineState)
    (reachable : OCaml.MachinePath program (OCaml.begin program) state) :
    ∃ encoded, state? (patterns program) state = some encoded :=
  state?_exists (patterns program) state (machine_path_covered program _ state (initial_covered program) reachable)

theorem reachable_state_open (program : OCaml.Program) (state : OCaml.MachineState)
    (language : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext)
    (reachable : OCaml.MachinePath program (OCaml.begin program) state) :
    ∃ encoded, state? (patterns program) state = some encoded ∧
      Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted language free [] (.base "MlConfig") encoded ∧
      encoded.freeFvarNames = [] := by
  obtain ⟨encoded, found⟩ := reachable_state_encodable program state reachable
  exact ⟨encoded, found, state?_open language terms free [] (patterns program) state encoded found,
    state?_closed (patterns program) state encoded found⟩

#print axioms apply_closure_covered
#print axioms start_arguments_covered
#print axioms evaluate_instruction_covered
#print axioms machine_step_covered
#print axioms reachable_state_encodable
#print axioms reachable_state_open

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
