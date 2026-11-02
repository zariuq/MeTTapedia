import Mettapedia.Languages.OCaml.Evaluation
import Mettapedia.Languages.OCaml.Machine

/-! Continuation meanings relate the reference machine to the independent
evaluation judgments. A machine frame describes the source computation
still to perform after the current value or fault is returned.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000

namespace Mettapedia.Languages.OCaml

inductive Builds (program : Program) : Build → List Value → Result → Prop where
  | tuple {values} (arity : 2 ≤ values.length) : Builds program .tuple values (.ok (.tuple values))
  | variant {typeId constructor values} (declared : ⟨typeId, constructor, values.length⟩ ∈ program.constructors) :
      Builds program (.variant typeId constructor) values (.ok (.variant typeId constructor values))
  | primitive {operator values result} (calculated : operator.eval values = .ok result) :
      Builds program (.primitive operator) values result

inductive Continues (program : Program) : Continuation → Result → Result → Prop where
  | done {value} : Continues program [] (.ok value) (.ok value)
  | fault {continuation fault} : Continues program continuation (.error fault) (.error fault)
  | argument {function environment rest argument callable intermediate result}
      (evaluated : Evaluates program environment function (.ok callable))
      (applied : Applies program callable argument intermediate)
      (continued : Continues program rest intermediate result) :
      Continues program (.argument function environment :: rest) (.ok argument) result
  | argumentFault {function environment rest argument fault}
      (evaluated : Evaluates program environment function (.error fault)) :
      Continues program (.argument function environment :: rest) (.ok argument) (.error fault)
  | function {argument rest callable intermediate result}
      (applied : Applies program callable argument intermediate)
      (continued : Continues program rest intermediate result) :
      Continues program (.function argument :: rest) (.ok callable) result
  | letBody {pattern body environment rest value bindings intermediate result}
      (matched : matchPattern pattern value = some bindings)
      (evaluated : Evaluates program (extend environment bindings) body intermediate)
      (continued : Continues program rest intermediate result) :
      Continues program (.letValue pattern body environment :: rest) (.ok value) result
  | letMismatch {pattern body environment rest value}
      (mismatch : matchPattern pattern value = none) :
      Continues program (.letValue pattern body environment :: rest) (.ok value) (.error .matchFailure)
  | branch {yes no environment rest choice intermediate result}
      (evaluated : Evaluates program environment (if choice then yes else no) intermediate)
      (continued : Continues program rest intermediate result) :
      Continues program (.branch yes no environment :: rest) (.ok (.literal (.boolean choice))) result
  | andFalse {right environment rest result}
      (continued : Continues program rest (.ok (.literal (.boolean false))) result) :
      Continues program (.andThen right environment :: rest) (.ok (.literal (.boolean false))) result
  | andTrue {right environment rest value result}
      (evaluated : Evaluates program environment right (.ok (.literal (.boolean value))))
      (continued : Continues program rest (.ok (.literal (.boolean value))) result) :
      Continues program (.andThen right environment :: rest) (.ok (.literal (.boolean true))) result
  | andFault {right environment rest fault}
      (evaluated : Evaluates program environment right (.error fault)) :
      Continues program (.andThen right environment :: rest) (.ok (.literal (.boolean true))) (.error fault)
  | orTrue {right environment rest result}
      (continued : Continues program rest (.ok (.literal (.boolean true))) result) :
      Continues program (.orElse right environment :: rest) (.ok (.literal (.boolean true))) result
  | orFalse {right environment rest value result}
      (evaluated : Evaluates program environment right (.ok (.literal (.boolean value))))
      (continued : Continues program rest (.ok (.literal (.boolean value))) result) :
      Continues program (.orElse right environment :: rest) (.ok (.literal (.boolean false))) result
  | orFault {right environment rest fault}
      (evaluated : Evaluates program environment right (.error fault)) :
      Continues program (.orElse right environment :: rest) (.ok (.literal (.boolean false))) (.error fault)
  | boolean {rest value result}
      (continued : Continues program rest (.ok (.literal (.boolean value))) result) :
      Continues program (.booleanResult :: rest) (.ok (.literal (.boolean value))) result
  | consTail {head environment rest tail first result}
      (evaluated : Evaluates program environment head (.ok first))
      (continued : Continues program rest (.ok (.cons first tail)) result) :
      Continues program (.consTail head environment :: rest) (.ok tail) result
  | consTailFault {head environment rest tail fault}
      (evaluated : Evaluates program environment head (.error fault)) :
      Continues program (.consTail head environment :: rest) (.ok tail) (.error fault)
  | consHead {tail rest head result}
      (continued : Continues program rest (.ok (.cons head tail)) result) :
      Continues program (.consHead tail :: rest) (.ok head) result
  | gather {kind reversed environment suffix rest value remaining intermediate result}
      (evaluated : EvaluatesArguments program environment reversed.reverse (.ok remaining))
      (built : Builds program kind (remaining ++ value :: suffix) intermediate)
      (continued : Continues program rest intermediate result) :
      Continues program (.gather kind reversed environment suffix :: rest) (.ok value) result
  | gatherFault {kind reversed environment suffix rest value fault}
      (evaluated : EvaluatesArguments program environment reversed.reverse (.error fault)) :
      Continues program (.gather kind reversed environment suffix :: rest) (.ok value) (.error fault)
  | matchBody {clauses environment rest value body bindings intermediate result}
      (selected : selectClause clauses value = some (body, bindings))
      (evaluated : Evaluates program (extend environment bindings) body intermediate)
      (continued : Continues program rest intermediate result) :
      Continues program (.matchValue clauses environment :: rest) (.ok value) result
  | matchFailure {clauses environment rest value}
      (mismatch : selectClause clauses value = none) :
      Continues program (.matchValue clauses environment :: rest) (.ok value) (.error .matchFailure)

inductive StateMeaning (program : Program) : MachineState → Result → Prop where
  | evaluate {code environment continuation intermediate result}
      (evaluated : Evaluates program environment code intermediate)
      (continued : Continues program continuation intermediate result) :
      StateMeaning program (.evaluate code environment continuation) result
  | returned {value continuation result} (continued : Continues program continuation (.ok value) result) :
      StateMeaning program (.returned value continuation) result
  | halted {result} : StateMeaning program (.halted result) result

theorem Continues.nil_iff {program : Program} {intermediate result : Result} :
    Continues program [] intermediate result ↔ intermediate = result := by
  constructor
  · intro continued
    cases continued <;> rfl
  · rintro rfl
    cases intermediate with
    | ok value => exact .done
    | error fault => exact .fault

theorem Continues.fault_iff {program : Program} {continuation : Continuation} {fault : Fault} {result : Result} :
    Continues program continuation (.error fault) result ↔ result = .error fault := by
  constructor
  · intro continued
    cases continued
    rfl
  · rintro rfl
    exact .fault

theorem StateMeaning.begin_iff {program : Program} {result : Result} :
    StateMeaning program (begin program) result ↔ Evaluates program [] program.entry result := by
  constructor
  · intro meaning
    cases meaning with
    | evaluate evaluated continued =>
      have same := Continues.nil_iff.mp continued
      exact same ▸ evaluated
  · intro evaluated
    exact .evaluate evaluated (Continues.nil_iff.mpr rfl)

theorem arguments_append_value {program : Program} {environment : Environment}
    {first second : List Code} {left right : List Value}
    (before : EvaluatesArguments program environment first (.ok left))
    (after : EvaluatesArguments program environment second (.ok right)) :
    EvaluatesArguments program environment (first ++ second) (.ok (left ++ right)) := by
  induction first generalizing left with
  | nil => cases before; exact after
  | cons first rest ih =>
    cases before with
    | cons last head => exact .cons (ih last) head

theorem arguments_append_fault {program : Program} {environment : Environment}
    (first : List Code) {second : List Code} {fault : Fault}
    (after : EvaluatesArguments program environment second (.error fault)) :
    EvaluatesArguments program environment (first ++ second) (.error fault) := by
  induction first with
  | nil => exact after
  | cons first rest ih => exact .tailFault ih

theorem arguments_append_head_fault {program : Program} {environment : Environment}
    {first second : List Code} {right : List Value} {fault : Fault}
    (before : EvaluatesArguments program environment first (.error fault))
    (after : EvaluatesArguments program environment second (.ok right)) :
    EvaluatesArguments program environment (first ++ second) (.error fault) := by
  induction first with
  | nil => cases before
  | cons first rest ih =>
    cases before with
    | tailFault last => exact .tailFault (ih last)
    | headFault last head => exact .headFault (arguments_append_value last after) head

theorem stateMeaning_fault {program : Program} {fault : Fault} {result : Result}
    (meaning : StateMeaning program (.halted (.error fault)) result) : result = .error fault := by
  cases meaning
  rfl

theorem finishBuild_reflects {program : Program} {kind : Build} {values : List Value}
    {continuation : Continuation} {next : MachineState} {result : Result}
    (stepped : finishBuild program kind values continuation = .ok next)
    (meaning : StateMeaning program next result) :
    ∃ intermediate, Builds program kind values intermediate ∧ Continues program continuation intermediate result := by
  cases kind with
  | tuple =>
    simp only [finishBuild] at stepped
    split at stepped
    · cases stepped
    · rename_i arity
      cases Except.ok.inj stepped
      cases meaning with
      | returned continued => exact ⟨_, .tuple (by omega), continued⟩
  | variant typeId constructor =>
    simp only [finishBuild] at stepped
    split at stepped
    · rename_i found
      have member : ⟨typeId, constructor, values.length⟩ ∈ program.constructors := by
        obtain ⟨declaration, member, same⟩ := List.any_eq_true.mp found
        simp only [Bool.and_eq_true, beq_iff_eq] at same
        rcases declaration with ⟨a, b, c⟩
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := same
        exact member
      cases Except.ok.inj stepped
      cases meaning with
      | returned continued => exact ⟨_, .variant member, continued⟩
    · cases stepped
  | primitive operator =>
    simp only [finishBuild] at stepped
    cases calculated : operator.eval values with
    | error error =>
      rw [calculated] at stepped
      change Except.error error = Except.ok next at stepped
      cases stepped
    | ok intermediate =>
      cases intermediate with
      | ok value =>
        rw [calculated] at stepped
        change Except.ok (.returned value continuation) = Except.ok next at stepped
        cases Except.ok.inj stepped
        cases meaning with
        | returned continued => exact ⟨_, .primitive calculated, continued⟩
      | error fault =>
        rw [calculated] at stepped
        change Except.ok (.halted (.error fault)) = Except.ok next at stepped
        cases Except.ok.inj stepped
        cases meaning
        exact ⟨_, .primitive calculated, .fault⟩

theorem enterBody_reflects {program : Program} {parameter : MatchPattern} {argument : Value} {body : Code}
    {captured : Environment} {continuation : Continuation} {result : Result}
    (meaning : StateMeaning program (enterBody parameter argument body captured continuation) result) :
    (∃ bindings intermediate, matchPattern parameter argument = some bindings ∧
      Evaluates program (extend captured bindings) body intermediate ∧ Continues program continuation intermediate result) ∨
    (matchPattern parameter argument = none ∧ result = .error .matchFailure) := by
  unfold enterBody at meaning
  cases matched : matchPattern parameter argument with
  | none =>
    rw [matched] at meaning
    exact Or.inr ⟨rfl, stateMeaning_fault meaning⟩
  | some bindings =>
    rw [matched] at meaning
    cases meaning with
    | evaluate evaluated continued => exact Or.inl ⟨bindings, _, rfl, evaluated, continued⟩

theorem applyClosure_reflects {program : Program} {callable argument : Value} {continuation : Continuation}
    {next : MachineState} {result : Result}
    (stepped : applyClosure program callable argument continuation = .ok next)
    (meaning : StateMeaning program next result) :
    ∃ intermediate, Applies program callable argument intermediate ∧ Continues program continuation intermediate result := by
  cases callable with
  | closure function captured =>
    cases function with
    | lambda code =>
      simp only [applyClosure] at stepped
      split at stepped
      · rename_i parameter body instruction
        cases Except.ok.inj stepped
        rcases enterBody_reflects meaning with matched | mismatch
        · obtain ⟨bindings, intermediate, found, evaluated, continued⟩ := matched
          exact ⟨intermediate, .lambda instruction found evaluated, continued⟩
        · obtain ⟨found, rfl⟩ := mismatch
          exact ⟨_, .lambdaMismatch instruction found, .fault⟩
      · cases stepped
    | recursive group slot =>
      simp only [applyClosure] at stepped
      split at stepped
      · rename_i definitions groupBody groupInstruction
        split at stepped
        · rename_i code definition
          split at stepped
          · rename_i parameter body instruction
            cases Except.ok.inj stepped
            rcases enterBody_reflects meaning with matched | mismatch
            · obtain ⟨bindings, intermediate, found, evaluated, continued⟩ := matched
              exact ⟨intermediate, .recursive groupInstruction definition instruction found evaluated, continued⟩
            · obtain ⟨found, rfl⟩ := mismatch
              exact ⟨_, .recursiveMismatch groupInstruction definition instruction found, .fault⟩
          · cases stepped
        · cases stepped
      · cases stepped
  | literal _ => cases stepped
  | tuple _ => cases stepped
  | cons _ _ => cases stepped
  | variant _ _ _ => cases stepped

theorem returnValue_reflects {program : Program} {value : Value} {continuation : Continuation}
    {next : MachineState} {result : Result}
    (stepped : returnValue program value continuation = .ok next)
    (meaning : StateMeaning program next result) : Continues program continuation (.ok value) result := by
  cases continuation with
  | nil =>
    cases Except.ok.inj stepped
    cases meaning
    exact .done
  | cons frame rest =>
    cases frame with
    | argument function environment =>
      cases Except.ok.inj stepped
      cases meaning with
      | evaluate evaluated continued =>
        cases continued with
        | fault => exact .argumentFault evaluated
        | function applied continued => exact .argument evaluated applied continued
    | function argument =>
      obtain ⟨intermediate, applied, continued⟩ := applyClosure_reflects stepped meaning
      exact .function applied continued
    | letValue pattern body environment =>
      change Except.ok (enterBody pattern value body environment rest) = Except.ok next at stepped
      cases Except.ok.inj stepped
      rcases enterBody_reflects meaning with matched | mismatch
      · obtain ⟨bindings, intermediate, found, evaluated, continued⟩ := matched
        exact .letBody found evaluated continued
      · obtain ⟨found, rfl⟩ := mismatch
        exact .letMismatch found
    | branch yes no environment =>
      cases value with
      | literal literal =>
        cases literal with
        | boolean choice =>
          cases Except.ok.inj stepped
          cases meaning with
          | evaluate evaluated continued => exact .branch evaluated continued
        | integer _ => cases stepped
        | unit => cases stepped
        | nil => cases stepped
        | string _ => cases stepped
      | tuple _ => cases stepped
      | cons _ _ => cases stepped
      | variant _ _ _ => cases stepped
      | closure _ _ => cases stepped
    | andThen right environment =>
      cases value with
      | literal literal =>
        cases literal with
        | boolean choice =>
          cases choice with
          | false =>
            cases Except.ok.inj stepped
            cases meaning with
            | returned continued => exact .andFalse continued
          | true =>
            cases Except.ok.inj stepped
            cases meaning with
            | evaluate evaluated continued =>
              cases continued with
              | fault => exact .andFault evaluated
              | boolean continued => exact .andTrue evaluated continued
        | integer _ => cases stepped
        | unit => cases stepped
        | nil => cases stepped
        | string _ => cases stepped
      | tuple _ => cases stepped
      | cons _ _ => cases stepped
      | variant _ _ _ => cases stepped
      | closure _ _ => cases stepped
    | orElse right environment =>
      cases value with
      | literal literal =>
        cases literal with
        | boolean choice =>
          cases choice with
          | true =>
            cases Except.ok.inj stepped
            cases meaning with
            | returned continued => exact .orTrue continued
          | false =>
            cases Except.ok.inj stepped
            cases meaning with
            | evaluate evaluated continued =>
              cases continued with
              | fault => exact .orFault evaluated
              | boolean continued => exact .orFalse evaluated continued
        | integer _ => cases stepped
        | unit => cases stepped
        | nil => cases stepped
        | string _ => cases stepped
      | tuple _ => cases stepped
      | cons _ _ => cases stepped
      | variant _ _ _ => cases stepped
      | closure _ _ => cases stepped
    | booleanResult =>
      cases value with
      | literal literal =>
        cases literal with
        | boolean choice =>
          cases Except.ok.inj stepped
          cases meaning with
          | returned continued => exact .boolean continued
        | integer _ => cases stepped
        | unit => cases stepped
        | nil => cases stepped
        | string _ => cases stepped
      | tuple _ => cases stepped
      | cons _ _ => cases stepped
      | variant _ _ _ => cases stepped
      | closure _ _ => cases stepped
    | consTail head environment =>
      cases Except.ok.inj stepped
      cases meaning with
      | evaluate evaluated continued =>
        cases continued with
        | fault => exact .consTailFault evaluated
        | consHead continued => exact .consTail evaluated continued
    | consHead tail =>
      cases Except.ok.inj stepped
      cases meaning with
      | returned continued => exact .consHead continued
    | gather kind reversed environment suffix =>
      cases reversed with
      | nil =>
        obtain ⟨intermediate, built, continued⟩ := finishBuild_reflects stepped meaning
        exact .gather .nil built continued
      | cons code later =>
        cases Except.ok.inj stepped
        cases meaning with
        | evaluate evaluated continued =>
          cases continued with
          | fault =>
            apply Continues.gatherFault
            simpa only [List.reverse_cons] using
              arguments_append_fault later.reverse (EvaluatesArguments.headFault .nil evaluated)
          | gather remaining built continued =>
            apply Continues.gather
            · simpa only [List.reverse_cons] using
                arguments_append_value remaining (EvaluatesArguments.cons .nil evaluated)
            · simpa only [List.append_assoc, List.cons_append, List.nil_append] using built
            · exact continued
          | gatherFault failed =>
            apply Continues.gatherFault
            simpa only [List.reverse_cons] using
              arguments_append_head_fault failed (EvaluatesArguments.cons .nil evaluated)
    | matchValue clauses environment =>
      dsimp only [returnValue] at stepped
      cases selected : selectClause clauses value with
      | none =>
        rw [selected] at stepped
        cases Except.ok.inj stepped
        cases meaning
        exact .matchFailure selected
      | some pair =>
        obtain ⟨body, bindings⟩ := pair
        rw [selected] at stepped
        cases Except.ok.inj stepped
        cases meaning with
        | evaluate evaluated continued => exact .matchBody selected evaluated continued

theorem startArguments_reflects {program : Program} {kind : Build} {arguments : List Code}
    {environment : Environment} {continuation : Continuation} {next : MachineState} {result : Result}
    (stepped : startArguments program kind arguments environment continuation = .ok next)
    (meaning : StateMeaning program next result) :
    (∃ values intermediate, EvaluatesArguments program environment arguments (.ok values) ∧
      Builds program kind values intermediate ∧ Continues program continuation intermediate result) ∨
    (∃ fault, EvaluatesArguments program environment arguments (.error fault) ∧ result = .error fault) := by
  unfold startArguments at stepped
  cases shape : arguments.reverse with
  | nil =>
    have empty : arguments = [] := by simpa using congrArg List.reverse shape
    subst arguments
    rw [List.reverse_nil] at stepped
    obtain ⟨intermediate, built, continued⟩ := finishBuild_reflects stepped meaning
    exact Or.inl ⟨[], intermediate, .nil, built, continued⟩
  | cons last rest =>
    rw [shape] at stepped
    cases Except.ok.inj stepped
    have original : arguments = rest.reverse ++ [last] := by
      simpa only [List.reverse_reverse, List.reverse_cons, List.reverse_nil, List.nil_append] using
        congrArg List.reverse shape
    cases meaning with
    | evaluate evaluated continued =>
      cases continued with
      | fault =>
        refine Or.inr ⟨_, ?_, rfl⟩
        rw [original]
        exact arguments_append_fault rest.reverse (.headFault .nil evaluated)
      | gather remaining built continued =>
        have combined := arguments_append_value remaining (.cons .nil evaluated)
        rw [← original] at combined
        exact Or.inl ⟨_, _, combined, by simpa only [List.append_nil] using built, continued⟩
      | gatherFault failed =>
        refine Or.inr ⟨_, ?_, rfl⟩
        rw [original]
        exact arguments_append_head_fault failed (.cons .nil evaluated)

theorem evaluateInstruction_reflects {program : Program} {code : Code} {environment : Environment}
    {continuation : Continuation} {next : MachineState} {result : Result}
    (stepped : evaluateInstruction program code environment continuation = .ok next)
    (meaning : StateMeaning program next result) :
    StateMeaning program (.evaluate code environment continuation) result := by
  unfold evaluateInstruction at stepped
  cases instruction : program.instruction? code with
  | none =>
    rw [instruction] at stepped
    cases stepped
  | some operation =>
    rw [instruction] at stepped
    cases operation with
    | literal value =>
      cases Except.ok.inj stepped
      cases meaning with
      | returned continued => exact .evaluate (.literal instruction) continued
    | «variable» index =>
      dsimp only at stepped
      cases binding : environment[index]? with
      | none => rw [binding] at stepped; cases stepped
      | some value =>
        rw [binding] at stepped
        cases Except.ok.inj stepped
        cases meaning with
        | returned continued => exact .evaluate (.variable instruction binding) continued
    | lambda parameter body =>
      cases Except.ok.inj stepped
      cases meaning with
      | returned continued => exact .evaluate (.lambda instruction) continued
    | apply function argument =>
      cases Except.ok.inj stepped
      cases meaning with
      | evaluate argumentValue continued =>
        cases continued with
        | fault => exact .evaluate (.argumentFault instruction argumentValue) .fault
        | argument functionValue applied continued =>
          exact .evaluate (.application instruction argumentValue functionValue applied) continued
        | argumentFault functionFault =>
          exact .evaluate (.functionFault instruction argumentValue functionFault) .fault
    | letValue pattern value body =>
      cases Except.ok.inj stepped
      cases meaning with
      | evaluate valueMeaning continued =>
        cases continued with
        | fault => exact .evaluate (.letFault instruction valueMeaning) .fault
        | letBody matched bodyMeaning continued =>
          exact .evaluate (.letBody instruction valueMeaning matched bodyMeaning) continued
        | letMismatch mismatch => exact .evaluate (.letMismatch instruction valueMeaning mismatch) .fault
    | letRecursive definitions body =>
      cases Except.ok.inj stepped
      cases meaning with
      | evaluate evaluated continued => exact .evaluate (.recursive instruction evaluated) continued
    | branch condition yes no =>
      cases Except.ok.inj stepped
      cases meaning with
      | evaluate conditionMeaning continued =>
        cases continued with
        | fault => exact .evaluate (.conditionFault instruction conditionMeaning) .fault
        | branch evaluated continued => exact .evaluate (.branch instruction conditionMeaning evaluated) continued
    | andThen left right =>
      cases Except.ok.inj stepped
      cases meaning with
      | evaluate evaluated continued =>
        cases continued with
        | fault => exact .evaluate (.andFault instruction evaluated) .fault
        | andFalse continued => exact .evaluate (.andFalse instruction evaluated) continued
        | andTrue rightMeaning continued => exact .evaluate (.andRightValue instruction evaluated rightMeaning) continued
        | andFault rightMeaning => exact .evaluate (.andRightFault instruction evaluated rightMeaning) .fault
    | orElse left right =>
      cases Except.ok.inj stepped
      cases meaning with
      | evaluate evaluated continued =>
        cases continued with
        | fault => exact .evaluate (.orFault instruction evaluated) .fault
        | orTrue continued => exact .evaluate (.orTrue instruction evaluated) continued
        | orFalse rightMeaning continued => exact .evaluate (.orRightValue instruction evaluated rightMeaning) continued
        | orFault rightMeaning => exact .evaluate (.orRightFault instruction evaluated rightMeaning) .fault
    | cons head tail =>
      cases Except.ok.inj stepped
      cases meaning with
      | evaluate evaluated continued =>
        cases continued with
        | fault => exact .evaluate (.consTailFault instruction evaluated) .fault
        | consTail first continued => exact .evaluate (.cons instruction evaluated first) continued
        | consTailFault first => exact .evaluate (.consHeadFault instruction evaluated first) .fault
    | matchValue scrutinee clauses =>
      cases Except.ok.inj stepped
      cases meaning with
      | evaluate evaluated continued =>
        cases continued with
        | fault => exact .evaluate (.matchFault instruction evaluated) .fault
        | matchBody selected bodyMeaning continued =>
          exact .evaluate (.matchBody instruction evaluated selected bodyMeaning) continued
        | matchFailure mismatch => exact .evaluate (.matchFailure instruction evaluated mismatch) .fault
    | tuple fields =>
      rcases startArguments_reflects stepped meaning with built | failed
      · obtain ⟨values, intermediate, evaluated, built, continued⟩ := built
        cases built with
        | tuple arity => exact .evaluate (.tuple instruction evaluated arity) continued
      · obtain ⟨fault, evaluated, rfl⟩ := failed
        exact .evaluate (.tupleFault instruction evaluated) .fault
    | variant typeId constructor fields =>
      rcases startArguments_reflects stepped meaning with built | failed
      · obtain ⟨values, intermediate, evaluated, built, continued⟩ := built
        cases built with
        | variant declared => exact .evaluate (.variant instruction evaluated declared) continued
      · obtain ⟨fault, evaluated, rfl⟩ := failed
        exact .evaluate (.variantFault instruction evaluated) .fault
    | primitive operator arguments =>
      rcases startArguments_reflects stepped meaning with built | failed
      · obtain ⟨values, intermediate, evaluated, built, continued⟩ := built
        cases built with
        | primitive calculated => exact .evaluate (.primitive instruction evaluated calculated) continued
      · obtain ⟨fault, evaluated, rfl⟩ := failed
        exact .evaluate (.primitiveFault instruction evaluated) .fault

theorem machineStep_reflects {program : Program} {state next : MachineState} {result : Result}
    (stepped : machineStep program state = .ok (some next))
    (meaning : StateMeaning program next result) : StateMeaning program state result := by
  cases state with
  | halted _ => cases stepped
  | evaluate code environment continuation =>
    cases actual : evaluateInstruction program code environment continuation with
    | error error => simp [machineStep, actual, Except.map] at stepped
    | ok nextState =>
      have same : nextState = next := by simpa [machineStep, actual, Except.map] using stepped
      subst nextState
      exact evaluateInstruction_reflects actual meaning
  | returned value continuation =>
    cases actual : returnValue program value continuation with
    | error error => simp [machineStep, actual, Except.map] at stepped
    | ok nextState =>
      have same : nextState = next := by simpa [machineStep, actual, Except.map] using stepped
      subst nextState
      exact .returned (returnValue_reflects actual meaning)

theorem completed_run_meaning (program : Program) (budget : Nat) (state : MachineState) (result : Result)
    (completed : run program budget state = .complete result) : StateMeaning program state result := by
  induction budget generalizing state with
  | zero =>
    cases state with
    | evaluate _ _ _ => cases completed
    | returned _ _ => cases completed
    | halted actual =>
      cases RunResult.complete.inj completed
      exact .halted
  | succ budget ih =>
    cases state with
    | halted actual =>
      cases RunResult.complete.inj completed
      exact .halted
    | evaluate code environment continuation =>
      cases stepping : machineStep program (.evaluate code environment continuation) with
      | error error => simp [run, stepping] at completed
      | ok successor =>
        cases successor with
        | none => simp [run, stepping] at completed
        | some next =>
          have rest : run program budget next = .complete result := by simpa only [run, stepping] using completed
          exact machineStep_reflects stepping (ih next rest)
    | returned value continuation =>
      cases stepping : machineStep program (.returned value continuation) with
      | error error => simp [run, stepping] at completed
      | ok successor =>
        cases successor with
        | none => simp [run, stepping] at completed
        | some next =>
          have rest : run program budget next = .complete result := by simpa only [run, stepping] using completed
          exact machineStep_reflects stepping (ih next rest)

theorem run_sound {program : Program} {budget : Nat} {result : Result}
    (completed : run program budget (begin program) = .complete result) :
    Evaluates program [] program.entry result :=
  StateMeaning.begin_iff.mp (completed_run_meaning program budget (begin program) result completed)

theorem resumed_run_sound {program : Program} {first second : Nat} {result : Result}
    (completed : resume program second (run program first (begin program)) = .complete result) :
    Evaluates program [] program.entry result := by
  rw [run_resume] at completed
  exact run_sound completed

#print axioms machineStep_reflects
#print axioms run_sound
#print axioms resumed_run_sound

end Mettapedia.Languages.OCaml
