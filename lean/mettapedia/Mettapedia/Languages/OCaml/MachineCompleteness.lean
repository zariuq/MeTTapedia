import Mettapedia.Languages.OCaml.MachineCorrectness
import Mathlib.Logic.Relation

/-! Finite source evaluation derivations are realized by the actual
environment machine. The induction is strengthened over continuations so
recursive calls, right-to-left argument gathering and faults compose.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.OCaml

def MachineTransition (program : Program) (source target : MachineState) : Prop :=
  machineStep program source = .ok (some target)

abbrev MachinePath (program : Program) := Relation.ReflTransGen (MachineTransition program)

def resultState (result : Result) (continuation : Continuation) : MachineState := match result with
  | .ok value => .returned value continuation
  | .error fault => .halted (.error fault)

theorem evaluate_path {program : Program} {code : Code} {environment : Environment}
    {continuation : Continuation} {next : MachineState}
    (stepped : evaluateInstruction program code environment continuation = .ok next) :
    MachinePath program (.evaluate code environment continuation) next :=
  Relation.ReflTransGen.single (by simp [MachineTransition, machineStep, stepped, Except.map])

theorem return_path {program : Program} {value : Value} {continuation : Continuation} {next : MachineState}
    (stepped : returnValue program value continuation = .ok next) :
    MachinePath program (.returned value continuation) next :=
  Relation.ReflTransGen.single (by simp [MachineTransition, machineStep, stepped, Except.map])

def EvaluatesRealized (program : Program) (environment : Environment) (code : Code) (result : Result) : Prop :=
  ∀ continuation, MachinePath program (.evaluate code environment continuation) (resultState result continuation)

def AppliesRealized (program : Program) (callable argument : Value) (result : Result) : Prop :=
  ∀ continuation, ∃ next, applyClosure program callable argument continuation = .ok next ∧
    MachinePath program next (resultState result continuation)

def gatherState (program : Program) (kind : Build) (pending : List Code)
    (environment : Environment) (suffix : List Value) (continuation : Continuation) :
    Except InternalError MachineState := match pending with
  | [] => finishBuild program kind suffix continuation
  | last :: rest => .ok (.evaluate last environment (.gather kind rest environment suffix :: continuation))

def ArgumentsRealized (program : Program) (environment : Environment) (arguments : List Code)
    (result : Except Fault (List Value)) : Prop :=
  ∀ kind suffix continuation pending finish,
    (match result with
      | .ok values => gatherState program kind pending environment (values ++ suffix) continuation
      | .error fault => .ok (.halted (.error fault))) = .ok finish →
    ∃ start,
      gatherState program kind (arguments.reverse ++ pending) environment suffix continuation = .ok start ∧
      MachinePath program start finish

theorem literal_realized {program : Program} {environment : Environment} {code : Code} {value : Literal}
    (instruction : program.instruction? code = some (.literal value)) :
    EvaluatesRealized program environment code (.ok (.literal value)) := by
  intro continuation
  exact evaluate_path (by rw [evaluateInstruction, instruction]; rfl)

theorem variable_realized {program : Program} {environment : Environment} {code index : Code} {value : Value}
    (instruction : program.instruction? code = some (.variable index))
    (binding : environment[index]? = some value) : EvaluatesRealized program environment code (.ok value) := by
  intro continuation
  exact evaluate_path (by simp only [evaluateInstruction, instruction]; rw [binding]; rfl)

theorem lambda_realized {program : Program} {environment : Environment} {code : Code}
    {parameter : MatchPattern} {body : Code}
    (instruction : program.instruction? code = some (.lambda parameter body)) :
    EvaluatesRealized program environment code (.ok (.closure (.lambda code) environment)) := by
  intro continuation
  exact evaluate_path (by rw [evaluateInstruction, instruction]; rfl)

theorem finishBuild_realizes {program : Program} {kind : Build} {values : List Value} {result : Result}
    (built : Builds program kind values result) (continuation : Continuation) :
    finishBuild program kind values continuation = .ok (resultState result continuation) := by
  cases built with
  | tuple arity =>
    simp only [finishBuild, show ¬ values.length < 2 by omega, if_false]
    rfl
  | @variant typeId constructor _ declared =>
    have found : (program.constructors.any fun declaration =>
      declaration.typeId == typeId && declaration.ordinal == constructor && declaration.arity == values.length) = true :=
      List.any_eq_true.mpr ⟨_, declared, by simp⟩
    simp only [finishBuild, found, if_true]
    rfl
  | primitive calculated =>
    simp only [finishBuild, calculated]
    cases result <;> rfl

theorem arguments_nil_realized (program : Program) (environment : Environment) :
    ArgumentsRealized program environment [] (.ok []) := by
  intro kind suffix continuation pending next finished
  exact ⟨next, finished, .refl⟩

theorem arguments_tailFault_realized {program : Program} {environment : Environment}
    {first : Code} {rest : List Code} {fault : Fault}
    (realized : ArgumentsRealized program environment rest (.error fault)) :
    ArgumentsRealized program environment (first :: rest) (.error fault) := by
  intro kind suffix continuation pending finish finished
  obtain ⟨start, started, path⟩ := realized kind suffix continuation (first :: pending) finish finished
  refine ⟨start, ?_, path⟩
  simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using started

theorem arguments_headFault_realized {program : Program} {environment : Environment}
    {first : Code} {rest : List Code} {values : List Value} {fault : Fault}
    (tailRealized : ArgumentsRealized program environment rest (.ok values))
    (headRealized : EvaluatesRealized program environment first (.error fault)) :
    ArgumentsRealized program environment (first :: rest) (.error fault) := by
  intro kind suffix continuation pending finish finished
  cases Except.ok.inj finished
  let frame := Frame.gather kind pending environment (values ++ suffix)
  obtain ⟨start, started, path⟩ := tailRealized kind suffix continuation (first :: pending)
    (.evaluate first environment (frame :: continuation)) rfl
  refine ⟨start, ?_, path.trans (headRealized _)⟩
  simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using started

theorem arguments_cons_realized {program : Program} {environment : Environment}
    {first : Code} {rest : List Code} {value : Value} {values : List Value}
    (tailRealized : ArgumentsRealized program environment rest (.ok values))
    (headRealized : EvaluatesRealized program environment first (.ok value)) :
    ArgumentsRealized program environment (first :: rest) (.ok (value :: values)) := by
  intro kind suffix continuation pending finish finished
  let frame := Frame.gather kind pending environment (values ++ suffix)
  obtain ⟨start, started, path⟩ := tailRealized kind suffix continuation (first :: pending)
    (.evaluate first environment (frame :: continuation)) rfl
  refine ⟨start, ?_, path.trans ((headRealized _).trans ?_)⟩
  · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using started
  · apply return_path
    cases pending with
    | nil => simpa only [frame, returnValue, gatherState, List.cons_append] using finished
    | cons last rest =>
      cases Except.ok.inj finished
      rfl

theorem arguments_start_realized {program : Program} {environment : Environment}
    {arguments : List Code} {values : List Value} (realized : ArgumentsRealized program environment arguments (.ok values))
    {kind : Build} {result : Result} (built : Builds program kind values result) (continuation : Continuation) :
    ∃ start, startArguments program kind arguments environment continuation = .ok start ∧
      MachinePath program start (resultState result continuation) := by
  have finished := finishBuild_realizes built continuation
  obtain ⟨start, started, path⟩ := realized kind [] continuation [] (resultState result continuation)
    (by simpa only [gatherState, List.append_nil] using finished)
  refine ⟨start, ?_, path⟩
  cases shape : arguments.reverse <;> simpa only [startArguments, shape, List.append_nil, gatherState] using started

theorem arguments_start_fault {program : Program} {environment : Environment}
    {arguments : List Code} {fault : Fault} (realized : ArgumentsRealized program environment arguments (.error fault))
    (kind : Build) (continuation : Continuation) :
    ∃ start, startArguments program kind arguments environment continuation = .ok start ∧
      MachinePath program start (.halted (.error fault)) := by
  obtain ⟨start, started, path⟩ := realized kind [] continuation [] (.halted (.error fault)) rfl
  refine ⟨start, ?_, path⟩
  cases shape : arguments.reverse <;> simpa only [startArguments, shape, List.append_nil, gatherState] using started

theorem lambda_apply_realized {program : Program} {code body : Code} {parameter : MatchPattern}
    {captured : Environment} {argument : Value} {bindings : List Value} {result : Result}
    (instruction : program.instruction? code = some (.lambda parameter body))
    (matched : matchPattern parameter argument = some bindings)
    (bodyRealized : EvaluatesRealized program (extend captured bindings) body result) :
    AppliesRealized program (.closure (.lambda code) captured) argument result := by
  intro continuation
  refine ⟨_, ?_, bodyRealized continuation⟩
  simp only [applyClosure, instruction, enterBody, matched]

theorem lambda_mismatch_realized {program : Program} {code body : Code} {parameter : MatchPattern}
    {captured : Environment} {argument : Value}
    (instruction : program.instruction? code = some (.lambda parameter body))
    (mismatch : matchPattern parameter argument = none) :
    AppliesRealized program (.closure (.lambda code) captured) argument (.error .matchFailure) := by
  intro continuation
  exact ⟨_, by simp only [applyClosure, instruction, enterBody, mismatch, resultState], .refl⟩

theorem recursive_apply_realized {program : Program} {group slot groupBody code body : Code}
    {definitions : List Code} {parameter : MatchPattern} {captured : Environment} {argument : Value}
    {bindings : List Value} {result : Result}
    (groupInstruction : program.instruction? group = some (.letRecursive definitions groupBody))
    (definition : definitions[slot]? = some code)
    (instruction : program.instruction? code = some (.lambda parameter body))
    (matched : matchPattern parameter argument = some bindings)
    (bodyRealized : EvaluatesRealized program
      (extend (recursiveEnvironment group definitions captured) bindings) body result) :
    AppliesRealized program (.closure (.recursive group slot) captured) argument result := by
  intro continuation
  refine ⟨_, ?_, bodyRealized continuation⟩
  simp only [applyClosure, groupInstruction, definition, instruction, enterBody, matched]
  rfl

theorem recursive_mismatch_realized {program : Program} {group slot groupBody code body : Code}
    {definitions : List Code} {parameter : MatchPattern} {captured : Environment} {argument : Value}
    (groupInstruction : program.instruction? group = some (.letRecursive definitions groupBody))
    (definition : definitions[slot]? = some code)
    (instruction : program.instruction? code = some (.lambda parameter body))
    (mismatch : matchPattern parameter argument = none) :
    AppliesRealized program (.closure (.recursive group slot) captured) argument (.error .matchFailure) := by
  intro continuation
  refine ⟨_, ?_, .refl⟩
  simp only [applyClosure, groupInstruction, definition, instruction, enterBody, mismatch, resultState]
  rfl

theorem evaluates_realized {program : Program} {environment : Environment} {code : Code} {result : Result}
    (evaluated : Evaluates program environment code result) : EvaluatesRealized program environment code result := by
  refine Evaluates.rec
    (motive_1 := fun environment code result _ => EvaluatesRealized program environment code result)
    (motive_2 := fun callable argument result _ => AppliesRealized program callable argument result)
    (motive_3 := fun environment arguments result _ => ArgumentsRealized program environment arguments result)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ evaluated
  · intro environment code value instruction
    exact literal_realized instruction
  · intro environment code index value instruction binding
    exact variable_realized instruction binding
  · intro environment code parameter body instruction
    exact lambda_realized instruction
  · intro environment code definitions body result instruction _ bodyIH continuation
    exact (evaluate_path (by rw [evaluateInstruction, instruction]; rfl)).trans (bodyIH continuation)
  · intro environment code function argument fault instruction _ argumentIH continuation
    exact (evaluate_path (by rw [evaluateInstruction, instruction]; rfl)).trans
      (argumentIH (.argument function environment :: continuation))
  · intro environment code function argument actual fault instruction _ _ argumentIH functionIH continuation
    refine (evaluate_path (by rw [evaluateInstruction, instruction]; rfl)).trans ((argumentIH _).trans ?_)
    exact (return_path rfl).trans (functionIH (.function actual :: continuation))
  · intro environment code function argument actual callable result instruction _ _ _ argumentIH functionIH appliedIH continuation
    obtain ⟨next, applied, path⟩ := appliedIH continuation
    refine (evaluate_path (by rw [evaluateInstruction, instruction]; rfl)).trans ((argumentIH _).trans ?_)
    exact (return_path rfl).trans ((functionIH _).trans
      ((return_path (by simpa only [returnValue] using applied)).trans path))
  · intro environment code pattern value body fault instruction _ valueIH continuation
    exact (evaluate_path (by rw [evaluateInstruction, instruction]; rfl)).trans
      (valueIH (.letValue pattern body environment :: continuation))
  · intro environment code pattern value body actual instruction _ mismatch valueIH continuation
    refine (evaluate_path (by rw [evaluateInstruction, instruction]; rfl)).trans ((valueIH _).trans ?_)
    apply return_path
    simp only [returnValue, enterBody, mismatch, resultState]
    rfl
  · intro environment code pattern value body actual bindings result instruction _ matched _ valueIH bodyIH continuation
    refine (evaluate_path (by rw [evaluateInstruction, instruction]; rfl)).trans ((valueIH _).trans ?_)
    refine (return_path ?_).trans (bodyIH continuation)
    simp only [returnValue, enterBody, matched]
    rfl
  · intro environment code condition yes no fault instruction _ conditionIH continuation
    exact (evaluate_path (by rw [evaluateInstruction, instruction]; rfl)).trans
      (conditionIH (.branch yes no environment :: continuation))
  · intro environment code condition yes no choice result instruction _ _ conditionIH bodyIH continuation
    exact (evaluate_path (by rw [evaluateInstruction, instruction]; rfl)).trans
      ((conditionIH _).trans ((return_path rfl).trans (bodyIH _)))
  · intro environment code left right fault instruction _ leftIH continuation
    exact (evaluate_path (by rw [evaluateInstruction, instruction]; rfl)).trans
      (leftIH (.andThen right environment :: continuation))
  · intro environment code left right instruction _ leftIH continuation
    exact (evaluate_path (by rw [evaluateInstruction, instruction]; rfl)).trans
      ((leftIH _).trans (return_path rfl))
  · intro environment code left right fault instruction _ _ leftIH rightIH continuation
    exact (evaluate_path (by rw [evaluateInstruction, instruction]; rfl)).trans
      ((leftIH _).trans ((return_path rfl).trans (rightIH (.booleanResult :: continuation))))
  · intro environment code left right value instruction _ _ leftIH rightIH continuation
    exact (evaluate_path (by rw [evaluateInstruction, instruction]; rfl)).trans
      ((leftIH _).trans ((return_path rfl).trans ((rightIH _).trans (return_path rfl))))
  · intro environment code left right fault instruction _ leftIH continuation
    exact (evaluate_path (by rw [evaluateInstruction, instruction]; rfl)).trans
      (leftIH (.orElse right environment :: continuation))
  · intro environment code left right instruction _ leftIH continuation
    exact (evaluate_path (by rw [evaluateInstruction, instruction]; rfl)).trans
      ((leftIH _).trans (return_path rfl))
  · intro environment code left right fault instruction _ _ leftIH rightIH continuation
    exact (evaluate_path (by rw [evaluateInstruction, instruction]; rfl)).trans
      ((leftIH _).trans ((return_path rfl).trans (rightIH (.booleanResult :: continuation))))
  · intro environment code left right value instruction _ _ leftIH rightIH continuation
    exact (evaluate_path (by rw [evaluateInstruction, instruction]; rfl)).trans
      ((leftIH _).trans ((return_path rfl).trans ((rightIH _).trans (return_path rfl))))
  · intro environment code head tail fault instruction _ tailIH continuation
    exact (evaluate_path (by rw [evaluateInstruction, instruction]; rfl)).trans
      (tailIH (.consTail head environment :: continuation))
  · intro environment code head tail tailValue fault instruction _ _ tailIH headIH continuation
    exact (evaluate_path (by rw [evaluateInstruction, instruction]; rfl)).trans
      ((tailIH _).trans ((return_path rfl).trans (headIH (.consHead tailValue :: continuation))))
  · intro environment code head tail first last instruction _ _ tailIH headIH continuation
    exact (evaluate_path (by rw [evaluateInstruction, instruction]; rfl)).trans
      ((tailIH _).trans ((return_path rfl).trans ((headIH _).trans (return_path rfl))))
  · intro environment code fields fault instruction _ fieldsIH continuation
    obtain ⟨start, started, path⟩ := arguments_start_fault fieldsIH .tuple continuation
    exact (evaluate_path (by simpa only [evaluateInstruction, instruction] using started)).trans path
  · intro environment code fields values instruction _ arity fieldsIH continuation
    obtain ⟨start, started, path⟩ := arguments_start_realized fieldsIH (.tuple arity) continuation
    exact (evaluate_path (by simpa only [evaluateInstruction, instruction] using started)).trans path
  · intro environment code typeId constructor fields fault instruction _ fieldsIH continuation
    obtain ⟨start, started, path⟩ := arguments_start_fault fieldsIH (.variant typeId constructor) continuation
    exact (evaluate_path (by simpa only [evaluateInstruction, instruction] using started)).trans path
  · intro environment code typeId constructor fields values instruction _ declared fieldsIH continuation
    obtain ⟨start, started, path⟩ := arguments_start_realized fieldsIH (.variant declared) continuation
    exact (evaluate_path (by simpa only [evaluateInstruction, instruction] using started)).trans path
  · intro environment code operator arguments fault instruction _ argumentsIH continuation
    obtain ⟨start, started, path⟩ := arguments_start_fault argumentsIH (.primitive operator) continuation
    exact (evaluate_path (by simpa only [evaluateInstruction, instruction] using started)).trans path
  · intro environment code operator arguments values result instruction _ calculated argumentsIH continuation
    obtain ⟨start, started, path⟩ := arguments_start_realized argumentsIH (.primitive calculated) continuation
    exact (evaluate_path (by simpa only [evaluateInstruction, instruction] using started)).trans path
  · intro environment code scrutinee clauses fault instruction _ scrutineeIH continuation
    exact (evaluate_path (by rw [evaluateInstruction, instruction]; rfl)).trans
      (scrutineeIH (.matchValue clauses environment :: continuation))
  · intro environment code scrutinee clauses value instruction _ mismatch scrutineeIH continuation
    refine (evaluate_path (by rw [evaluateInstruction, instruction]; rfl)).trans ((scrutineeIH _).trans ?_)
    apply return_path
    simp only [returnValue, mismatch, resultState]
    rfl
  · intro environment code scrutinee clauses value body bindings result instruction _ selected _ scrutineeIH bodyIH continuation
    refine (evaluate_path (by rw [evaluateInstruction, instruction]; rfl)).trans ((scrutineeIH _).trans ?_)
    refine (return_path ?_).trans (bodyIH continuation)
    simp only [returnValue, selected]
    rfl
  · intro code parameter body captured argument bindings result instruction matched _ bodyIH
    exact lambda_apply_realized instruction matched bodyIH
  · intro code parameter body captured argument instruction mismatch
    exact lambda_mismatch_realized instruction mismatch
  · intro group slot definitions groupBody code parameter body captured argument bindings result
      groupInstruction definition instruction matched _ bodyIH
    exact recursive_apply_realized groupInstruction definition instruction matched bodyIH
  · intro group slot definitions groupBody code parameter body captured argument
      groupInstruction definition instruction mismatch
    exact recursive_mismatch_realized groupInstruction definition instruction mismatch
  · intro environment
    exact arguments_nil_realized program environment
  · intro environment first rest fault _ tailIH
    exact arguments_tailFault_realized tailIH
  · intro environment first rest values fault _ _ tailIH headIH
    exact arguments_headFault_realized tailIH headIH
  · intro environment first rest value values _ _ tailIH headIH
    exact arguments_cons_realized tailIH headIH

theorem run_prepend_transition {program : Program} {source target : MachineState} {budget : Nat} {result : Result}
    (step : MachineTransition program source target)
    (completed : run program budget target = .complete result) :
    run program (budget + 1) source = .complete result := by
  cases source with
  | halted _ => cases step
  | evaluate code environment continuation =>
    simpa only [run, show machineStep program (.evaluate code environment continuation) = .ok (some target) from step]
      using completed
  | returned value continuation =>
    simpa only [run, show machineStep program (.returned value continuation) = .ok (some target) from step]
      using completed

theorem path_to_budget {program : Program} {source target : MachineState}
    (path : MachinePath program source target) {budget : Nat} {result : Result}
    (completed : run program budget target = .complete result) :
    ∃ work, run program work source = .complete result := by
  induction path generalizing budget with
  | refl => exact ⟨budget, completed⟩
  | @tail middle last _ step ih =>
    exact ih (run_prepend_transition step completed)

theorem evaluates_complete {program : Program} {environment : Environment} {code : Code} {result : Result}
    (evaluated : Evaluates program environment code result) :
    ∃ budget, run program budget (.evaluate code environment []) = .complete result := by
  have path := evaluates_realized evaluated []
  cases result with
  | error fault => exact path_to_budget path (budget := 0) rfl
  | ok value =>
    have finished : MachinePath program (.returned value []) (.halted (.ok value)) := return_path rfl
    exact path_to_budget (path.trans finished) (budget := 0) rfl

theorem evaluates_iff_completed_run {program : Program} {result : Result} :
    Evaluates program [] program.entry result ↔ ∃ budget, run program budget (begin program) = .complete result := by
  constructor
  · exact evaluates_complete
  · rintro ⟨budget, completed⟩
    exact run_sound completed

theorem run_complete_stable {program : Program} {state : MachineState} {budget extra : Nat} {result : Result}
    (completed : run program budget state = .complete result) :
    run program (budget + extra) state = .complete result := by
  have same := run_resume program budget extra state
  rw [completed] at same
  exact same.symm

theorem completed_results_unique {program : Program} {state : MachineState} {first second : Nat}
    {left right : Result}
    (leftCompleted : run program first state = .complete left)
    (rightCompleted : run program second state = .complete right) : left = right := by
  have firstStable := run_complete_stable (extra := second) leftCompleted
  have secondStable := run_complete_stable (extra := first) rightCompleted
  rw [Nat.add_comm second first] at secondStable
  exact RunResult.complete.inj (firstStable.symm.trans secondStable)

theorem evaluates_deterministic {program : Program} {environment : Environment} {code : Code} {first second : Result}
    (left : Evaluates program environment code first) (right : Evaluates program environment code second) : first = second := by
  obtain ⟨leftBudget, leftRun⟩ := evaluates_complete left
  obtain ⟨rightBudget, rightRun⟩ := evaluates_complete right
  exact completed_results_unique leftRun rightRun

#print axioms evaluates_realized
#print axioms evaluates_complete
#print axioms evaluates_iff_completed_run
#print axioms evaluates_deterministic

end Mettapedia.Languages.OCaml
