import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaProgramEnvironment

/-!
# Recursive emitted-expression execution

Operational segments for the existing MeTTa interpreter compose under lexical
binding. The contracts preserve caller bindings and distinguish source
exhaustion from refusal. They quantify over sufficiently large target budgets.
The remaining argument-list and invocation cases are established separately.
-/

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalControlExecution
open Mettapedia.Languages.MeTTa.HE.CanonAbsorbsFreshening
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge
open Mettapedia.Languages.MeTTa.HE.LeaTTaSpecConformance
open Metta.Minimal

namespace Execution

/-- The public tagged observation of source evaluation. -/
def observation : Outcome → Atom
  | .value term => value (MeTTaData.encode term)
  | .failure => .symbol "nik:Failure"
  | .exhausted => .symbol "nik:Exhausted"

theorem observation_closed (result : Outcome) :
    (toLeaTTaAtom (observation result)).vars = [] := by
  cases result <;> simp [observation, value, call, toLeaTTaAtom, toLeaTTaAtoms,
    Metta.Atom.vars, data_atom_runtime_closed (MeTTaData.encode_data _)]

theorem observation_injective : Function.Injective observation := by
  intro left right same
  cases left <;> cases right <;> simp [observation, value, call] at same ⊢
  exact MeTTaData.encode_injective same

/-- An actual body segment at sufficient target budget. It preserves the
world, closed binding invariant, and unassigned caller names outside the
body. The result is ready for the retained function handler, before its
separate return step. This is a contract for the existing interpreter. -/
def BodyRun (environment : MinEnv) (state : St) (incoming : Metta.Bindings)
    (code result : Metta.Atom) (parentBody : Metta.Atom) (scope : List String)
    (continuation : Stack) : Prop :=
  let parent : Frame := {atom := parentBody, ret := .function, vars := scope}
  ∃ nextState output cost threshold,
    nextState.world = state.world ∧ ClosedValueBindings output ∧
    LeaRuntimeBindingInvariant output ∧
    (∀ key ∈ liveStackVars (parent :: continuation), key ∉ code.vars →
      Metta.Bindings.lookupVal incoming key = none →
      Metta.Bindings.lookupVal output key = none) ∧
    ∀ fuel, threshold ≤ fuel → ∀ rest done,
      interpretFuel environment (fuel + cost) state
        (⟨atomToStack code (parent :: continuation), incoming⟩ :: rest) done =
      interpretFuel environment fuel nextState
        (finItem (parent :: continuation) (.expr [.sym "return", result]) output :: rest) done

/-- Execution of emitted code after its source inputs have become data.
The assumptions are input well-formedness and a static loaded world, not
agreement with the desired result. -/
def CompiledExecutes (environment : MinEnv) (compiled : Emit Atom) (result : Outcome) : Prop :=
  ∀ first (rename : String → String), Function.Injective rename →
  ∀ state : St, state.world.selfExtra = [] → state.world.selfImports = [] →
  ∀ incoming : Metta.Bindings, ClosedValueBindings incoming → LeaRuntimeBindingInvariant incoming →
  ∀ parentBody scope continuation,
    let code := renBy rename (toLeaTTaAtom (compiled first).1)
    (∀ key ∈ code.vars, Metta.Bindings.lookupVal incoming key = none) →
    BodyRun environment state incoming code (toLeaTTaAtom (observation result))
      parentBody scope continuation

/-- Specialization to the actual source-expression compiler, retaining the
source environment, source fuel and exact outcome. -/
def ExpressionExecutes (program : Program) (environment : MinEnv) (sourceFuel : Nat)
    (sourceBindings : Env) (term : Term) (result : Outcome) : Prop :=
  CompiledExecutes environment
    (expression program (sourceBindings.map (fun row => (row.1, MeTTaData.encode row.2)))
      (.grounded (.int sourceFuel)) term) result

/-- Zero source fuel returns exhaustion without inspecting the guest body. -/
theorem expression_zero (program : Program) (environment : MinEnv)
    (groundings : environment.gt = Metta.Builtins.table) (sourceBindings : Env) (term : Term) :
    ExpressionExecutes program environment 0 sourceBindings term .exhausted := by
  intro first rename _ state _ _ incoming stored invariant parentBody scope continuation code _
  refine ⟨state, incoming, 4, 0, rfl, stored, invariant, ?_, ?_⟩
  · intro key _ _ unassigned
    exact unassigned
  · intro fuel _ rest done
    dsimp only [code]
    rw [expression]
    exact renamed_withFuel_zero_enters_handler environment state incoming rename _ first fuel
      parentBody scope continuation rest done groundings stored.hasLoop_false

/-- A source form compiled as a constant return has the complete body run.
This shared case covers literals, missing variables and malformed forms. -/
theorem expression_of_return (program : Program) (environment : MinEnv)
    (groundings : environment.gt = Metta.Builtins.table)
    (sourceBindings : Env) (term : Term) (remaining : Nat) (result : Outcome)
    (emitted : ∀ first, (expression program
        (sourceBindings.map (fun row => (row.1, MeTTaData.encode row.2)))
        (.grounded (.int (remaining + 1))) term first).1 =
      (withFuel (.grounded (.int (remaining + 1)))
        (fun _ => pure (returned (observation result))) first).1) :
    ExpressionExecutes program environment (remaining + 1) sourceBindings term result := by
  intro first rename injective state _ _ incoming stored invariant parentBody scope continuation code fresh
  refine ⟨state, incoming, 9, 0, rfl, stored, invariant, ?_, ?_⟩
  · intro key _ _ unassigned
    exact unassigned
  · intro fuel _ rest done
    have privateRemaining : Metta.instantiate incoming (.var (rename (freshName first))) =
        .var (rename (freshName first)) := by
      apply instantiate_unassigned incoming stored
      intro key member
      have equal : key = rename (freshName first) := by simpa [Metta.Atom.vars] using member
      subst key
      exact fresh _ (expression_remaining_occurs _ _ _ _ _ _)
    have closed := observation_closed result
    have materialized : Metta.instantiate incoming
        (renBy rename (toLeaTTaAtom (observation result))) = toLeaTTaAtom (observation result) := by
      rw [renBy_eq_self_of_vars_nil rename _ closed, Metta.instantiate_of_closed _ _ closed]
    have bounded : UsesBefore (first + 1) (observation result) := by
      intro key occurs
      have member := mem_translated_vars_of_atomOccurs occurs
      rw [closed] at member
      exact False.elim (List.not_mem_nil member)
    dsimp only [code]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [emitted]
    exact renamed_withFuel_return_enters_handler environment state incoming rename injective
      (observation result) (toLeaTTaAtom (observation result)) first remaining fuel
      parentBody scope continuation rest done groundings privateRemaining bounded materialized closed


/-- Variable lookup, including missing-variable refusal, executes literally. -/
theorem expression_variable (program : Program) (environment : MinEnv)
    (groundings : environment.gt = Metta.Builtins.table)
    (sourceBindings : Env) (name : String) (remaining : Nat) :
    ExpressionExecutes program environment (remaining + 1) sourceBindings (.var name)
      (match sourceBindings.lookup name with | some v => .value v | none => .failure) := by
  apply expression_of_return program environment groundings sourceBindings (.var name) remaining
  intro first
  rw [expression_encoded_variable]
  cases sourceBindings.lookup name <;> rfl

theorem expression_symbol (program : Program) (environment : MinEnv)
    (groundings : environment.gt = Metta.Builtins.table)
    (sourceBindings : Env) (name : String) (remaining : Nat) :
    ExpressionExecutes program environment (remaining + 1) sourceBindings (.sym name) (.value (.sym name)) :=
  expression_of_return program environment groundings sourceBindings (.sym name) remaining _ (fun _ => by rw [expression]; rfl)

theorem expression_literal (program : Program) (environment : MinEnv)
    (groundings : environment.gt = Metta.Builtins.table)
    (sourceBindings : Env) (literal : String) (remaining : Nat) :
    ExpressionExecutes program environment (remaining + 1) sourceBindings (.lit literal) (.value (.lit literal)) :=
  expression_of_return program environment groundings sourceBindings (.lit literal) remaining _ (fun _ => by rw [expression]; rfl)

theorem expression_empty (program : Program) (environment : MinEnv)
    (groundings : environment.gt = Metta.Builtins.table)
    (sourceBindings : Env) (remaining : Nat) :
    ExpressionExecutes program environment (remaining + 1) sourceBindings (.expr []) (.value (.expr [])) :=
  expression_of_return program environment groundings sourceBindings (.expr []) remaining _ (fun _ => by rw [expression]; rfl)

theorem expression_nullary (program : Program) (environment : MinEnv)
    (groundings : environment.gt = Metta.Builtins.table)
    (sourceBindings : Env) (name : String) (remaining : Nat) :
    ExpressionExecutes program environment (remaining + 1) sourceBindings
      (.expr [.sym "metta-nullary", .sym name]) (.value (.expr [.sym name])) :=
  expression_of_return program environment groundings sourceBindings _ remaining _ (fun _ => by rw [expression]; rfl)


/-- A compiled operand opens its own function frame and returns to the
waiting caller. Only the ordinary function-return step is added to the
already established body segment. -/
theorem expression_as_operand (program : Program) (environment : MinEnv)
    (sourceFuel : Nat) (sourceBindings : Env) (term : Term) (result : Outcome)
    (run : ExpressionExecutes program environment sourceFuel sourceBindings term result)
    (first : Nat) (rename : String → String) (injective : Function.Injective rename)
    (state : St) (noExtra : state.world.selfExtra = []) (noImports : state.world.selfImports = [])
    (incoming : Metta.Bindings) (stored : ClosedValueBindings incoming)
    (invariant : LeaRuntimeBindingInvariant incoming) (caller : Frame) (continuation : Stack) :
    let body := renBy rename (toLeaTTaAtom (expression program
      (sourceBindings.map (fun row => (row.1, MeTTaData.encode row.2)))
      (.grounded (.int sourceFuel)) term first).1)
    let sourceCall := .expr [.sym "function", body]
    (∀ key ∈ body.vars, Metta.Bindings.lookupVal incoming key = none) →
    ∃ nextState output cost threshold,
      nextState.world = state.world ∧ ClosedValueBindings output ∧
      LeaRuntimeBindingInvariant output ∧
      (∀ key ∈ liveStackVars (caller :: continuation), key ∉ body.vars →
        Metta.Bindings.lookupVal incoming key = none → Metta.Bindings.lookupVal output key = none) ∧
      ∀ fuel, threshold ≤ fuel → ∀ rest done,
        interpretFuel environment (fuel + cost) state
          (⟨atomToStack sourceCall (caller :: continuation), incoming⟩ :: rest) done =
        interpretFuel environment fuel nextState
          (finItem (caller :: continuation) (toLeaTTaAtom (observation result)) output :: rest) done := by
  intro body sourceCall fresh
  obtain ⟨nextState, output, cost, threshold, world, outputClosed, outputInvariant, preserved, execution⟩ :=
    run first rename injective state noExtra noImports incoming stored invariant sourceCall
      (varsCopy (caller :: continuation)) (caller :: continuation) fresh
  have shape : ∃ items, body = .expr items := by
    have embedded := expression_runtime_embedded program
      (sourceBindings.map (fun row => (row.1, MeTTaData.encode row.2)))
      (.grounded (.int sourceFuel)) term first rename
    change isEmbeddedOp body = true at embedded
    cases bodyShape : body with
    | sym => simp [bodyShape, isEmbeddedOp] at embedded
    | var => simp [bodyShape, isEmbeddedOp] at embedded
    | gnd => simp [bodyShape, isEmbeddedOp] at embedded
    | expr items => exact ⟨items, rfl⟩
  refine ⟨nextState, output, cost + 1, threshold, world, outputClosed, outputInvariant, ?_, ?_⟩
  · intro key live absent unassigned
    apply preserved key _ absent unassigned
    exact List.mem_append_right _ live
  · intro fuel enough rest done
    obtain ⟨items, shape⟩ := shape
    have entered := execution (fuel + 1) (by omega) rest done
    have returns : interpretFuel environment (fuel + 1) nextState
        (finItem ({atom := sourceCall, ret := .function, vars := varsCopy (caller :: continuation)} ::
          caller :: continuation) (.expr [.sym "return", toLeaTTaAtom (observation result)]) output :: rest) done =
      interpretFuel environment fuel nextState
        (finItem (caller :: continuation) (toLeaTTaAtom (observation result)) output :: rest) done := by
      apply driver_singleton_step
      · simpa only [Metta.instantiate_of_closed output _ (observation_closed result)] using
          step_function_return environment fuel nextState (caller :: continuation)
            (varsCopy (caller :: continuation)) sourceCall (toLeaTTaAtom (observation result)) output
      · rfl
    have combined := entered.trans returns
    have opener : atomToStack sourceCall (caller :: continuation) =
        atomToStack body ({atom := sourceCall, ret := .function, vars := varsCopy (caller :: continuation)} :: caller :: continuation) := by
      simp only [sourceCall, shape, atomToStack]
    simpa only [show fuel + (cost + 1) = fuel + 1 + cost by omega, opener] using combined

/-- The successful let case composes the bound-expression and body induction
hypotheses. The lexical environment receives the actual bound value; fresh
runtime state is established by the generated binder. -/
theorem expression_let_value (program : Program) (environment : MinEnv)
    (groundings : environment.gt = Metta.Builtins.table)
    (sourceBindings : Env) (name : String) (bound body payload : Term)
    (remaining : Nat) (result : Outcome)
    (boundRun : ExpressionExecutes program environment remaining sourceBindings bound (.value payload))
    (bodyRun : ExpressionExecutes program environment remaining ((name, payload) :: sourceBindings) body result) :
    ExpressionExecutes program environment (remaining + 1) sourceBindings
      (.expr [.sym "let", .var name, bound, body]) result := by
  intro first rename injective state noExtra noImports incoming stored invariant parentBody scope continuation code fresh
  dsimp only [code] at fresh ⊢
  simp only [Nat.cast_add, Nat.cast_one] at fresh ⊢
  let names := sourceBindings.map (fun row => (row.1, MeTTaData.encode row.2))
  let source := (expression program names (.grounded (.int (remaining + 1)))
    (.expr [.sym "let", .var name, bound, body]) first).1
  let target := Atom.var (freshName (first + 1))
  let assigned := expression program names (.grounded (.int remaining)) bound (first + 2)
  let tail := expression program ((name, target) :: names) (.grounded (.int remaining)) body assigned.2
  let parent : Frame := {atom := parentBody, ret := .function, vars := scope}
  let sourceCall := renBy rename (toLeaTTaAtom (call "function" [assigned.1]))
  let template := renBy rename (toLeaTTaAtom (resultBranches (.var (freshName tail.2)) target tail.1))
  let recipient : Frame :=
    {atom := .expr [.sym "chain", sourceCall, .var (rename (freshName tail.2)), template],
     ret := .chain, vars := chainFrameVars (parent :: continuation) sourceCall template}
  have namesData : ∀ entry ∈ names, MeTTaData.DataAtom entry.2 := by
    intro entry member
    obtain ⟨row, _, rfl⟩ := List.mem_map.mp member
    exact MeTTaData.encode_data row.2
  have operandSubset : ∀ key ∈ (renBy rename (toLeaTTaAtom assigned.1)).vars,
      key ∈ (renBy rename (toLeaTTaAtom source)).vars := by
    intro key member
    apply let_core_variables_in_source program names name bound body first remaining namesData
      rename injective key
    change key ∈ (renBy rename (toLeaTTaAtom (call "chain" [call "function" [assigned.1], _, _]))).vars
    simp only [call, toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_cons, List.map_nil,
      Metta.Atom.vars, List.flatten_cons, List.flatten_nil, List.nil_append,
      List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil]
    tauto
  obtain ⟨middleState, middle, operandCost, operandThreshold, middleWorld, middleStored,
      middleInvariant, operandPreserved, operandExecution⟩ :=
    expression_as_operand program environment remaining sourceBindings bound (.value payload) boundRun
      (first + 2) rename injective state noExtra noImports incoming stored invariant recipient
      (parent :: continuation) (fun key member => fresh key (operandSubset key member))
  let output := Metta.Bindings.addValRaw middle (rename (freshName (first + 1)))
    (toLeaTTaAtom (MeTTaData.encode payload))
  let entered := renBy rename (toLeaTTaAtom (expression program
    (((name, payload) :: sourceBindings).map (fun row => (row.1, MeTTaData.encode row.2)))
    (.grounded (.int remaining)) body assigned.2).1)
  have prefixRun (fuel : Nat) (enough : operandThreshold ≤ fuel)
      (rest : List Item) (done : List (Metta.Atom × Metta.Bindings)) :=
    let_value_enters_continuation program sourceBindings name bound body payload first remaining
      operandCost fuel environment state middleState incoming middle rename injective
      stored middleStored middleInvariant groundings parentBody scope continuation rest done
      fresh operandPreserved (by simpa only [recipient, parent, sourceCall, template,
        target, tail, assigned, names, call, toLeaTTaAtom, toLeaTTaAtoms, renBy,
        List.map_cons, List.map_nil, observation] using operandExecution (fuel + 4) (by omega) rest done)
  obtain ⟨outputStored, outputInvariant, enteredSubset, enteredPrivate, callerPreserved, _⟩ :=
    prefixRun operandThreshold le_rfl [] []
  obtain ⟨finalState, finalBindings, bodyCost, bodyThreshold, finalWorld, finalStored,
      finalInvariant, bodyPreserved, bodyExecution⟩ :=
    bodyRun assigned.2 rename injective middleState (by rw [middleWorld]; exact noExtra)
      (by rw [middleWorld]; exact noImports) output outputStored outputInvariant
      parentBody scope continuation enteredPrivate
  refine ⟨finalState, finalBindings, bodyCost + 12 + operandCost,
    max operandThreshold bodyThreshold, finalWorld.trans middleWorld,
    finalStored, finalInvariant, ?_, ?_⟩
  · intro key live absent unassigned
    exact bodyPreserved key live (fun member => absent (enteredSubset key member))
      (callerPreserved key live absent unassigned)
  · intro fuel enough rest done
    have firstRun := (prefixRun (fuel + bodyCost) (by omega) rest done).2.2.2.2.2
    have lastRun := bodyExecution fuel (by omega) rest done
    have combined := firstRun.trans lastRun
    simpa only [show fuel + bodyCost + 12 + operandCost =
      fuel + (bodyCost + 12 + operandCost) by omega] using combined

/-- A stopped bound computation determines the whole let outcome. The body
is not evaluated, and refusal remains distinct from source exhaustion. -/
theorem expression_let_stopped (program : Program) (environment : MinEnv)
    (groundings : environment.gt = Metta.Builtins.table)
    (sourceBindings : Env) (name : String) (bound body : Term)
    (remaining : Nat) (result : Outcome) (stopped : result = .failure ∨ result = .exhausted)
    (boundRun : ExpressionExecutes program environment remaining sourceBindings bound result) :
    ExpressionExecutes program environment (remaining + 1) sourceBindings
      (.expr [.sym "let", .var name, bound, body]) result := by
  obtain ⟨marker, markers, observed⟩ : ∃ marker : String,
      (marker = "nik:Failure" ∨ marker = "nik:Exhausted") ∧ observation result = .symbol marker := by
    rcases stopped with rfl | rfl
    · exact ⟨"nik:Failure", Or.inl rfl, rfl⟩
    · exact ⟨"nik:Exhausted", Or.inr rfl, rfl⟩
  intro first rename injective state noExtra noImports incoming stored invariant parentBody scope continuation code fresh
  dsimp only [code] at fresh ⊢
  simp only [Nat.cast_add, Nat.cast_one] at fresh ⊢
  let names := sourceBindings.map (fun row => (row.1, MeTTaData.encode row.2))
  let source := (expression program names (.grounded (.int (remaining + 1)))
    (.expr [.sym "let", .var name, bound, body]) first).1
  let target := Atom.var (freshName (first + 1))
  let assigned := expression program names (.grounded (.int remaining)) bound (first + 2)
  let tail := expression program ((name, target) :: names) (.grounded (.int remaining)) body assigned.2
  let parent : Frame := {atom := parentBody, ret := .function, vars := scope}
  let sourceCall := renBy rename (toLeaTTaAtom (call "function" [assigned.1]))
  let template := renBy rename (toLeaTTaAtom (resultBranches (.var (freshName tail.2)) target tail.1))
  let recipient : Frame :=
    {atom := .expr [.sym "chain", sourceCall, .var (rename (freshName tail.2)), template],
     ret := .chain, vars := chainFrameVars (parent :: continuation) sourceCall template}
  have namesData : ∀ entry ∈ names, MeTTaData.DataAtom entry.2 := by
    intro entry member
    obtain ⟨row, _, rfl⟩ := List.mem_map.mp member
    exact MeTTaData.encode_data row.2
  have operandSubset : ∀ key ∈ (renBy rename (toLeaTTaAtom assigned.1)).vars,
      key ∈ (renBy rename (toLeaTTaAtom source)).vars := by
    intro key member
    apply let_core_variables_in_source program names name bound body first remaining namesData
      rename injective key
    change key ∈ (renBy rename (toLeaTTaAtom (call "chain" [call "function" [assigned.1], _, _]))).vars
    simp only [call, toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_cons, List.map_nil,
      Metta.Atom.vars, List.flatten_cons, List.flatten_nil, List.nil_append,
      List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil]
    tauto
  obtain ⟨nextState, output, operandCost, operandThreshold, world, outputStored,
      outputInvariant, operandPreserved, operandExecution⟩ :=
    expression_as_operand program environment remaining sourceBindings bound result boundRun
      (first + 2) rename injective state noExtra noImports incoming stored invariant recipient
      (parent :: continuation) (fun key member => fresh key (operandSubset key member))
  let steps := if marker = "nik:Failure" then 3 else 5
  refine ⟨nextState, output, steps + 10 + operandCost, operandThreshold, world,
    outputStored, outputInvariant, ?_, ?_⟩
  · intro key live absent unassigned
    apply operandPreserved key (List.mem_append_right _ live)
      (fun member => absent (operandSubset key member)) unassigned
  · intro fuel enough rest done
    have run := let_stopped_execution_in_frame program names name bound body first remaining
      operandCost fuel environment state nextState incoming output rename injective namesData stored
      groundings marker markers outputStored.hasLoop_false parentBody scope continuation rest done
      fresh (by simpa only [observed, recipient, parent, sourceCall, template, target, tail,
        assigned, names, steps, call, toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_cons, List.map_nil] using
        operandExecution (fuel + steps + 2) (by omega) rest done)
    simpa only [observed, toLeaTTaAtom, names, steps, Nat.add_assoc] using run


/-- The complete let case of the source-fuel induction, with the source
outcome computed by the existing evaluator. -/
theorem expression_let (program : Program) (host : Host) (environment : MinEnv)
    (groundings : environment.gt = Metta.Builtins.table)
    (sourceBindings : Env) (name : String) (bound body : Term) (remaining : Nat)
    (boundRun : ExpressionExecutes program environment remaining sourceBindings bound
      (eval program host remaining sourceBindings bound))
    (bodyRun : ∀ payload, ExpressionExecutes program environment remaining
      ((name, payload) :: sourceBindings) body
      (eval program host remaining ((name, payload) :: sourceBindings) body)) :
    ExpressionExecutes program environment (remaining + 1) sourceBindings
      (.expr [.sym "let", .var name, bound, body])
      (eval program host (remaining + 1) sourceBindings
        (.expr [.sym "let", .var name, bound, body])) := by
  rw [eval, evalStep]
  cases outcome : eval program host remaining sourceBindings bound with
  | value payload =>
    exact expression_let_value program environment groundings sourceBindings name bound body payload
      remaining _ (by simpa only [outcome] using boundRun) (bodyRun payload)
  | failure =>
    exact expression_let_stopped program environment groundings sourceBindings name bound body
      remaining .failure (Or.inl rfl) (by simpa only [outcome] using boundRun)
  | exhausted =>
    exact expression_let_stopped program environment groundings sourceBindings name bound body
      remaining .exhausted (Or.inr rfl) (by simpa only [outcome] using boundRun)

/-- Arbitrary guest payloads, including variable-shaped data, pass through
lexical binding without becoming target variables or executable code. -/
theorem arbitrary_payload_let_control (program : Program) (environment : MinEnv)
    (groundings : environment.gt = Metta.Builtins.table) (payload : Term) :
    ExpressionExecutes program environment 2 [("outer", payload)]
      (.expr [.sym "let", .var "inner", .var "outer", .var "inner"]) (.value payload) := by
  apply expression_let_value program environment groundings [("outer", payload)] "inner"
    (.var "outer") (.var "inner") payload 1 (.value payload)
  · simpa [Env.lookup] using expression_variable program environment groundings
      [("outer", payload)] "outer" 0
  · simpa [Env.lookup] using expression_variable program environment groundings
      [("inner", payload), ("outer", payload)] "inner" 0

/-- A new lexical declaration shadows the old source value. -/
theorem lexical_shadowing_control (program : Program) (environment : MinEnv)
    (groundings : environment.gt = Metta.Builtins.table) (old : Term) :
    ExpressionExecutes program environment 2 [("x", old)]
      (.expr [.sym "let", .var "x", .sym "new", .var "x"]) (.value (.sym "new")) := by
  apply expression_let_value program environment groundings [("x", old)] "x"
    (.sym "new") (.var "x") (.sym "new") 1 (.value (.sym "new"))
  · exact expression_symbol program environment groundings [("x", old)] "new" 0
  · simpa [Env.lookup] using expression_variable program environment groundings
      [("x", .sym "new"), ("x", old)] "x" 0

/-- A successful-looking body does not hide a missing bound input. -/
theorem bound_refusal_control (program : Program) (environment : MinEnv)
    (groundings : environment.gt = Metta.Builtins.table) :
    ExpressionExecutes program environment 2 []
      (.expr [.sym "let", .var "x", .var "missing", .sym "ok"]) .failure := by
  apply expression_let_stopped program environment groundings [] "x" (.var "missing")
    (.sym "ok") 1 .failure (Or.inl rfl)
  simpa [Env.lookup] using expression_variable program environment groundings [] "missing" 0

/-- Source exhaustion prevents the bound expression and body from running. -/
theorem bound_exhaustion_control (program : Program) (environment : MinEnv)
    (groundings : environment.gt = Metta.Builtins.table) :
    ExpressionExecutes program environment 1 []
      (.expr [.sym "let", .var "x", .sym "value", .sym "ok"]) .exhausted :=
  expression_let_stopped program environment groundings [] "x" (.sym "value") (.sym "ok")
    0 .exhausted (Or.inr rfl) (expression_zero program environment groundings [] (.sym "value"))

/-- A completed bound value does not excuse a refusal in the body. -/
theorem body_refusal_control (program : Program) (environment : MinEnv)
    (groundings : environment.gt = Metta.Builtins.table) :
    ExpressionExecutes program environment 2 []
      (.expr [.sym "let", .var "x", .sym "value", .var "missing"]) .failure := by
  apply expression_let_value program environment groundings [] "x" (.sym "value")
    (.var "missing") (.sym "value") 1 .failure
  · exact expression_symbol program environment groundings [] "value" 0
  · simpa [Env.lookup] using expression_variable program environment groundings
      [("x", .sym "value")] "missing" 0

/-- The observation encoding keeps logical refusal and source exhaustion distinct. -/
theorem refusal_is_not_exhaustion : observation .failure ≠ observation .exhausted := by
  intro same
  have impossible := observation_injective same
  cases impossible

end Execution
end Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit
