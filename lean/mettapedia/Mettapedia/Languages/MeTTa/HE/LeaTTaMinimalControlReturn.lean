import Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalControlContinuation

/-!
# Return and sequencing inside an existing caller

The laws retain arbitrary caller frames, queued work and previous answers.
Returned operands are materialized by the existing interpreter. No assumption
about a caller's eventual result is needed to resume that caller.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalControlExecution

open Metta Metta.Minimal FuelConvergenceInterpreter

/-- A completed frame no longer uses its variable-retention list. The caller and
all scheduling observations are unchanged. -/
theorem finished_frame_scope_irrelevant (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (result : Atom) (scope : List VarName)
    (parent : Frame) (continuation : Stack) (fuel : Nat) (rest : List Item)
    (done : List (Atom × Metta.Bindings)) :
    interpretFuel environment fuel state
      (⟨{ atom := result, fin := true, vars := scope } :: parent :: continuation,
        bindings⟩ :: rest) done =
    interpretFuel environment fuel state
      (finItem (parent :: continuation) result bindings :: rest) done := by
  cases fuel with
  | zero =>
    rw [FuelConvergenceInterpreter.interpretFuel_zero_cons,
      FuelConvergenceInterpreter.interpretFuel_zero_cons]
    rfl
  | succ fuel =>
    rw [interpretFuel_succ, interpretFuel_succ]
    simp only [interpretStack1, finItem, if_true]

/-- A return becomes ready for the enclosing function handler, including when
that function has no caller. -/
theorem return_enters_handler (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (parentBody value : Atom) (scope : List VarName)
    (continuation : Stack) (fuel : Nat) (rest : List Item)
    (done : List (Atom × Metta.Bindings)) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    interpretFuel environment (fuel + 1) state
      (⟨atomToStack (.expr [.sym "return", value]) (parent :: continuation), bindings⟩ :: rest) done =
    interpretFuel environment fuel state
      (finItem (parent :: continuation) (.expr [.sym "return", value]) bindings :: rest) done := by
  intro parent
  let next : Item := ⟨{ atom := .expr [.sym "return", value], fin := true, vars := scope } ::
    parent :: continuation, bindings⟩
  have step : interpretStack1 environment fuel state
      ⟨atomToStack (.expr [.sym "return", value]) (parent :: continuation), bindings⟩ =
      ([next], state) := by
    simp [interpretStack1, atomToStack, parent, varsCopy, isEmbeddedOp, next]
  rw [driver_singleton_step environment fuel state state _ next rest done step (by rfl)]
  exact finished_frame_scope_irrelevant environment state bindings _ scope parent continuation
    fuel rest done

/-- The outermost function return becomes exactly one public result. -/
theorem selected_closed_return_finishes (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (parentBody value : Atom) (scope : List VarName)
    (fuel : Nat) (closed : value.vars = []) (visible : (value != emptyA) = true) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    interpretFuel environment (fuel + 1) state
      [finItem [parent] (.expr [.sym "return", value]) bindings] [] =
      ([(value, bindings)], state) := by
  intro parent
  have step := step_function_return environment fuel state [] scope parentBody value bindings
  rw [instantiate_of_closed bindings value closed] at step
  rw [interpretFuel_succ_of environment fuel state state _ [] _ [] step]
  change interpretFuel environment fuel state [] [(instantiate bindings value, bindings)] = _
  rw [FuelConvergenceInterpreter.interpretFuel_nil, instantiate_of_closed bindings value closed]
  simp [visible]

/-- An exhausted recursive computation returns to its caller through the
same guard as a top-level request. It preserves bindings, runtime state,
queued work and accumulated answers, without evaluating the fallback. -/
theorem integer_zero_guard_to_caller_in_frame (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (name marker : String) (otherwise : Atom) (fuel : Nat)
    (parentBody : Atom) (scope : List VarName) (caller : Frame) (continuation : Stack) (rest : List Item)
    (done : List (Atom × Metta.Bindings))
    (groundings : environment.gt = Builtins.table)
    (acyclic : bindings.hasLoop = false) :
    let equality := Atom.expr [.sym "eval", .expr [.sym "==", .gnd (.int 0), .gnd (.int 0)]]
    let template := Atom.expr [.sym "unify", .var name, .gnd (.bool true),
      .expr [.sym "return", .sym marker], otherwise]
    let body := Atom.expr [.sym "chain", equality, .var name, template]
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    interpretFuel environment (fuel + 5) state
        (⟨atomToStack body (parent :: caller :: continuation),
          bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (finItem (caller :: continuation) (.sym marker) bindings :: rest) done := by
  intro equality template body parent
  let selected := finItem (parent :: caller :: continuation)
    (.expr [.sym "return", .sym marker]) bindings
  rw [show fuel + 5 = (fuel + 1) + 4 by omega,
    integer_zero_guard_selects_in_frame environment state bindings name marker otherwise
      (fuel + 1) parent (caller :: continuation) rest done groundings acyclic]
  change interpretFuel environment (fuel + 1) state (selected :: rest) done = _
  apply driver_singleton_step
  · simpa [selected, parent, instantiate, Bindings.resolveAtom] using
      step_function_return environment fuel state (caller :: continuation)
        scope parentBody
        (.sym marker) bindings
  · rfl

/-- Opening a recursive function specializes the retained-frame exhaustion
law; the fallback is still never evaluated. -/
theorem integer_zero_guard_to_caller (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (name marker : String) (otherwise : Atom) (fuel : Nat)
    (caller : Frame) (continuation : Stack) (rest : List Item)
    (done : List (Atom × Metta.Bindings))
    (groundings : environment.gt = Builtins.table)
    (acyclic : bindings.hasLoop = false) :
    let equality := Atom.expr [.sym "eval", .expr [.sym "==", .gnd (.int 0), .gnd (.int 0)]]
    let template := Atom.expr [.sym "unify", .var name, .gnd (.bool true),
      .expr [.sym "return", .sym marker], otherwise]
    let body := Atom.expr [.sym "chain", equality, .var name, template]
    interpretFuel environment (fuel + 5) state
        (⟨atomToStack (.expr [.sym "function", body]) (caller :: continuation),
          bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (finItem (caller :: continuation) (.sym marker) bindings :: rest) done := by
  intro equality template body
  simpa only [body, equality, template, atomToStack] using
    integer_zero_guard_to_caller_in_frame environment state bindings name marker otherwise fuel
      (.expr [.sym "function", body]) (varsCopy (caller :: continuation)) caller continuation
      rest done groundings acyclic

/-- Returning from a nested function preserves its caller and the rest of the
driver. The returned atom is exactly the runtime's instantiated operand. -/
theorem return_to_caller (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (parentBody value : Atom) (scope : List VarName)
    (caller : Frame) (continuation : Stack) (fuel : Nat)
    (rest : List Item) (done : List (Atom × Metta.Bindings)) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    interpretFuel environment (fuel + 2) state
        (⟨atomToStack (.expr [.sym "return", value])
          (parent :: caller :: continuation), bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (finItem (caller :: continuation) (instantiate bindings value) bindings :: rest) done := by
  intro parent
  rw [show fuel + 2 = (fuel + 1) + 1 by omega,
    return_enters_handler environment state bindings parentBody value scope
      (caller :: continuation) (fuel + 1) rest done]
  exact driver_singleton_step environment fuel state state _ _ rest done
    (step_function_return environment fuel state (caller :: continuation) scope parentBody
      value bindings) (by rfl)

/-- A finished argument enters its actual `chain` continuation. Binding
resolution precedes substitution, and every surrounding frame is retained. -/
theorem chain_result_enters (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (source result template : Atom) (name : VarName)
    (scope : List VarName) (parent : Frame) (continuation : Stack) (fuel : Nat)
    (rest : List Item) (done : List (Atom × Metta.Bindings)) :
    let caller : Frame := { atom := .expr [.sym "chain", source, .var name, template], ret := .chain, vars := scope }
    interpretFuel environment (fuel + 2) state
        (finItem (caller :: parent :: continuation) result bindings :: rest) done =
      interpretFuel environment fuel state
        (⟨atomToStack (Subst.apply [(name, instantiate bindings result)] template)
          (parent :: continuation), bindings⟩ :: rest) done := by
  intro caller
  let middle : Item := ⟨{ atom := .expr [.sym "chain", instantiate bindings result,
    .var name, template], ret := .chain, vars := scope } :: parent :: continuation, bindings⟩
  have firstStep (budget : Nat) : interpretStack1 environment budget state
      (finItem (caller :: parent :: continuation) result bindings) = ([middle], state) := by
    exact step_chain_result environment budget state (parent :: continuation) scope
      source result template name bindings
  have lastStep (budget : Nat) : interpretStack1 environment budget state middle =
      ([⟨atomToStack (Subst.apply [(name, instantiate bindings result)] template)
        (parent :: continuation), bindings⟩], state) := by
    exact step_chain_apply environment budget state (parent :: continuation) scope
      (instantiate bindings result) template name bindings
  rw [driver_singleton_step environment (fuel + 1) state state _ middle rest done
    (firstStep _) (by rfl)]
  exact driver_singleton_step environment fuel state state middle _ rest done
    (lastStep _) (atomToStack_pending _ _ _ _)

/-- A closed return from a nested function enters the caller's template.
This composes the function and sequencing laws without a new execution model. -/
theorem closed_return_chain_enters (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (parentBody value source template : Atom)
    (name : VarName) (functionScope chainScope : List VarName)
    (parent : Frame) (continuation : Stack) (fuel : Nat)
    (rest : List Item) (done : List (Atom × Metta.Bindings))
    (closed : value.vars = []) :
    let function : Frame := { atom := parentBody, ret := .function, vars := functionScope }
    let caller : Frame := { atom := .expr [.sym "chain", source, .var name, template], ret := .chain, vars := chainScope }
    interpretFuel environment (fuel + 4) state
        (⟨atomToStack (.expr [.sym "return", value])
          (function :: caller :: parent :: continuation), bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (⟨atomToStack (Subst.apply [(name, value)] template)
          (parent :: continuation), bindings⟩ :: rest) done := by
  intro function caller
  rw [show fuel + 4 = (fuel + 2) + 2 by omega,
    return_to_caller environment state bindings parentBody value functionScope caller
      (parent :: continuation) (fuel + 2) rest done,
    Metta.instantiate_of_closed bindings value closed]
  rw [chain_result_enters environment state bindings source value template name chainScope
    parent continuation fuel rest done, Metta.instantiate_of_closed bindings value closed]

end Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalControlExecution
