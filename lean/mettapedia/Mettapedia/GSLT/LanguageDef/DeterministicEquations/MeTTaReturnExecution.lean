import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaFuelExecution
import Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalControlReturn

/-!
# Generated returns in a caller's continuation

A compiled operand may refer to data through the incoming binding frame.
Materializing that operand and executing the generated return preserves the
caller, queued work and previous answers. These laws compose with argument
sequencing rather than requiring the expression to be a whole program.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalControlExecution
open Mettapedia.Languages.MeTTa.HE.CanonAbsorbsFreshening
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge
open Metta.Minimal

/-- The body allocation bound of a return follows from the operand's scope. -/
theorem return_body_bound (result : Atom) (first : Nat)
    (bounded : UsesBefore (first + 1) result) :
    first + 1 ≤ ((pure (returned result) : Emit Atom) (first + 1)).2 ∧
      UsesBefore ((pure (returned result) : Emit Atom) (first + 1)).2
        ((pure (returned result) : Emit Atom) (first + 1)).1 := by
  change first + 1 ≤ first + 1 ∧ UsesBefore (first + 1) (returned result)
  simpa [returned] using bounded

/-- Runtime binding materialization commutes with the generated return form. -/
theorem instantiate_returned (bindings : Metta.Bindings) (result : Atom) :
    Metta.instantiate bindings (toLeaTTaAtom (returned result)) =
      .expr [.sym "return", Metta.instantiate bindings (toLeaTTaAtom result)] := by
  simp [returned, call, toLeaTTaAtom, toLeaTTaAtoms,
    Metta.instantiate, Metta.Bindings.resolveAtom]

/-- A generated positive-fuel return reaches its function handler on any stack.
The final public/caller return is a separate interpreter step. -/
theorem renamed_withFuel_return_enters_handler (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (rename : String → String) (injective : Function.Injective rename)
    (result : Atom) (actual : Metta.Atom) (first remaining fuel : Nat)
    (parentBody : Metta.Atom) (scope : List Metta.VarName) (continuation : Stack)
    (rest : List Item) (done : List (Metta.Atom × Metta.Bindings))
    (groundings : environment.gt = Metta.Builtins.table)
    (privateRemaining : Metta.instantiate bindings (.var (rename (freshName first))) =
      .var (rename (freshName first)))
    (bounded : UsesBefore (first + 1) result)
    (materialized : Metta.instantiate bindings (renBy rename (toLeaTTaAtom result)) = actual)
    (closed : actual.vars = []) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    interpretFuel environment (fuel + 9) state
      (⟨atomToStack (renBy rename (toLeaTTaAtom (withFuel (.grounded (.int (remaining + 1)))
        (fun _ => pure (returned result)) first).1)) (parent :: continuation), bindings⟩ :: rest) done =
    interpretFuel environment fuel state
      (finItem (parent :: continuation) (.expr [.sym "return", actual]) bindings :: rest) done := by
  intro parent
  have computation := renamed_withFuel_positive_execution_in_frame environment state bindings
    rename injective (fun _ => pure (returned result)) first remaining (fuel + 1)
    parentBody scope continuation rest done groundings privateRemaining
    (return_body_bound result first bounded)
  rw [show fuel + 9 = (fuel + 1) + 8 by omega, computation]
  rw [show ((pure (returned result) : Emit Atom) (first + 1)).1 = returned result from rfl]
  have resolved : Metta.instantiate bindings (renBy rename (toLeaTTaAtom (returned result))) =
      .expr [.sym "return", actual] := by
    simpa only [returned, call, toLeaTTaAtom, toLeaTTaAtoms, renBy,
      List.map_cons, List.map_nil, Metta.instantiate, Metta.Bindings.resolveAtom] using
      congrArg (fun value => Metta.Atom.expr [.sym "return", value]) materialized
  rw [resolved, Metta.Subst.apply_of_closed _ _ (by simp [Metta.Atom.vars, closed])]
  exact return_enters_handler environment state bindings parentBody actual scope continuation
    fuel rest done

/-- A freshly renamed generated return materializes its payload and resumes
its caller. The renaming is the same one applied to the enclosing equation;
only local scope and binding facts are required. -/
theorem renamed_withFuel_return_to_caller_in_frame (environment : Metta.Minimal.MinEnv)
    (state : Metta.Minimal.St) (bindings : Metta.Bindings)
    (rename : String → String) (injective : Function.Injective rename)
    (result : Atom) (actual : Metta.Atom) (first remaining fuel : Nat)
    (parentBody : Metta.Atom) (scope : List Metta.VarName)
    (caller : Metta.Minimal.Frame) (continuation : Metta.Minimal.Stack)
    (rest : List Metta.Minimal.Item) (done : List (Metta.Atom × Metta.Bindings))
    (groundings : environment.gt = Metta.Builtins.table)
    (privateRemaining : Metta.instantiate bindings (.var (rename (freshName first))) =
      .var (rename (freshName first)))
    (bounded : UsesBefore (first + 1) result)
    (materialized : Metta.instantiate bindings (renBy rename (toLeaTTaAtom result)) = actual)
    (closed : actual.vars = []) :
    let parent : Metta.Minimal.Frame := { atom := parentBody, ret := .function, vars := scope }
    Metta.Minimal.interpretFuel environment (fuel + 10) state
        (⟨Metta.Minimal.atomToStack (renBy rename (toLeaTTaAtom
          (withFuel (.grounded (.int (remaining + 1)))
            (fun _ => pure (returned result)) first).1))
          (parent :: caller :: continuation), bindings⟩ :: rest) done =
      Metta.Minimal.interpretFuel environment fuel state
        (Metta.Minimal.finItem (caller :: continuation) actual bindings :: rest) done := by
  intro parent
  rw [show fuel + 10 = (fuel + 1) + 9 by omega,
    renamed_withFuel_return_enters_handler environment state bindings rename injective
      result actual first remaining (fuel + 1) parentBody scope (caller :: continuation)
      rest done groundings privateRemaining bounded materialized closed]
  apply driver_singleton_step
  · simpa only [Metta.instantiate_of_closed bindings actual closed] using
      step_function_return environment fuel state (caller :: continuation) scope parentBody
        actual bindings
  · rfl

/-- The return law also applies when this call opens its own function frame. -/
theorem renamed_withFuel_return_to_caller (environment : Metta.Minimal.MinEnv)
    (state : Metta.Minimal.St) (bindings : Metta.Bindings)
    (rename : String → String) (injective : Function.Injective rename)
    (result : Atom) (actual : Metta.Atom) (first remaining fuel : Nat)
    (caller : Metta.Minimal.Frame) (continuation : Metta.Minimal.Stack)
    (rest : List Metta.Minimal.Item) (done : List (Metta.Atom × Metta.Bindings))
    (groundings : environment.gt = Metta.Builtins.table)
    (privateRemaining : Metta.instantiate bindings (.var (rename (freshName first))) =
      .var (rename (freshName first)))
    (bounded : UsesBefore (first + 1) result)
    (materialized : Metta.instantiate bindings (renBy rename (toLeaTTaAtom result)) = actual)
    (closed : actual.vars = []) :
    Metta.Minimal.interpretFuel environment (fuel + 10) state
        (⟨Metta.Minimal.atomToStack (renBy rename (toLeaTTaAtom (call "function"
          [(withFuel (.grounded (.int (remaining + 1)))
            (fun _ => pure (returned result)) first).1])))
          (caller :: continuation), bindings⟩ :: rest) done =
      Metta.Minimal.interpretFuel environment fuel state
        (Metta.Minimal.finItem (caller :: continuation) actual bindings :: rest) done := by
  let body := renBy rename (toLeaTTaAtom
    (withFuel (.grounded (.int (remaining + 1))) (fun _ => pure (returned result)) first).1)
  have shape : ∃ items, body = .expr items := by
    change ∃ items, renBy rename (toLeaTTaAtom (call "chain" [_, _, _])) = .expr items
    simp only [call, toLeaTTaAtom, renBy]
    exact ⟨_, rfl⟩
  obtain ⟨items, shape⟩ := shape
  dsimp only [body] at shape
  simpa only [call, toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_cons, List.map_nil,
    body, shape, Metta.Minimal.atomToStack] using
    renamed_withFuel_return_to_caller_in_frame environment state bindings rename injective
      result actual first remaining fuel (.expr [.sym "function", body])
      (Metta.Minimal.varsCopy (caller :: continuation)) caller continuation rest done
      groundings privateRemaining bounded materialized closed

/-- A generated positive-fuel return resumes an arbitrary caller with its
materialized data. Freshness and input resolution are local syntax/binding
invariants; no premise assumes any execution result. -/
theorem withFuel_return_to_caller (environment : Metta.Minimal.MinEnv)
    (state : Metta.Minimal.St) (bindings : Metta.Bindings)
    (result : Atom) (actual : Metta.Atom) (first remaining fuel : Nat)
    (caller : Metta.Minimal.Frame) (continuation : Metta.Minimal.Stack)
    (rest : List Metta.Minimal.Item) (done : List (Metta.Atom × Metta.Bindings))
    (groundings : environment.gt = Metta.Builtins.table)
    (privateRemaining : Metta.instantiate bindings (.var (freshName first)) =
      .var (freshName first))
    (bounded : UsesBefore (first + 1) result)
    (materialized : Metta.instantiate bindings (toLeaTTaAtom result) = actual)
    (closed : actual.vars = []) :
    Metta.Minimal.interpretFuel environment (fuel + 10) state
        (⟨Metta.Minimal.atomToStack (toLeaTTaAtom (call "function"
          [(withFuel (.grounded (.int (remaining + 1)))
            (fun _ => pure (returned result)) first).1]))
          (caller :: continuation), bindings⟩ :: rest) done =
      Metta.Minimal.interpretFuel environment fuel state
        (Metta.Minimal.finItem (caller :: continuation) actual bindings :: rest) done := by
  have identity (atom : Metta.Atom) : renBy id atom = atom := by
    change renBy (applyRen []) atom = atom
    rw [← renameVars_eq_renBy]
    exact Metta.renameVars_nil atom
  simpa only [identity, id_eq] using
    renamed_withFuel_return_to_caller environment state bindings id (fun _ _ same => same)
      result actual first remaining fuel caller continuation rest done groundings privateRemaining
      bounded (by rwa [identity]) closed

/-- A compiled return used as a `chain` operand enters the caller's template
with exactly the returned data substituted. The caller can itself be nested. -/
theorem withFuel_return_chain_enters (environment : Metta.Minimal.MinEnv)
    (state : Metta.Minimal.St) (bindings : Metta.Bindings)
    (result : Atom) (actual source template : Metta.Atom) (name : Metta.VarName)
    (scope : List Metta.VarName) (first remaining fuel : Nat)
    (parent : Metta.Minimal.Frame) (continuation : Metta.Minimal.Stack)
    (rest : List Metta.Minimal.Item) (done : List (Metta.Atom × Metta.Bindings))
    (groundings : environment.gt = Metta.Builtins.table)
    (privateRemaining : Metta.instantiate bindings (.var (freshName first)) =
      .var (freshName first))
    (bounded : UsesBefore (first + 1) result)
    (materialized : Metta.instantiate bindings (toLeaTTaAtom result) = actual)
    (closed : actual.vars = []) :
    let caller : Metta.Minimal.Frame := { atom := .expr [.sym "chain", source, .var name, template], ret := .chain, vars := scope }
    Metta.Minimal.interpretFuel environment (fuel + 12) state
        (⟨Metta.Minimal.atomToStack (toLeaTTaAtom (call "function"
          [(withFuel (.grounded (.int (remaining + 1)))
            (fun _ => pure (returned result)) first).1]))
          (caller :: parent :: continuation), bindings⟩ :: rest) done =
      Metta.Minimal.interpretFuel environment fuel state
        (⟨Metta.Minimal.atomToStack (Metta.Subst.apply [(name, actual)] template)
          (parent :: continuation), bindings⟩ :: rest) done := by
  intro caller
  rw [show fuel + 12 = (fuel + 2) + 10 by omega,
    withFuel_return_to_caller environment state bindings result actual first remaining
      (fuel + 2) caller (parent :: continuation) rest done groundings privateRemaining
      bounded materialized closed,
    chain_result_enters environment state bindings source actual template name scope parent
      continuation fuel rest done, Metta.instantiate_of_closed bindings actual closed]

/-- A found source variable reads the data in its actual target binding frame.
It returns through its caller without evaluating that data as an instruction. -/
theorem expression_variable_to_caller (program : Program) (names : Names)
    (name sourceName : String) (target : Atom)
    (found : names.find? (fun entry => entry.1 == name) = some (sourceName, target))
    (environment : Metta.Minimal.MinEnv) (state : Metta.Minimal.St)
    (bindings : Metta.Bindings) (payload : Term) (first remaining fuel : Nat)
    (caller : Metta.Minimal.Frame) (continuation : Metta.Minimal.Stack)
    (rest : List Metta.Minimal.Item) (done : List (Metta.Atom × Metta.Bindings))
    (groundings : environment.gt = Metta.Builtins.table)
    (privateRemaining : Metta.instantiate bindings (.var (freshName first)) =
      .var (freshName first))
    (bounded : UsesBefore first target)
    (materialized : Metta.instantiate bindings (toLeaTTaAtom target) =
      toLeaTTaAtom (MeTTaData.encode payload)) :
    Metta.Minimal.interpretFuel environment (fuel + 10) state
        (⟨Metta.Minimal.atomToStack (toLeaTTaAtom (call "function"
          [(expression program names (.grounded (.int (remaining + 1)))
            (.var name) first).1])) (caller :: continuation), bindings⟩ :: rest) done =
      Metta.Minimal.interpretFuel environment fuel state
        (Metta.Minimal.finItem (caller :: continuation)
          (toLeaTTaAtom (value (MeTTaData.encode payload))) bindings :: rest) done := by
  have scope : UsesBefore (first + 1) (value target) := by
    simpa [value] using bounded.mono (Nat.le_succ first)
  have resolved : Metta.instantiate bindings (toLeaTTaAtom (value target)) =
      toLeaTTaAtom (value (MeTTaData.encode payload)) := by
    simpa only [value, call, toLeaTTaAtom, toLeaTTaAtoms,
      Metta.instantiate, Metta.Bindings.resolveAtom, List.map_cons, List.map_nil] using
      congrArg (fun atom => Metta.Atom.expr [.sym "nik:Value", atom]) materialized
  have closed : (toLeaTTaAtom (value (MeTTaData.encode payload))).vars = [] := by
    have encodedClosed := data_atom_runtime_closed (MeTTaData.encode_data payload)
    simp [value, call, toLeaTTaAtom, toLeaTTaAtoms, Metta.Atom.vars, encodedClosed]
  simpa only [expression, found] using withFuel_return_to_caller environment state bindings
    (value target) (toLeaTTaAtom (value (MeTTaData.encode payload))) first remaining fuel
    caller continuation rest done groundings privateRemaining scope resolved closed

/-- Closed source environments become literal target input tables. -/
theorem encoded_names_lookup (sourceBindings : Env) (name : String) :
    ((sourceBindings.map fun entry => (entry.1, MeTTaData.encode entry.2)).find?
      (fun entry => entry.1 == name)).map Prod.snd =
    (sourceBindings.lookup name).map MeTTaData.encode := by
  induction sourceBindings with
  | nil => rfl
  | cons entry rest ih =>
    by_cases equal : entry.1 == name
    · simp [List.find?, Env.lookup, equal]
    · simpa only [List.map_cons, List.find?_cons, Env.lookup, equal, if_false] using ih

/-- Source-variable lookup and its absence select the corresponding return code. -/
theorem expression_encoded_variable (program : Program) (sourceBindings : Env)
    (name : String) (sourceFuel : Atom) (first : Nat) :
    expression program (sourceBindings.map fun entry => (entry.1, MeTTaData.encode entry.2))
      sourceFuel (.var name) first =
    withFuel sourceFuel (fun _ => pure (returned
      (((sourceBindings.lookup name).map fun term => value (MeTTaData.encode term)).getD
        (.symbol "nik:Failure")))) first := by
  have lookup := encoded_names_lookup sourceBindings name
  cases found : (sourceBindings.map fun entry => (entry.1, MeTTaData.encode entry.2)).find?
      (fun entry => entry.1 == name) with
  | none =>
    have absent : sourceBindings.lookup name = none := by
      cases sourceFound : sourceBindings.lookup name <;> simp_all
    simp only [expression, found, absent, Option.map_none, Option.getD_none]
  | some pair =>
    obtain ⟨label, target⟩ := pair
    have result : ((sourceBindings.lookup name).map fun term => value (MeTTaData.encode term)).getD
        (.symbol "nik:Failure") = value target := by
      have mapped := congrArg (fun result => (result.map value).getD (.symbol "nik:Failure")) lookup
      simpa only [found, Option.map_some, Option.getD_some, Option.map_map, Function.comp_def]
        using mapped.symm
    simp only [expression, found, result]

/-- Compiled variable access reads the supplied environment and returns through
the current function handler; missing variables give a completed refusal. -/
theorem expression_encoded_variable_enters_handler (program : Program) (sourceBindings : Env)
    (name : String) (first remaining fuel : Nat) (rename : String → String)
    (injective : Function.Injective rename)
    (environment : MinEnv) (state : St) (bindings : Metta.Bindings)
    (stored : ClosedValueBindings bindings)
    (parentBody : Metta.Atom) (scope : List String) (continuation : Stack)
    (rest : List Item) (done : List (Metta.Atom × Metta.Bindings))
    (groundings : environment.gt = Metta.Builtins.table)
    (privateNames : ∀ keyName ∈
      (renBy rename (toLeaTTaAtom (expression program
        (sourceBindings.map fun entry => (entry.1, MeTTaData.encode entry.2))
        (.grounded (.int (remaining + 1))) (.var name) first).1)).vars,
      keyName ∉ bindings.vars) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    let result := ((sourceBindings.lookup name).map fun term => value (MeTTaData.encode term)).getD
      (.symbol "nik:Failure")
    interpretFuel environment (fuel + 9) state
        (⟨atomToStack (renBy rename (toLeaTTaAtom (expression program
          (sourceBindings.map fun entry => (entry.1, MeTTaData.encode entry.2))
          (.grounded (.int (remaining + 1))) (.var name) first).1))
          (parent :: continuation), bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (finItem (parent :: continuation) (.expr [.sym "return", toLeaTTaAtom result]) bindings :: rest) done := by
  intro parent result
  have privateRemaining : Metta.instantiate bindings (.var (rename (freshName first))) =
      .var (rename (freshName first)) := by
    have absent := privateNames _ (expression_remaining_occurs _ _ _ _ _ _)
    have unassigned := stored.toValueBindings.lookup_none_of_not_key
      (fun key => absent (bindingValueKey_mem_vars key))
    simp only [Metta.instantiate, Metta.Bindings.resolveAtom, stored.resolve_eq_lookupVal,
      unassigned, Option.getD_none]
  have bounded : UsesBefore (first + 1) result := by
    cases found : sourceBindings.lookup name with
    | none => simp [result, found]
    | some term => simpa [result, found, value] using usesBefore_data (first + 1) term
  have closed : (toLeaTTaAtom result).vars = [] := by
    cases found : sourceBindings.lookup name with
    | none => simp [result, found, toLeaTTaAtom, Metta.Atom.vars]
    | some term =>
      simp [result, found, value, call, toLeaTTaAtom, toLeaTTaAtoms, Metta.Atom.vars,
        data_atom_runtime_closed (MeTTaData.encode_data term)]
  rw [expression_encoded_variable]
  exact renamed_withFuel_return_enters_handler environment state bindings rename injective
    result (toLeaTTaAtom result) first remaining fuel parentBody scope continuation rest done
    groundings privateRemaining bounded
    (by rw [renBy_eq_self_of_vars_nil rename _ closed,
      Metta.instantiate_of_closed bindings _ closed]) closed

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit
