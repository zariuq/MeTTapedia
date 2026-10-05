import Mettapedia.Languages.MeTTa.HE.FuelConvergenceInterpreter
import MettaHyperonFull.Proofs.BindingLaws

/-!
# Exact control steps of the existing minimal interpreter

These equations expose invocation, sequencing and function return in the
existing stack machine. They retain its binding materialization and real
work-queue driver. Integer guard computations use the existing grounding
implementations; no alternate evaluator or guest primitive is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalControlExecution

open Metta Metta.Minimal
open FuelConvergenceInterpreter

theorem step_eval (environment : MinEnv) (fuel : Nat) (state : St)
    (continuation : Stack) (scope : List VarName) (argument : Atom)
    (bindings : Metta.Bindings) :
    interpretStack1 environment fuel state
        ⟨{ atom := .expr [.sym "eval", argument], vars := scope } :: continuation, bindings⟩ =
      evalOp environment state continuation argument bindings := by
  simp [interpretStack1]

theorem step_unify (environment : MinEnv) (fuel : Nat) (state : St)
    (continuation : Stack) (scope : List VarName) (atom pattern yes no : Atom)
    (bindings : Metta.Bindings) :
    interpretStack1 environment fuel state
        ⟨{ atom := .expr [.sym "unify", atom, pattern, yes, no], vars := scope } ::
          continuation, bindings⟩ =
      (unifyOp continuation atom pattern yes no bindings, state) := by
  simp [interpretStack1]

theorem step_chain_result (environment : MinEnv) (fuel : Nat) (state : St)
    (continuation : Stack) (scope : List VarName) (source result template : Atom)
    (name : VarName) (bindings : Metta.Bindings) :
    interpretStack1 environment fuel state
        (finItem ({ atom := .expr [.sym "chain", source, .var name, template], ret := .chain,
                    vars := scope } :: continuation) result bindings) =
      ([⟨{ atom := .expr [.sym "chain", instantiate bindings result, .var name, template], ret := .chain,
           vars := scope } :: continuation, bindings⟩], state) := by
  simp [interpretStack1, finItem]

theorem step_chain_apply (environment : MinEnv) (fuel : Nat) (state : St)
    (continuation : Stack) (scope : List VarName) (value template : Atom)
    (name : VarName) (bindings : Metta.Bindings) :
    interpretStack1 environment fuel state
        ⟨{ atom := .expr [.sym "chain", value, .var name, template], ret := .chain,
           vars := scope } :: continuation, bindings⟩ =
      ([⟨atomToStack (Subst.apply [(name, value)] template) continuation, bindings⟩], state) := by
  simp [interpretStack1]

theorem step_function_return (environment : MinEnv) (fuel : Nat) (state : St)
    (continuation : Stack) (scope : List VarName) (body value : Atom)
    (bindings : Metta.Bindings) :
    interpretStack1 environment fuel state
        (finItem ({ atom := body, ret := .function, vars := scope } :: continuation)
          (.expr [.sym "return", value]) bindings) =
      ([finItem continuation (instantiate bindings value) bindings], state) := by
  simp [interpretStack1, finItem, instantiate, Bindings.resolveAtom]

/-- A singleton unfinished successor is continued by the actual driver,
with exactly one unit of its own fuel consumed. The rest of the queue and
previous results are preserved. -/
theorem driver_singleton_step (environment : MinEnv) (fuel : Nat)
    (state nextState : St) (item next : Item) (rest : List Item)
    (done : List (Atom × Metta.Bindings))
    (step : interpretStack1 environment fuel state item = ([next], nextState))
    (pending : isFinal next = false) :
    interpretFuel environment (fuel + 1) state (item :: rest) done =
      interpretFuel environment fuel nextState (next :: rest) done := by
  rw [interpretFuel_succ_of environment fuel state nextState item rest [next] done step]
  simp [pending]

theorem builtin_equality (arguments : List Atom) :
    callGrounded Builtins.table "==" arguments = Builtins.eqAtom arguments := by
  rfl

theorem builtin_subtraction (arguments : List Atom) :
    callGrounded Builtins.table "-" arguments = Builtins.numBin (· - ·) (· - ·) arguments := by
  rfl

/-- Closed integer arguments remain integers through bindings, token
substitution and state-handle resolution. The runtime returns its native
Boolean atom, which the ordinary matcher compares with parsed `True`. -/
theorem evalOp_integer_equality (environment : MinEnv) (state : St)
    (continuation : Stack) (bindings : Metta.Bindings) (left right : Int)
    (groundings : environment.gt = Builtins.table) :
    evalOp environment state continuation
        (.expr [.sym "==", .gnd (.int left), .gnd (.int right)]) bindings =
      ([finItem continuation (.gnd (.bool (left == right))) bindings], state) := by
  simp [evalOp, instantiate, Bindings.resolveAtom, subTokens, resolveStates,
    groundings, builtin_equality, Builtins.eqAtom, Atom.isError, Atom.equiv, Ground.equiv, Ground.beq,
    evalResult, finItem]

theorem evalOp_integer_subtraction (environment : MinEnv) (state : St)
    (continuation : Stack) (bindings : Metta.Bindings) (left right : Int)
    (groundings : environment.gt = Builtins.table) :
    evalOp environment state continuation
        (.expr [.sym "-", .gnd (.int left), .gnd (.int right)]) bindings =
      ([finItem continuation (.gnd (.int (left - right))) bindings], state) := by
  simp [evalOp, instantiate, Bindings.resolveAtom, subTokens, resolveStates,
    groundings, builtin_subtraction, Builtins.numBin, evalResult, finItem]

/-- The actual matcher accepts the grounded Boolean returned by `==` against
the emitted Boolean pattern, retaining the incoming acyclic frame. -/
theorem unifyOp_true (continuation : Stack) (yes no : Atom) (bindings : Metta.Bindings)
    (acyclic : bindings.hasLoop = false) :
    unifyOp continuation (.gnd (.bool true)) (.gnd (.bool true)) yes no bindings =
      [finItem continuation (instantiate bindings yes) bindings] := by
  have matched : matchAtoms (.gnd (.bool true)) (.gnd (.bool true)) = [[]] := rfl
  simp [unifyOp, matched, Bindings.merge_empty_right, acyclic]

/-- A false guard takes only the fallback; it does not evaluate the true arm. -/
theorem unifyOp_false (continuation : Stack) (yes no : Atom) (bindings : Metta.Bindings) :
    unifyOp continuation (.gnd (.bool false)) (.gnd (.bool true)) yes no bindings =
      [finItem continuation no bindings] := by
  have matched : matchAtoms (.gnd (.bool false)) (.gnd (.bool true)) = [] := rfl
  simp [unifyOp, matched]

/-- A symbolic spelling is not a Boolean atom. This is why emitted syntax
must agree with the parser's literal representation. -/
theorem unifyOp_symbolic_true_refuses (continuation : Stack) (yes no : Atom)
    (bindings : Metta.Bindings) :
    unifyOp continuation (.gnd (.bool true)) (.sym "True") yes no bindings =
      [finItem continuation no bindings] := by
  simp [unifyOp, matchAtoms, matchAtomsWith, Atom.equiv]

/-- A zero guard selects its return without executing the fallback. The
exact four-step prefix preserves the surrounding stack, work queue and
previous results, so it can be used by both top-level and recursive calls. -/
theorem integer_zero_guard_selects_in_frame (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (name marker : String) (otherwise : Atom) (fuel : Nat)
    (parent : Frame) (continuation : Stack) (rest : List Item) (done : List (Atom × Metta.Bindings))
    (groundings : environment.gt = Builtins.table)
    (acyclic : bindings.hasLoop = false) :
    let equality := Atom.expr [.sym "eval", .expr [.sym "==", .gnd (.int 0), .gnd (.int 0)]]
    let template := Atom.expr [.sym "unify", .var name, .gnd (.bool true),
      .expr [.sym "return", .sym marker], otherwise]
    let body := Atom.expr [.sym "chain", equality, .var name, template]
    interpretFuel environment (fuel + 4) state
        (⟨atomToStack body (parent :: continuation), bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (finItem (parent :: continuation) (.expr [.sym "return", .sym marker]) bindings :: rest) done := by
  intro equality template body
  let scope := chainFrameVars (parent :: continuation) equality template
  let start : Item := ⟨{ atom := equality, vars := scope } ::
    { atom := body, ret := .chain, vars := scope } :: (parent :: continuation), bindings⟩
  let first := finItem ({ atom := body, ret := .chain, vars := scope } :: (parent :: continuation))
    (.gnd (.bool true)) bindings
  let second : Item := ⟨{ atom := .expr [.sym "chain", .gnd (.bool true), .var name, template], ret := .chain, vars := scope } :: (parent :: continuation), bindings⟩
  let selected := Atom.expr [.sym "unify", .gnd (.bool true), .gnd (.bool true),
    .expr [.sym "return", .sym marker], Subst.apply [(name, .gnd (.bool true))] otherwise]
  let third : Item := ⟨atomToStack selected (parent :: continuation), bindings⟩
  let fourth := finItem (parent :: continuation) (.expr [.sym "return", .sym marker]) bindings
  have initial : atomToStack body (parent :: continuation) = start.stack := by
    simp [body, equality, start, scope, atomToStack, varsCopy, chainFrameVars]
  have firstStep (budget : Nat) :
      interpretStack1 environment budget state start = ([first], state) := by
    dsimp only [start, equality]
    rw [step_eval]
    simpa [first] using evalOp_integer_equality environment state
      ({ atom := body, ret := .chain, vars := scope } :: (parent :: continuation)) bindings 0 0 groundings
  have secondStep (budget : Nat) :
      interpretStack1 environment budget state first = ([second], state) := by
    simpa [first, second, body, instantiate, Bindings.resolveAtom] using
      step_chain_result environment budget state (parent :: continuation) scope equality
        (.gnd (.bool true)) template name bindings
  have thirdStep (budget : Nat) :
      interpretStack1 environment budget state second = ([third], state) := by
    rw [show second = ⟨{ atom := .expr [.sym "chain", .gnd (.bool true), .var name, template], ret := .chain, vars := scope } :: (parent :: continuation), bindings⟩ from rfl,
      step_chain_apply]
    simp [third, selected, template, Subst.apply, Subst.lookup]
  have fourthStep (budget : Nat) :
      interpretStack1 environment budget state third = ([fourth], state) := by
    simp only [third, selected, atomToStack, step_unify]
    rw [unifyOp_true _ _ _ _ acyclic]
    simp [fourth, instantiate, Bindings.resolveAtom]
  rw [initial]
  change interpretFuel environment (fuel + 4) state (start :: rest) done = _
  rw [driver_singleton_step environment (fuel + 3) state state start first rest done
    (firstStep _) (by rfl)]
  rw [driver_singleton_step environment (fuel + 2) state state first second rest done
    (secondStep _) (by rfl)]
  rw [driver_singleton_step environment (fuel + 1) state state second third rest done
    (thirdStep _) (by rfl)]
  exact driver_singleton_step environment fuel state state third fourth rest done
    (fourthStep _) (by rfl)

/-- Opening a function specializes the same guard law to its new frame. -/
theorem integer_zero_guard_selects (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (name marker : String) (otherwise : Atom) (fuel : Nat)
    (continuation : Stack) (rest : List Item) (done : List (Atom × Metta.Bindings))
    (groundings : environment.gt = Builtins.table)
    (acyclic : bindings.hasLoop = false) :
    let equality := Atom.expr [.sym "eval", .expr [.sym "==", .gnd (.int 0), .gnd (.int 0)]]
    let template := Atom.expr [.sym "unify", .var name, .gnd (.bool true),
      .expr [.sym "return", .sym marker], otherwise]
    let body := Atom.expr [.sym "chain", equality, .var name, template]
    let parent : Frame :=
      { atom := .expr [.sym "function", body], ret := .function, vars := varsCopy continuation }
    interpretFuel environment (fuel + 4) state
        (⟨atomToStack (.expr [.sym "function", body]) continuation, bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (finItem (parent :: continuation) (.expr [.sym "return", .sym marker]) bindings :: rest) done := by
  intro equality template body parent
  simpa only [body, equality, template, parent, atomToStack] using
    integer_zero_guard_selects_in_frame environment state bindings name marker otherwise fuel
      parent continuation rest done groundings acyclic

/-- A complete top-level zero guard returns exactly one exhaustion marker.
The recursive case uses the same guard prefix. -/
theorem integer_zero_guard_returns (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (name marker : String) (otherwise : Atom) (fuel : Nat)
    (groundings : environment.gt = Builtins.table)
    (acyclic : bindings.hasLoop = false) (visible : marker ≠ "Empty") :
    let equality := Atom.expr [.sym "eval", .expr [.sym "==", .gnd (.int 0), .gnd (.int 0)]]
    let template := Atom.expr [.sym "unify", .var name, .gnd (.bool true),
      .expr [.sym "return", .sym marker], otherwise]
    let body := Atom.expr [.sym "chain", equality, .var name, template]
    interpretFuel environment (fuel + 5) state
        [⟨atomToStack (.expr [.sym "function", body]) [], bindings⟩] [] =
      ([(.sym marker, bindings)], state) := by
  intro equality template body
  let parent : Frame := { atom := .expr [.sym "function", body], ret := .function }
  let fourth := finItem [parent] (.expr [.sym "return", .sym marker]) bindings
  have lastStep (budget : Nat) :
      interpretStack1 environment budget state fourth =
        ([finItem [] (.sym marker) bindings], state) := by
    simpa [fourth, parent, instantiate, Bindings.resolveAtom] using
      step_function_return environment budget state [] []
        (.expr [.sym "function", body]) (.sym marker) bindings
  rw [show fuel + 5 = (fuel + 1) + 4 by omega,
    integer_zero_guard_selects environment state bindings name marker otherwise
      (fuel + 1) [] [] [] groundings acyclic]
  change interpretFuel environment (fuel + 1) state [fourth] [] = _
  rw [interpretFuel_succ_of environment fuel state state fourth []
    [finItem [] (.sym marker) bindings] [] (lastStep _)]
  change interpretFuel environment fuel state [] [(instantiate bindings (.sym marker), bindings)] = _
  rw [interpretFuel_nil]
  have kept : ((.sym marker : Atom) != .sym "Empty") = true := by
    change (marker != "Empty") = true
    simp [visible]
  simp [instantiate, Bindings.resolveAtom, emptyA, kept]

end Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalControlExecution
