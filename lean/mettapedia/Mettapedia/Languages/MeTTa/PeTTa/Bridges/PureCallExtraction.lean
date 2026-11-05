import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarInvocation
import Mettapedia.GSLT.Dynamics.RegionPortfolio

/-!
# Call-aware partial evaluation over actual PeTTa source

The input is a loaded program, captured substitution and source Atom. The
preparer reuses typed scalar/body extraction, then follows pure authored
calls through the actual argument-demand and clause-selection functions.
Each result proves singleton return, unchanged state and no I/O for every
initial effect state. A finite unfolding budget refuses recursive work it
cannot finish. Refusal does not assert divergence, absence or a source fault.

This is call-specific partial evaluation, not a symbolic theorem about every
possible argument to the function. The preparation cost is not a speedup.
Whole-fold host dispatch and replacement of a loop by an algebraic summary
require their own source and uniformity bridges.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.PureCallExtraction

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Eval SpaceSemantics
open Mettapedia.Machines.TypedScalar

/-- Source-result evidence is universally state preserving. It is built by
the preparer below from scalar derivations and actual operational call laws. -/
structure Certified (program : Program) (caller : Subst) (source : Atom) where
  value : Atom
  returns : ∀ state, PureReturns program caller state source state value

structure Arguments (program : Program) (caller : Subst) (sources : List Atom) where
  values : List Atom
  returns : ∀ state, List.Forall₂
    (fun source value => PureReturns program caller state source state value) sources values

def Arguments.nil (program : Program) (caller : Subst) : Arguments program caller [] :=
  ⟨[], fun _ => .nil⟩

def Arguments.cons {program : Program} {caller : Subst} {source : Atom} {sources : List Atom}
    (head : Certified program caller source) (tail : Arguments program caller sources) :
    Arguments program caller (source :: sources) :=
  ⟨head.value :: tail.values, fun state => .cons (head.returns state) (tail.returns state)⟩

/-- Lift independently established argument results through the evaluator's
actual left-to-right argument frames. Raw-demand positions are not admitted. -/
theorem evaluated_arguments (program : Program) (caller : Subst) (state : Effects.State)
    (head : String) (sources values : List Atom)
    (returns : List.Forall₂ (fun source value => PureReturns program caller state source state value)
      sources values) (prior : List Atom) (index : Nat) (answer : Atom)
    (demand : ∀ offset < sources.length, argumentIsRaw program head (index + offset) = false)
    (rest : (theory program).MultiStep
      { state, control := .arguments caller (.function head) [] (prior ++ values) (index + sources.length) }
      (finished state [answer] [] [])) :
    (theory program).MultiStep
      { state, control := .arguments caller (.function head) sources prior index }
      (finished state [answer] [] []) := by
  induction returns generalizing prior index with
  | nil => simpa using rest
  | @cons source value sources values first later ih =>
      apply evaluated_argument_returns program caller state state state (.function head)
        source value answer sources prior index
        (by simpa using demand 0 (by simp)) first
      apply ih (prior ++ [value]) (index + 1)
      · intro offset bounded
        simpa [Nat.add_assoc, Nat.add_comm 1] using demand (offset + 1) (by simpa using bounded)
      · simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 1] using rest

def fromScalar (program : Program) (caller : Subst) (source : Atom) :
    Option (Certified program caller source) := do
  let compiled ← ScalarBody.elaborate program (ScalarInvocation.environment caller) source
  match evaluated : compiled.val.eval program (ScalarInvocation.locals caller) with
  | none => none
  | some value =>
      return ⟨value, fun state => compiled.property.returns caller state
        (ScalarInvocation.locals caller) (ScalarInvocation.captured caller) value evaluated⟩

/-- Captured values are not re-evaluated. Their full Atom is retained even
when it is a Boolean, tuple, handle or code-shaped value outside scalar IR. -/
def fromValue (program : Program) (caller : Subst) : (source : Atom) →
    Option (Certified program caller source)
  | .var name => some ⟨applySubst caller (.var name), fun state => variable_returns program caller state name⟩
  | .symbol name => some ⟨.symbol name, fun state => symbol_returns program caller state name⟩
  | .grounded value => some ⟨.grounded value, fun state => grounded_returns program caller state value⟩
  | .expression [] => some ⟨.expression [], fun _ =>
      .step (step_transition rfl) (.step (step_transition rfl) (.refl _))⟩
  | _ => none

structure Callable (program : Program) (head : String) (arity : Nat) : Prop where
  notIO : ioHead head = false
  notNative : StdLib.known head = false
  registered : program.equations.any (·.head == head) = true
  ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"]
  demanded : ∀ index < arity, argumentIsRaw program head index = false

def callable (program : Program) (head : String) (arity : Nat) : Option (PLift (Callable program head arity)) :=
  if notIO : ioHead head = false then
    if notNative : StdLib.known head = false then
      if registered : program.equations.any (·.head == head) = true then
        if ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"] then
          if demanded : ∀ index ∈ List.range arity, argumentIsRaw program head index = false then
            some ⟨⟨notIO, notNative, registered, ordinary, fun index bounded =>
              demanded index (List.mem_range.mpr bounded)⟩⟩
          else none
        else none
      else none
    else none
  else none

def call {program : Program} {caller callee : Subst} {head : String} {sources : List Atom}
    {body : Atom} (admitted : Callable program head sources.length)
    (arguments : Arguments program caller sources)
    (selected : clauses program head arguments.values = [.evaluate callee body])
    (compiled : Certified program callee body) :
    Certified program caller (.expression (.symbol head :: sources)) where
  value := compiled.value
  returns state := by
    apply call_returns program caller state state head sources compiled.value
      (by simp [admitted.registered]) _ admitted.ordinary
    apply evaluated_arguments program caller state head sources arguments.values
      (arguments.returns state) [] 0 compiled.value (by simpa using admitted.demanded)
    simpa using authored_function_arguments_return program caller callee state state head arguments.values
      sources.length body compiled.value admitted.notIO admitted.notNative selected (compiled.returns state)

def branch {program : Program} {caller : Subst} {test yes no : Atom}
    (condition : Certified program caller test) (flag : Bool)
    (boolean : condition.value = Effects.boolean flag)
    (chosen : Certified program caller (if flag then yes else no)) :
    Certified program caller (.expression [.symbol "if", test, yes, no]) where
  value := chosen.value
  returns state := BridgeKit.pure_if_returns program caller state test flag yes no chosen.value
    (by rw [← boolean]; exact condition.returns state) (chosen.returns state)

def decode (atom : Atom) : Option (Sigma Value) :=
  match atom with
  | .grounded (.int value) => some ⟨.data, .integer value⟩
  | .grounded (.bool value) => some ⟨.test, value⟩
  | .symbol name => some ⟨.data, .symbol name⟩
  | _ => none

theorem decode_exact (atom : Atom) (value : Sigma Value) (decoded : decode atom = some value) :
    atom = ScalarSource.encode value.2 := by
  cases atom with
  | grounded ground =>
      cases ground <;> simp only [decode] at decoded
      all_goals first | contradiction | (cases decoded; rfl)
  | symbol name => cases decoded; rfl
  | var | expression => cases decoded

theorem binary_returns {a b c : Kind} (op : Binary a b c)
    (program : Program) (caller : Subst) (state : Effects.State)
    (left right : Atom) (x : Value a) (y : Value b) (value : Value c)
    (first : PureReturns program caller state left state (ScalarSource.encode x))
    (second : PureReturns program caller state right state (ScalarSource.encode y))
    (computed : op.eval x y = some value) :
    PureReturns program caller state (.expression [.symbol op.name, left, right]) state
      (ScalarSource.encode value) := by
  exact native_binary_call_returns program caller state state state state op.name
    left right (ScalarSource.encode x) (ScalarSource.encode y) (ScalarSource.encode value)
    (by cases op <;> simp [Binary.name, ioHead])
    (by cases op <;> simp [Binary.name, StdLib.known])
    (by cases op <;> simp [Binary.name, argumentIsRaw, StdLib.known, StdLib.rawArgument])
    (by cases op <;> simp [Binary.name, argumentIsRaw, StdLib.known, StdLib.rawArgument])
    first second (ScalarSource.binary_primitive op state x y value computed)
    (by cases op <;> simp [Binary.name])

/-- Recursive pure calls may occur inside scalar operands. Booleans retain
their own sort, so a comparison result is never silently re-encoded as 0/1. -/
def binary {program : Program} {caller : Subst} {left right : Atom}
    (head : String) (first : Certified program caller left) (second : Certified program caller right) :
    Option (Certified program caller (.expression [.symbol head, left, right])) := do
  match leftDecoded : decode first.value with
  | none => none
  | some x =>
    match rightDecoded : decode second.value with
    | none => none
    | some y =>
      let ⟨kind, op⟩ ← ScalarSource.selectBinary head x.1 y.1
      if same : op.name = head then
        if _clear : ScalarSource.Clear program head then
          match computed : op.eval x.2 y.2 with
          | none => none
          | some value =>
              return ⟨ScalarSource.encode value, fun state => by
                subst head
                exact binary_returns op program caller state left right x.2 y.2 value
                  (by rw [← decode_exact first.value x leftDecoded]; exact first.returns state)
                  (by rw [← decode_exact second.value y rightDecoded]; exact second.returns state)
                  computed⟩
        else none
      else none

/-- The outer fuel bounds source unfolding, including nested actual calls.
Scalar leaf compilation does not evaluate effects or run the reference engine. -/
def prepare : (fuel : Nat) → (program : Program) → (caller : Subst) →
    (source : Atom) → Option (Certified program caller source)
  | 0, _, _, _ => none
  | fuel + 1, program, caller, source =>
      match (fromValue program caller source).orElse (fun _ => fromScalar program caller source) with
      | some compiled => some compiled
      | none => match source with
        | .expression [.symbol "if", test, yes, no] => do
            let condition ← prepare fuel program caller test
            match value : condition.value with
            | .grounded (.bool flag) =>
                let chosen ← prepare fuel program caller (if flag then yes else no)
                return branch condition flag value chosen
            | _ => none
        | .expression [.symbol head, left, right] =>
            match prepare fuel program caller left, prepare fuel program caller right with
            | some first, some second =>
                match binary head first second with
                | some compiled => some compiled
                | none => authored program caller head [left, right] (prepare fuel program)
            | _, _ => none
        | .expression (.symbol head :: sources) =>
            authored program caller head sources (prepare fuel program)
        | _ => none
where
  authored (program : Program) (caller : Subst) (head : String) (sources : List Atom)
      (compile : (bindings : Subst) → (source : Atom) → Option (Certified program bindings source)) :
      Option (Certified program caller (.expression (.symbol head :: sources))) := do
    let admitted ← callable program head sources.length
    let args ← arguments program caller (compile caller) sources
    match selected : clauses program head args.values with
    | [.evaluate callee body] =>
        let compiled ← compile callee body
        return call admitted.down args selected compiled
    | _ => none

  arguments (program : Program) (caller : Subst)
      (compile : (source : Atom) → Option (Certified program caller source)) :
      (sources : List Atom) → Option (Arguments program caller sources)
    | [] => some (Arguments.nil program caller)
    | first :: rest => do
        let head ← compile first
        let tail ← arguments program caller compile rest
        return Arguments.cons head tail

theorem zero_budget_declines (program : Program) (caller : Subst) (source : Atom) :
    prepare 0 program caller source = none := rfl

/-- Both directions of the complete observation: no additional result,
state change or I/O can hide behind successful pure extraction. -/
theorem completed_iff {program : Program} {caller : Subst} {source : Atom}
    (compiled : Certified program caller source) (state after : Effects.State)
    (answers input output : List Atom) :
    (∃ fuel, run program fuel {state, control := .evaluate caller source} =
      .complete after answers input output) ↔
      after = state ∧ answers = [compiled.value] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program caller state state source compiled.value
    (compiled.returns state) after answers input output

/-- Exact-page clients can observe source fuel and residual configurations;
completed-result clients ask only for the unique eventual result. -/
inductive Observation | completedResult | exactPage
  deriving DecidableEq

/-- Exact-page demand declines this shortcut. A rejected preparation uses
the unchanged input and budget of the ordinary evaluator. -/
def execute (observation : Observation) (prepareFuel sourceFuel : Nat) (program : Program) (caller : Subst)
    (source : Atom) (state : Effects.State) : Outcome :=
  if observation = .exactPage then run program sourceFuel {state, control := .evaluate caller source}
  else match prepare prepareFuel program caller source with
    | none => run program sourceFuel {state, control := .evaluate caller source}
    | some compiled => .complete state [compiled.value] [] []

theorem refusal_falls_back (observation : Observation) (prepareFuel sourceFuel : Nat) (program : Program) (caller : Subst)
    (source : Atom) (state : Effects.State)
    (declined : prepare prepareFuel program caller source = none) :
    execute observation prepareFuel sourceFuel program caller source state =
      run program sourceFuel {state, control := .evaluate caller source} := by
  simp [execute, declined]

theorem exact_page_always_uses_source (prepareFuel sourceFuel : Nat) (program : Program) (caller : Subst)
    (source : Atom) (state : Effects.State) :
    execute .exactPage prepareFuel sourceFuel program caller source state =
      run program sourceFuel {state, control := .evaluate caller source} := by
  simp [execute]

/-- Successful extraction certifies the completed source observation, not
equality at an arbitrary insufficient source fuel. -/
theorem accepted_has_source_run (prepareFuel : Nat) (program : Program) (caller : Subst)
    (source : Atom) (state : Effects.State) (compiled : Certified program caller source)
    (accepted : prepare prepareFuel program caller source = some compiled) (sourceFuel : Nat) :
    ∃ fuel, run program fuel {state, control := .evaluate caller source} =
      execute .completedResult prepareFuel sourceFuel program caller source state := by
  simp only [execute, reduceCtorEq, ↓reduceIte, accepted]
  exact (completed_iff compiled state state [compiled.value] [] []).mpr ⟨rfl, rfl, rfl, rfl⟩

theorem execute_no_invented_completion (observation : Observation) (prepareFuel sourceFuel : Nat)
    (program : Program) (caller : Subst) (source : Atom) (state after : Effects.State)
    (answers input output : List Atom)
    (completed : execute observation prepareFuel sourceFuel program caller source state =
      .complete after answers input output) :
    ∃ fuel, run program fuel {state, control := .evaluate caller source} =
      .complete after answers input output := by
  cases observation with
  | exactPage => exact ⟨sourceFuel, by simpa [execute] using completed⟩
  | completedResult =>
      cases prepared : prepare prepareFuel program caller source with
      | none => exact ⟨sourceFuel, by simpa [execute, prepared] using completed⟩
      | some compiled =>
          have same : state = after ∧ [compiled.value] = answers ∧ [] = input ∧ [] = output := by
            simpa [execute, prepared] using completed
          obtain ⟨rfl, rfl, rfl, rfl⟩ := same
          exact (completed_iff compiled state state [compiled.value] [] []).mpr ⟨rfl, rfl, rfl, rfl⟩

theorem execute_preserves_completed_source (observation : Observation) (prepareFuel sourceFuel : Nat)
    (program : Program) (caller : Subst) (source : Atom) (state after : Effects.State)
    (answers input output : List Atom)
    (completed : run program sourceFuel {state, control := .evaluate caller source} =
      .complete after answers input output) :
    execute observation prepareFuel sourceFuel program caller source state =
      .complete after answers input output := by
  cases observation with
  | exactPage => simpa [execute] using completed
  | completedResult =>
      cases prepared : prepare prepareFuel program caller source with
      | none => simpa [execute, prepared] using completed
      | some compiled =>
          obtain ⟨rfl, rfl, rfl, rfl⟩ :=
            (completed_iff compiled state after answers input output).mp ⟨sourceFuel, completed⟩
          simp [execute, prepared]

/-- Reuse across program changes uses the existing operational support law.
Agreement includes dispatch, argument demand and selected bodies; agreeing
only on the latest returned value is not this premise. -/
def Certified.transport {allowed : String → Bool} {first second : Program}
    {caller : Subst} {source : Atom} (compiled : Certified first caller source)
    (closed : ProgramClosed allowed first) (agreement : ProgramAgreementOn allowed first second)
    (within : codeWithin allowed source = true) : Certified second caller source where
  value := compiled.value
  returns state := path_of_closed_agreement closed agreement ⟨within, rfl⟩ (compiled.returns state)

/-- Renaming caller variables is justified by equality of the captured
argument values, not by forgetting their frames or comparing raw spellings. -/
def Certified.recapture {program : Program} {first second : Subst}
    {head : String} {one two : List Atom}
    (compiled : Certified program first (.expression (.symbol head :: one)))
    (dispatch : (ioHead head || StdLib.known head || program.equations.any (·.head == head)) = true)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"])
    (firstAdmitted : ∀ offset argument, one[offset]? = some argument →
      argumentIsRaw program head offset = true ∨ passiveArgument argument = true)
    (secondAdmitted : ∀ offset argument, two[offset]? = some argument →
      argumentIsRaw program head offset = true ∨ passiveArgument argument = true)
    (captured : one.map (applySubst first) = two.map (applySubst second)) :
    Certified program second (.expression (.symbol head :: two)) where
  value := compiled.value
  returns state := captured_call_returns program first second state state head one two compiled.value
    dispatch ordinary firstAdmitted secondAdmitted captured (compiled.returns state)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.PureCallExtraction
