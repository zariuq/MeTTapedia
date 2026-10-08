import Mettapedia.Machines.CMemory.ReadLoops

/-!
# Scoped read blocks with retained C control flow

Declarations, local assignments, eager Boolean compound OR, selected branches
and explicit return/break compose physical scalar-expression reads. Nested
flat read loops use the existing counted-loop interpreter. Statement fuel and
iteration fuel are separate from undefined reads and completed C outcomes.

The outer counted-block operation executes each supplied body through this
block service; it propagates returns and exits breaks without incrementing.
This fragment does not execute allocation, physical stores or arbitrary nested
imperative loops. It reuses the shared heap primitives and their lifetime
requirements, rather than defining another memory model.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory.ReadBlock

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open ReadExpressions

inductive Flow (Context : Type := Environment) where
  | next (environment : Context)
  | broken (environment : Context)
  | returned (environment : Context) (value : Option CVal)

inductive Result (Context : Type := Environment) where
  | finished (flow : Flow Context)
  | exhausted

def resume {Context : Type} (continuation : Context → CProg CVal (Result Context)) :
    Result Context → CProg CVal (Result Context)
  | .finished (.next environment) => continuation environment
  | result => pure result

/-- Flow readouts transport the complete returned context while retaining
break, return and the optional scalar result. -/
def Flow.mapContext {Context Other : Type} (map : Context → Other) : Flow Context → Flow Other
  | .next context => .next (map context)
  | .broken context => .broken (map context)
  | .returned context value => .returned (map context) value

def Result.mapContext {Context Other : Type} (map : Context → Other) :
    Result Context → Result Other
  | .finished flow => .finished (flow.mapContext map)
  | .exhausted => .exhausted

/-- A function-reply observer reads only an explicit returned scalar.
Exhaustion and normal/break flow do not invent a completed return value. -/
def Result.returnedValue? {Context : Type} : Result Context → Option CVal
  | .finished (.returned _ value) => value
  | _ => none

/-- Transporting a lexical context preserves this scalar-reply observer.
Observers of the context itself still require their own compatibility law. -/
theorem returned_value_context_map {Context Other : Type} (map : Context → Other)
    (result : Result Context) :
    (result.mapContext map).returnedValue? = result.returnedValue? := by
  cases result with
  | exhausted => rfl
  | finished flow => cases flow <;> rfl

theorem returned_value_is_explicit {Context : Type} (context : Context) (value : CVal) :
    (Result.finished (Flow.returned context (some value))).returnedValue? = some value := rfl

theorem exhaustion_does_not_invent_return {Context : Type} :
    (Result.exhausted : Result Context).returnedValue? = none := rfl

theorem flow_context_map_identity {Context : Type} (flow : Flow Context) :
    flow.mapContext id = flow := by cases flow <;> rfl

theorem flow_context_map_composition {First Second Third : Type}
    (first : First → Second) (second : Second → Third) (flow : Flow First) :
    (flow.mapContext first).mapContext second = flow.mapContext (second ∘ first) := by
  cases flow <;> rfl

theorem result_context_map_identity {Context : Type} (result : Result Context) :
    result.mapContext id = result := by
  cases result with
  | exhausted => rfl
  | finished flow => cases flow <;> rfl

theorem result_context_map_composition {First Second Third : Type}
    (first : First → Second) (second : Second → Third) (result : Result First) :
    (result.mapContext first).mapContext second = result.mapContext (second ∘ first) := by
  cases result with
  | exhausted => rfl
  | finished flow => cases flow <;> rfl

def restore (name : Name) (previous : Option CVal) : Result → Result
  | .finished (.next environment) => .finished (.next (Function.update environment name previous))
  | .finished (.broken environment) => .finished (.broken (Function.update environment name previous))
  | .finished (.returned environment value) =>
      .finished (.returned (Function.update environment name previous) value)
  | .exhausted => .exhausted

theorem restore_is_context_map (name : Name) (previous : Option CVal) (result : Result) :
    restore name previous result =
      result.mapContext (fun context => Function.update context name previous) := by
  cases result with
  | exhausted => rfl
  | finished flow => cases flow <;> rfl

theorem returned_declaration_restores_scope (environment : ReadExpressions.Environment)
    (name : Name) (localValue : Option CVal) (returnedValue : Option CVal) :
    restore name (environment name)
      (.finished (.returned (Function.update environment name localValue) returnedValue)) =
        .finished (.returned environment returnedValue) := by
  simp only [restore, Function.update_idem, Function.update_eq_self]

theorem returned_nested_declarations_restore_scope (environment : ReadExpressions.Environment)
    (outer inner : Name) (outerValue innerValue returnedValue : Option CVal) :
    restore outer (environment outer)
      (restore inner (Function.update environment outer outerValue inner)
        (.finished (.returned
          (Function.update (Function.update environment outer outerValue) inner innerValue)
          returnedValue))) = .finished (.returned environment returnedValue) := by
  rw [returned_declaration_restores_scope, returned_declaration_restores_scope]

theorem resume_return_does_not_enter_continuation
    (continuation : Environment → CProg CVal Result) (environment : Environment)
    (value : Option CVal) :
    resume continuation (.finished (.returned environment value)) =
      pure (.finished (.returned environment value)) := rfl

theorem resume_normal_completion_enters_continuation
    (continuation : Environment → CProg CVal Result) (environment : Environment) :
    resume continuation (.finished (.next environment)) = continuation environment := rfl

def declaredValue (type : CType) (value : CVal) : CProg CVal CVal :=
  if type = ⟨"bool".toList, 0⟩ then truth value >>= fun selected => pure (.bool selected)
  else if type = ⟨"int".toList, 0⟩ then signedWord value >>= fun signed => pure (.i32 signed)
  else if type = ⟨"uint32_t".toList, 0⟩ then word value >>= fun unsigned => pure (.u32 unsigned)
  else if type = ⟨"Space".toList, 1⟩ then pointer value >>= fun address => pure (.ptr address)
  else CProg.undefined

theorem declared_pointer_retains_nullable_value (value : Option Ptr) :
    declaredValue ⟨"Space".toList, 1⟩ (.ptr value) = pure (.ptr value) := rfl

theorem declared_boolean_retains_value (value : Bool) :
    declaredValue ⟨"bool".toList, 0⟩ (.bool value) = pure (.bool value) := rfl

/-- This admitted native profile has a 32-bit `int`; the signed input is
transported rather than coerced to an unsigned counter. -/
theorem declared_signed_retains_value (value : Int32) :
    declaredValue ⟨"int".toList, 0⟩ (.i32 value) = pure (.i32 value) := rfl

/-- Both operands are read, including when the previous Boolean is true.
The admitted operands are canonical Boolean values; no mixed-width integer
promotion is assumed by this operation. -/
def booleanOrAssignment (layout : Layout) (environment : Environment)
    (name : Name) (rhs : CExpr) : CProg CVal Environment := do
  let old ← resolved (environment name)
  let actual ← expression layout environment rhs
  match old, actual with
  | .bool previous, .bool incoming =>
      pure (Function.update environment name (some (.bool (previous || incoming))))
  | _, _ => CProg.undefined

def assign (layout : Layout) (environment : Environment) : CStatement → CProg CVal Environment
  | .assign (.identifier name) rhs => ReadLoops.statements layout environment
      [.assign (.identifier name) rhs]
  | .compoundAssign .bitOr (.identifier name) rhs =>
      booleanOrAssignment layout environment name rhs
  | _ => CProg.undefined

def execute (layout : Layout) (loopFuel : Nat) (fuel : Nat) (environment : Environment)
    (body : List CStatement) : CProg CVal Result :=
  match body with
  | [] => pure (.finished (.next environment))
  | statement :: rest => match fuel with
    | 0 => pure .exhausted
    | fuel + 1 => match statement with
      | .empty => execute layout loopFuel fuel environment rest
      | .declare type name rhs => do
          let actual ← expression layout environment rhs
          let initial ← declaredValue type actual
          let result ← execute layout loopFuel fuel
            (Function.update environment name (some initial)) rest
          pure (restore name (environment name) result)
      | .assign _ _ | .compoundAssign _ _ _ => do
          let updated ← assign layout environment statement
          execute layout loopFuel fuel updated rest
      | .branch condition yes no => do
          let actual ← expression layout environment condition
          let selected ← truth actual
          let result ← execute layout loopFuel fuel environment (if selected then yes else no)
          resume (fun updated => execute layout loopFuel fuel updated rest) result
      | .forLoop _ _ _ _ _ _ => do
          let result ← ReadLoops.counted layout loopFuel environment statement
          match result with
          | .finished updated => execute layout loopFuel fuel updated rest
          | .exhausted => pure .exhausted
      | .break => pure (.finished (.broken environment))
      | .return none => pure (.finished (.returned environment none))
      | .return (some rhs) => do
          let actual ← expression layout environment rhs
          pure (.finished (.returned environment (some actual)))
      | _ => CProg.undefined

def loop (layout : Layout) (innerFuel bodyFuel : Nat) (condition step : CExpr)
    (body : List CStatement) (fuel : Nat) (environment : Environment) : CProg CVal Result := do
  let actual ← expression layout environment condition
  let selected ← truth actual
  if selected then match fuel with
    | 0 => pure .exhausted
    | fuel + 1 => do
        let result ← execute layout innerFuel bodyFuel environment body
        match result with
        | .finished (.next updated) => do
            let advanced ← ReadLoops.increment updated step
            loop layout innerFuel bodyFuel condition step body fuel advanced
        | .finished (.broken updated) => pure (.finished (.next updated))
        | result => pure result
  else pure (.finished (.next environment))

def counted (layout : Layout) (innerFuel bodyFuel fuel : Nat) (environment : Environment) :
    CStatement → CProg CVal Result
  | .forLoop type name initial condition step body =>
      if type = ⟨"uint32_t".toList, 0⟩ then do
        let actual ← expression layout environment initial
        let unsigned ← word actual
        let result ← loop layout innerFuel bodyFuel condition step body fuel
          (Function.update environment name (some (.u32 unsigned)))
        pure (restore name (environment name) result)
      else CProg.undefined
  | _ => CProg.undefined

theorem scope_restoration_keeps_other_assignment (environment : Environment)
    (localName otherName : Name) (localValue otherValue : Option CVal)
    (different : localName ≠ otherName) :
    Function.update (Function.update (Function.update environment localName localValue)
      otherName otherValue) localName (environment localName) =
      Function.update environment otherName otherValue := by
  rw [Function.update_comm different, Function.update_idem,
    Function.update_comm different.symm, Function.update_eq_self]

theorem empty_body_is_normal_completion (layout : Layout) (loopFuel fuel : Nat)
    (environment : Environment) :
    execute layout loopFuel fuel environment [] = pure (.finished (.next environment)) := by
  rw [execute.eq_def]

theorem declaration_retains_actual_read_and_scope (layout : Layout) (loopFuel fuel : Nat)
    (environment : Environment) (type : CType) (name : Name) (rhs : CExpr)
    (rest : List CStatement) :
    execute layout loopFuel (fuel + 1) environment (.declare type name rhs :: rest) =
      (expression layout environment rhs >>= fun actual => declaredValue type actual >>= fun initial =>
        execute layout loopFuel fuel (Function.update environment name (some initial)) rest >>=
          fun result => pure (restore name (environment name) result)) := by
  rw [execute.eq_def]

theorem branch_retains_selected_body_and_continuation (layout : Layout) (loopFuel fuel : Nat)
    (environment : Environment) (condition : CExpr) (yes no rest : List CStatement) :
    execute layout loopFuel (fuel + 1) environment (.branch condition yes no :: rest) =
      (expression layout environment condition >>= fun actual => truth actual >>= fun selected =>
        execute layout loopFuel fuel environment (if selected then yes else no) >>=
          resume (fun updated => execute layout loopFuel fuel updated rest)) := by
  rw [execute.eq_def]

theorem nested_loop_retains_supplied_header_and_body (layout : Layout) (loopFuel fuel : Nat)
    (environment : Environment) (type : CType) (name : Name) (initial condition step : CExpr)
    (body rest : List CStatement) :
    execute layout loopFuel (fuel + 1) environment
      (.forLoop type name initial condition step body :: rest) =
      (ReadLoops.counted layout loopFuel environment (.forLoop type name initial condition step body)
        >>= fun result => match result with
          | .finished updated => execute layout loopFuel fuel updated rest
          | .exhausted => pure .exhausted) := by
  rw [execute.eq_def]

theorem compound_assignment_retains_supplied_operands (layout : Layout) (loopFuel fuel : Nat)
    (environment : Environment) (operator : BinaryOperator) (location rhs : CExpr)
    (rest : List CStatement) :
    execute layout loopFuel (fuel + 1) environment
      (.compoundAssign operator location rhs :: rest) =
      (assign layout environment (.compoundAssign operator location rhs) >>= fun updated =>
        execute layout loopFuel fuel updated rest) := rfl

theorem counted_retains_initializer_and_outer_scope (layout : Layout)
    (innerFuel bodyFuel fuel : Nat) (environment : Environment) (name : Name)
    (condition step : CExpr) (body : List CStatement) :
    counted layout innerFuel bodyFuel fuel environment
      (.forLoop ⟨"uint32_t".toList, 0⟩ name (.unsignedInteger 0) condition step body) =
      (loop layout innerFuel bodyFuel condition step body fuel
        (Function.update environment name (some (.u32 0))) >>= fun result =>
          pure (restore name (environment name) result)) := rfl

namespace Controls

def layout : Layout := fun _ => none
def environment : Environment := fun name =>
  if name = ['o', 'k'] then some (.bool true)
  else if name = ['i'] then some (.u32 7) else none

theorem branch_keeps_failure_assignment_and_break :
    execute layout 0 3 environment
      [.branch (.bool true) [.assign (.identifier ['o', 'k']) (.bool false), .break] []] =
      pure (.finished (.broken (Function.update environment ['o', 'k'] (some (.bool false))))) := rfl

theorem removed_failure_assignment_changes_observation :
    execute layout 0 3 environment [.branch (.bool true) [.break] []] =
      pure (.finished (.broken environment)) := rfl

theorem break_does_not_execute_later_effect :
    execute layout 0 3 environment [.break, .effect (.call "io".toList [])] =
      pure (.finished (.broken environment)) := rfl

theorem return_does_not_execute_later_effect :
    execute layout 0 3 environment [.return (some (.bool false)), .effect (.call "io".toList [])] =
      pure (.finished (.returned environment (some (.bool false)))) := rfl

theorem compound_or_reads_missing_rhs_even_when_true :
    booleanOrAssignment layout environment ['o', 'k'] (.identifier "missing".toList) =
      CProg.undefined := by
  simp [booleanOrAssignment, expression, resolved, environment]
  exact undefined_bind _

theorem break_skips_invalid_increment :
    loop layout 0 1 (.bool true) (.identifier "missing".toList) [.break] 1 environment =
      pure (.finished (.next environment)) := rfl

theorem return_is_not_normal_loop_completion :
    loop layout 0 1 (.bool true) (.identifier "missing".toList)
      [.return (some (.bool false))] 1 environment =
      pure (.finished (.returned environment (some (.bool false)))) := rfl

theorem body_fuel_is_not_false_return :
    loop layout 0 0 (.bool true) (.postIncrement (.identifier ['i'])) [.return (some (.bool false))]
      1 environment = pure .exhausted := rfl

end Controls

end Mettapedia.Machines.CMemory.ReadBlock
