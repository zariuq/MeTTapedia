import Mettapedia.GSLT.LanguageDef.NativeOpsCLocalStore

/-!
# Local retained-source control over typed identity arrays

The block interpreter composes local declarations, scalar assignments,
conditional continuations, unsigned switches, scoped blocks, counted read loops,
post-index stores and explicit break/return completion. Switches retain arm order
and fall-through; a switch consumes its own break but not a return.
Declarations restore their previous binding when their
remaining scope completes. No selected branch is synthesized from an expected
result. The counted-loop fuel is derived from its immutable typed upper bound;
the loop still executes its own condition and body.

Physical pointer, lifetime, layout and synchronized-read realization remain
outside the typed field/array service. Statement proof fuel and invalid reads
are not allocation failure or a completed C false return.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.LocalBlock

open ScalarRead

variable {Ptr : Type} [DecidableEq Ptr]

inductive Flow (Ptr : Type) where
  | next (environment : Environment Ptr)
  | broken (environment : Environment Ptr)
  | returned (environment : Environment Ptr) (value : Option (Value Ptr))

inductive Result (Ptr : Type) where
  | finished (value : Option (Flow Ptr))
  | exhausted

def resume (continuation : Environment Ptr → Result Ptr) : Result Ptr → Result Ptr
  | .finished (some (.next environment)) => continuation environment
  | result => result

def switchResume (continuation : Environment Ptr → Result Ptr) : Result Ptr → Result Ptr
  | .finished (some (.next environment)) | .finished (some (.broken environment)) =>
      continuation environment
  | result => result

/-- Selection reads the supplied case constants. Each braced arm has its own
scope; reaching its end falls through to the next arm. Missing or incompatible
reads do not select the default. Only unsigned selector values are admitted. -/
def switchBody? (fields : FieldReader Ptr) (environment : Environment Ptr)
    (selector : Value Ptr) (cases : List (CExpr × List CStatement))
    (otherwise : List CStatement) : Option (List CStatement) :=
  match cases with
  | [] => some [.block otherwise]
  | (key, body) :: rest => do
      let value ← expression environment fields key
      let selected ← equal? selector value
      if selected then some (.block body :: rest.map (fun arm => .block arm.2) ++ [.block otherwise])
      else switchBody? fields environment selector rest otherwise

def selectedSwitch? (fields : FieldReader Ptr) (environment : Environment Ptr)
    (selector : CExpr) (cases : List (CExpr × List CStatement))
    (otherwise : List CStatement) : Option (List CStatement) := do
  let value ← expression environment fields selector
  match value with
  | .unsigned _ | .unsigned64 _ => switchBody? fields environment value cases otherwise
  | _ => none

def restore (name : Name) (previous : Option (Value Ptr)) : Result Ptr → Result Ptr
  | .finished (some (.next environment)) => .finished (some (.next
      (Function.update environment name previous)))
  | .finished (some (.broken environment)) => .finished (some (.broken
      (Function.update environment name previous)))
  | .finished (some (.returned environment value)) => .finished (some (.returned
      (Function.update environment name previous) value))
  | result => result

def declaredValue? (type : CType) (value : Value Ptr) : Option (Value Ptr) :=
  if type = ⟨"bool".toList, 0⟩ then (truth? value).map Value.boolean
  else if type = ⟨"int".toList, 0⟩ then
    match value with
    | .signed value => some (.signed value)
    | _ => none
  else if type = ⟨"uint32_t".toList, 0⟩ then
    match value with
    | .unsigned value => some (.unsigned value)
    | _ => none
  else if type = ⟨"Space".toList, 1⟩ then
    match value with
    | .identity value => some (.identity value)
    | _ => none
  else none

omit [DecidableEq Ptr] in
theorem declared_signed_retains_actual_value (value : Int32) :
    declaredValue? (Ptr := Ptr) ⟨"int".toList, 0⟩ (.signed value) =
      some (.signed value) := rfl

def readLoopFuel (fields : FieldReader Ptr) (environment : Environment Ptr) : CStatement → Nat
  | .forLoop _ _ _ (.binary .and (.binary .lt _ bound) _) _ _ =>
      match expression environment fields bound with
      | some (.unsigned count) => count.toNat
      | _ => 0
  | _ => 0

def assign (fields : FieldReader Ptr) (environment : Environment Ptr)
    (statement : CStatement) : Option (Environment Ptr) :=
  match statement with
  | .assign (.identifier name) value => assignment environment fields (.identifier name) value
  | .compoundAssign .bitOr location value => booleanOrAssignment environment fields location value
  | .compoundAssign .mul location value =>
      unsignedCompoundAssignment environment fields .mul location value
  | _ => LocalStore.execute environment statement

def execute (fields : FieldReader Ptr) (fuel : Nat) (environment : Environment Ptr)
    (body : List CStatement) : Result Ptr :=
  match body with
  | [] => .finished (some (.next environment))
  | statement :: rest => match fuel with
    | 0 => .exhausted
    | fuel + 1 => match statement with
      | .empty => execute fields fuel environment rest
      | .declare type name value =>
          match (expression environment fields value).bind (declaredValue? type) with
          | none => .finished none
          | some initial => restore name (environment name)
              (execute fields fuel (Function.update environment name (some initial)) rest)
      | .assign _ _ => match assign fields environment statement with
          | none => .finished none
          | some updated => execute fields fuel updated rest
      | .compoundAssign _ _ _ => match assign fields environment statement with
          | none => .finished none
          | some updated => execute fields fuel updated rest
      | .branch condition yes no =>
          match (expression environment fields condition).bind truth? with
          | none => .finished none
          | some selected => resume (fun updated => execute fields fuel updated rest)
              (execute fields fuel environment (if selected then yes else no))
      | .block selected => resume (fun updated => execute fields fuel updated rest)
          (execute fields fuel environment selected)
      | .switch selector cases otherwise =>
          match selectedSwitch? fields environment selector cases otherwise with
          | none => .finished none
          | some selected => switchResume (fun updated => execute fields fuel updated rest)
              (execute fields fuel environment selected)
      | .forLoop _ _ _ _ _ _ =>
          match countedLoop fields (readLoopFuel fields environment statement) environment statement with
          | none | some (.finished none) => .finished none
          | some (.finished (some updated)) => execute fields fuel updated rest
          | some .exhausted => .exhausted
      | .break => .finished (some (.broken environment))
      | .return none => .finished (some (.returned environment none))
      | .return (some value) => match expression environment fields value with
          | none => .finished none
          | some returned => .finished (some (.returned environment (some returned)))
      | _ => .finished none

theorem declaration_executes_retained_scope (fields : FieldReader Ptr) (fuel : Nat)
    (environment : Environment Ptr) (type : CType) (name : Name) (value : CExpr)
    (rest : List CStatement) (initial : Value Ptr)
    (read : (expression environment fields value).bind (declaredValue? type) = some initial) :
    execute fields (fuel + 1) environment (.declare type name value :: rest) =
      restore name (environment name)
        (execute fields fuel (Function.update environment name (some initial)) rest) := by
  rw [execute.eq_def]
  dsimp only
  rw [read]

theorem undefined_declaration_has_no_completed_flow (fields : FieldReader Ptr) (fuel : Nat)
    (environment : Environment Ptr) (type : CType) (name : Name) (value : CExpr)
    (rest : List CStatement)
    (read : (expression environment fields value).bind (declaredValue? type) = none) :
    execute fields (fuel + 1) environment (.declare type name value :: rest) =
      .finished none := by
  rw [execute.eq_def]
  dsimp only
  rw [read]

theorem assignment_executes_actual_result (fields : FieldReader Ptr) (fuel : Nat)
    (environment updated : Environment Ptr) (location value : CExpr) (rest : List CStatement)
    (assigned : assign fields environment (.assign location value) = some updated) :
    execute fields (fuel + 1) environment (.assign location value :: rest) =
      execute fields fuel updated rest := by
  rw [execute.eq_def]
  dsimp only
  rw [assigned]

theorem compound_assignment_executes_actual_result (fields : FieldReader Ptr) (fuel : Nat)
    (environment updated : Environment Ptr) (operator : BinaryOperator)
    (location value : CExpr) (rest : List CStatement)
    (assigned : assign fields environment (.compoundAssign operator location value) = some updated) :
    execute fields (fuel + 1) environment (.compoundAssign operator location value :: rest) =
      execute fields fuel updated rest := by
  rw [execute.eq_def]
  dsimp only
  rw [assigned]

omit [DecidableEq Ptr] in
theorem scope_restoration_keeps_other_assignment (environment : Environment Ptr)
    (localName otherName : Name) (localValue otherValue : Option (Value Ptr))
    (different : localName ≠ otherName) :
    Function.update (Function.update (Function.update environment localName localValue)
      otherName otherValue) localName (environment localName) =
      Function.update environment otherName otherValue := by
  rw [Function.update_comm different, Function.update_idem,
    Function.update_comm different.symm, Function.update_eq_self]

theorem branch_executes_retained_continuation (fields : FieldReader Ptr) (fuel : Nat)
    (environment : Environment Ptr) (condition : CExpr) (yes no rest : List CStatement)
    (selected : Bool)
    (read : (expression environment fields condition).bind truth? = some selected) :
    execute fields (fuel + 1) environment (.branch condition yes no :: rest) =
      resume (fun updated => execute fields fuel updated rest)
        (execute fields fuel environment (if selected then yes else no)) := by
  rw [execute.eq_def]
  dsimp only
  rw [read]

theorem counted_loop_executes_actual_result (fields : FieldReader Ptr) (fuel : Nat)
    (environment updated : Environment Ptr) (type : CType) (counter : Name)
    (initial condition step : CExpr) (body rest : List CStatement)
    (completed : countedLoop fields
      (readLoopFuel fields environment (.forLoop type counter initial condition step body))
      environment (.forLoop type counter initial condition step body) =
      some (.finished (some updated))) :
    execute fields (fuel + 1) environment (.forLoop type counter initial condition step body :: rest) =
      execute fields fuel updated rest := by
  rw [execute.eq_def]
  dsimp only
  rw [completed]

theorem switch_executes_selected_body (fields : FieldReader Ptr) (fuel : Nat)
    (environment : Environment Ptr) (selector : CExpr)
    (cases : List (CExpr × List CStatement)) (otherwise selected rest : List CStatement)
    (read : selectedSwitch? fields environment selector cases otherwise = some selected) :
    execute fields (fuel + 1) environment (.switch selector cases otherwise :: rest) =
      switchResume (fun updated => execute fields fuel updated rest)
        (execute fields fuel environment selected) := by
  rw [execute.eq_def]
  dsimp only
  rw [read]

theorem undefined_switch_has_no_completed_flow (fields : FieldReader Ptr) (fuel : Nat)
    (environment : Environment Ptr) (selector : CExpr)
    (cases : List (CExpr × List CStatement)) (otherwise rest : List CStatement)
    (read : selectedSwitch? fields environment selector cases otherwise = none) :
    execute fields (fuel + 1) environment (.switch selector cases otherwise :: rest) =
      .finished none := by
  rw [execute.eq_def]
  dsimp only
  rw [read]

theorem empty_body_completes (fields : FieldReader Ptr) (fuel : Nat)
    (environment : Environment Ptr) :
    execute fields fuel environment [] = .finished (some (.next environment)) := by
  rw [execute.eq_def]

/-- Empty fall-through labels reach the one retained return body. Neither
later arms nor the outer continuation execute after that return. -/
theorem empty_blocks_then_return (reader : FieldReader Ptr)
    (locals : Environment Ptr) (fuel count : Nat) (value : CExpr)
    (answer : Value Ptr) (rest : List CStatement)
    (read : expression locals reader value = some answer) :
    execute reader (fuel + count + 2) locals
      (List.replicate count (.block []) ++ .block [.return (some value)] :: rest) =
      .finished (some (.returned locals (some answer))) := by
  induction count with
  | zero =>
      simp only [List.replicate_zero, List.nil_append, Nat.add_zero]
      rw [execute.eq_def]
      dsimp only
      rw [execute.eq_def]
      dsimp only
      rw [read]
      rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      rw [execute.eq_def]
      dsimp only
      rw [empty_body_completes]
      exact ih

theorem branch_returns_expression (reader : FieldReader Ptr)
    (locals : Environment Ptr) (fuel : Nat) (condition value : CExpr)
    (selected : Bool) (answer : Value Ptr) (rest : List CStatement)
    (readCondition : (expression locals reader condition).bind truth? = some selected)
    (readAnswer : expression locals reader value = some answer) :
    execute reader (fuel + 2) locals
      (.branch condition [.return (some value)] [] :: rest) =
      if selected then .finished (some (.returned locals (some answer)))
      else execute reader (fuel + 1) locals rest := by
  rw [branch_executes_retained_continuation reader (fuel + 1)
    locals condition [.return (some value)] [] rest selected readCondition]
  cases selected with
  | false => rfl
  | true =>
      change resume _
        (execute reader (fuel + 1) locals [.return (some value)]) = _
      rw [execute.eq_def]
      dsimp only
      rw [readAnswer]
      rfl

theorem local_store_executes_actual_result (fields : FieldReader Ptr) (fuel : Nat)
    (environment : Environment Ptr) (site : LocalStore.Site) :
    execute fields (fuel + 1) environment [site.statement] =
      .finished ((LocalStore.execute environment site.statement).map Flow.next) := by
  rw [execute.eq_def]
  dsimp only [LocalStore.Site.statement, assign]
  change (match LocalStore.execute environment site.statement with
    | none => Result.finished none
    | some updated => execute fields fuel updated []) =
      Result.finished ((LocalStore.execute environment site.statement).map Flow.next)
  cases completed : LocalStore.execute environment site.statement <;>
    simp only [empty_body_completes, Option.map_none, Option.map_some]

namespace Controls

def fields : FieldReader Nat := fun _ _ => none
def environment : Environment Nat := fun name =>
  if name = "ok".toList then some (.boolean true)
  else if name = "dependency".toList then some (.identity (some 7)) else none

def observeOk : Result Nat → Option Bool
  | .finished (some (.next environment)) | .finished (some (.broken environment)) =>
      (environment "ok".toList).bind truth?
  | _ => none

theorem chosen_failure_branch_keeps_assignment_and_break :
    observeOk (execute fields 3 environment
      [.branch (.bool true)
        [.assign (.identifier "ok".toList) (.bool false), .break] []]) = some false := rfl

theorem omitted_failure_assignment_changes_observation :
    observeOk (execute fields 3 environment [.branch (.bool true) [.break] []]) = some true := rfl

theorem break_does_not_execute_remaining_statements :
    observeOk (execute fields 2 environment
      [.break, .assign (.identifier "ok".toList) (.bool false)]) = some true := rfl

theorem declaration_restores_outer_binding :
    (match execute fields 2 environment
      [.declare ⟨"Space".toList, 1⟩ "dependency".toList .null] with
      | .finished (some (.next completed)) => completed "dependency".toList
      | _ => none) = some (.identity (some 7)) := rfl

theorem false_return_is_not_undefined_read :
    execute fields 1 environment [.return (some (.bool false))] =
      .finished (some (.returned environment (some (.boolean false)))) ∧
    execute fields 1 environment [.return (some (.identifier "missing".toList))] =
      .finished none := by constructor <;> rfl

theorem compound_or_keeps_existing_true :
    observeOk (execute fields 1 environment
      [.compoundAssign .bitOr (.identifier "ok".toList) (.bool false)]) = some true := rfl

theorem replacing_compound_or_with_assignment_loses_existing_true :
    observeOk (execute fields 1 environment
      [.assign (.identifier "ok".toList) (.bool false)]) = some false := rfl

theorem compound_or_does_not_short_circuit_missing_rhs :
    execute fields 1 environment
      [.compoundAssign .bitOr (.identifier "ok".toList) (.identifier "missing".toList)] =
      .finished none := rfl

theorem unsupported_compound_operator_is_not_boolean_or :
    execute fields 1 environment
      [.compoundAssign .mul (.identifier "ok".toList) (.bool false)] = .finished none := rfl

theorem switch_break_resumes_outer_continuation :
    observeOk (execute fields 5 environment
      [.switch (.unsignedInteger 1) [(.unsignedInteger 1, [.break])]
        [.assign (.identifier "ok".toList) (.bool true)],
       .assign (.identifier "ok".toList) (.bool false)]) = some false := rfl

theorem empty_label_falls_through_to_return_once :
    execute fields 6 environment
      [.switch (.unsignedInteger 1)
        [(.unsignedInteger 1, []), (.unsignedInteger 2, [.return (some (.bool true))])]
        [.return (some (.bool false))]] =
      .finished (some (.returned environment (some (.boolean true)))) := rfl

theorem fallthrough_keeps_each_arm_scope :
    execute fields 8 environment
      [.switch (.unsignedInteger 1)
        [(.unsignedInteger 1, [.declare ⟨"bool".toList, 0⟩ "ok".toList (.bool false)]),
         (.unsignedInteger 2, [.return (some (.identifier "ok".toList))])]
        []] = .finished (some (.returned environment (some (.boolean true)))) := by
  change Result.finished (some (.returned
    (Function.update (Function.update environment "ok".toList (some (.boolean false)))
      "ok".toList (environment "ok".toList))
    (some (.boolean true)))) = _
  rw [Function.update_idem, Function.update_eq_self]

theorem missing_switch_case_does_not_select_default :
    execute fields 4 environment
      [.switch (.unsignedInteger 1) [(.identifier "missing".toList, [])]
        [.return (some (.bool true))]] = .finished none := rfl

theorem unknown_numeric_selector_selects_actual_default :
    execute fields 4 environment
      [.switch (.unsignedInteger 3)
        [(.unsignedInteger 1, [.return (some (.bool true))])]
        [.return (some (.bool false))]] =
      .finished (some (.returned environment (some (.boolean false)))) := rfl

end Controls

#print axioms Controls.chosen_failure_branch_keeps_assignment_and_break
#print axioms declaration_executes_retained_scope
#print axioms undefined_declaration_has_no_completed_flow
#print axioms assignment_executes_actual_result
#print axioms scope_restoration_keeps_other_assignment
#print axioms branch_executes_retained_continuation
#print axioms counted_loop_executes_actual_result
#print axioms empty_body_completes
#print axioms local_store_executes_actual_result
#print axioms Controls.omitted_failure_assignment_changes_observation
#print axioms Controls.break_does_not_execute_remaining_statements
#print axioms Controls.declaration_restores_outer_binding
#print axioms Controls.false_return_is_not_undefined_read
#print axioms compound_assignment_executes_actual_result
#print axioms Controls.compound_or_keeps_existing_true
#print axioms Controls.replacing_compound_or_with_assignment_loses_existing_true
#print axioms Controls.compound_or_does_not_short_circuit_missing_rhs
#print axioms Controls.unsupported_compound_operator_is_not_boolean_or
#print axioms switch_executes_selected_body
#print axioms undefined_switch_has_no_completed_flow
#print axioms Controls.switch_break_resumes_outer_continuation
#print axioms Controls.empty_label_falls_through_to_return_once
#print axioms Controls.fallthrough_keeps_each_arm_scope
#print axioms Controls.missing_switch_case_does_not_select_default
#print axioms Controls.unknown_numeric_selector_selects_actual_default

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.LocalBlock
