import Mettapedia.GSLT.LanguageDef.NativeOpsIR
import Mettapedia.GSLT.LanguageDef.NativeOpsTyping

/-!
# Ordered lowering of the authored operational fragment

The output retains the deployed emitter's temporaries, explicit guards,
initialization loops, scopes and jumps. Generated-C admission and operational
preservation/reflection are separate obligations. This construction does not
execute guest functions or select canned semantic bodies.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.NativeLowering

open NativeIR (Atom Place Instruction PureOperation Supply LoopLabels)

structure Expression where
  code : List Instruction
  result : Atom
  supply : Supply
  deriving Repr

structure Arguments where
  code : List Instruction
  results : List Atom
  supply : Supply
  deriving Repr

structure Block where
  code : List Instruction
  scope : Scope
  supply : Supply
  deriving Repr

structure Cases where
  cases : List (BitVec 64 × List Instruction)
  supply : Supply
  deriving Repr

def fieldPosition? : List Parameter → String → Option Nat
  | [], _ => none
  | field :: rest, name =>
      if field.name == name then some 0 else (fieldPosition? rest name).map (· + 1)

def fieldLayout? (interface : Interface) (record name : String) : Option Nat := do
  let record ← lookupRecord interface record
  fieldPosition? record.fields name

def pureTemporary (supply : Supply) (type : NativeType) (operation : PureOperation) : Expression :=
  let next := NativeIR.fresh supply
  ⟨[.temporary next.1 type operation], .temporary next.1 type, next.2⟩

def prependCode (code : List Instruction) (expression : Expression) : Expression :=
  { expression with code := code ++ expression.code }

def checkReference (value : Atom) : List Instruction :=
  [.helper none (.reference value), .checkContext]

def numericGuard (operation : Binary) (right : Atom) : List Instruction :=
  match operation with
  | .word .div => [.checkedNumericGuard .div right]
  | .word .mod => [.checkedNumericGuard .mod right]
  | .word .shl => [.checkedNumericGuard .shl right]
  | .word .shr => [.checkedNumericGuard .shr right]
  | _ => []

mutual
  def expression? (interface : Interface) (scope : Scope) (expression : Expr)
      (supply : Supply) : Option Expression := do
    let type ← inferExpr interface scope expression
    match expression with
    | .word value => some (pureTemporary supply type (.word (NativeWord64.encode value)))
    | .byte value => some (pureTemporary supply type (.byte (NativeWord64.encode value)))
    | .bool value => some (pureTemporary supply type (.bool value))
    | .variable name => some (pureTemporary supply type (.readLocal name))
    | .zero _ | .null _ => some (pureTemporary supply type (.zero type))
    | .new element =>
        let next := NativeIR.fresh supply
        let result := Atom.temporary next.1 type
        some ⟨[.helper (some (.temporary next.1 type)) (.allocate (.word 1) element),
          .checkContext, .write result (.zero element)], result, next.2⟩
    | .newArray element count => do
        let count ← expression? interface scope count supply
        let result := pureTemporary count.supply type (.zero type)
        let counter := NativeIR.fresh result.supply
        some ⟨count.code ++ result.code ++
          [.helper (some (.arrayData result.result element)) (.allocate count.result element),
           .checkContext, .assign (.arrayLength result.result) count.result,
           .forWord counter.1 count.result
             [.writeElement result.result (.iterationCounter counter.1) (.zero element)]],
          result.result, counter.2⟩
    | .field base name => do
        let baseType ← inferExpr interface scope base
        match baseType with
        | .named record => do
            let base ← expression? interface scope base supply
            let index ← fieldLayout? interface record name
            some (prependCode base.code
              (pureTemporary base.supply type (.fieldValue base.result record index)))
        | .ref (.named _) => do
            let location ← location? interface scope (.field base name) supply
            some (prependCode location.code
              (pureTemporary location.supply type (.indirectRead location.result)))
        | _ => none
    | .index array index => do
        let location ← location? interface scope (.index array index) supply
        some (prependCode location.code
          (pureTemporary location.supply type (.indirectRead location.result)))
    | .load reference => do
        let location ← location? interface scope (.load reference) supply
        some (prependCode location.code
          (pureTemporary location.supply type (.indirectRead location.result)))
    | .address location => do
        let location ← location? interface scope location supply
        some (prependCode location.code
          (pureTemporary location.supply type (.copy location.result)))
    | .length array => do
        let array ← expression? interface scope array supply
        some (prependCode array.code (pureTemporary array.supply type (.length array.result)))
    | .slice array start count => do
        let array ← expression? interface scope array supply
        let start ← expression? interface scope start array.supply
        let count ← expression? interface scope count start.supply
        match type with
        | .array element =>
            let result := pureTemporary count.supply type (.zero type)
            some ⟨array.code ++ start.code ++ count.code ++ result.code ++
              [.helper (some (.arrayData result.result element))
                (.slice array.result start.result count.result element),
               .checkContext, .assign (.arrayLength result.result) count.result],
              result.result, result.supply⟩
        | _ => none
    | .call name arguments => do
        let arguments ← arguments? interface scope arguments supply
        let target := if interface.functions.any (fun header => header.name == name) then
          NativeIR.CallTarget.function name else .external name
        if type = .unit then
          some ⟨arguments.code ++ [.call none target arguments.results, .checkContext],
            .unit, arguments.supply⟩
        else
          let next := NativeIR.fresh arguments.supply
          some ⟨arguments.code ++
            [.call (some (.temporary next.1 type)) target arguments.results, .checkContext],
            .temporary next.1 type, next.2⟩
    | .unary operation operand => do
        let operand ← expression? interface scope operand supply
        some (prependCode operand.code
          (pureTemporary operand.supply type (.unary operation operand.result)))
    | .binary .and left right | .binary .or left right => do
        let left ← expression? interface scope left supply
        let result := pureTemporary left.supply type (.copy left.result)
        let right ← expression? interface scope right result.supply
        let condition := match expression with
          | .binary .and _ _ => NativeIR.Condition.value result.result
          | _ => .negated result.result
        let destination := Place.temporary (NativeIR.fresh left.supply).1 type
        some ⟨left.code ++ result.code ++
          [.branch condition (right.code ++ [.assign destination right.result]) []],
          result.result, right.supply⟩
    | .binary operation left right => do
        let left ← expression? interface scope left supply
        let right ← expression? interface scope right left.supply
        some (prependCode (left.code ++ right.code ++ numericGuard operation right.result)
          (pureTemporary right.supply type (.binary operation left.result right.result)))
  termination_by 2 * sizeOf expression + 1
  decreasing_by
    all_goals simp +unfoldPartialApp +zetaDelta -failIfUnchanged [-Nat.mul_lt_mul_left]
    all_goals omega

  def location? (interface : Interface) (scope : Scope) (location : Expr)
      (supply : Supply) : Option Expression := do
    let type ← inferLocation interface scope location
    match location with
    | .variable name => some ⟨[], .localAddress name type, supply⟩
    | .field base name => do
        let baseType ← inferExpr interface scope base
        match baseType with
        | .named record => do
            let base ← location? interface scope base supply
            let index ← fieldLayout? interface record name
            some (prependCode base.code
              (pureTemporary base.supply (.ref type) (.fieldAddress base.result record index)))
        | .ref (.named record) => do
            let base ← expression? interface scope base supply
            let index ← fieldLayout? interface record name
            some (prependCode (base.code ++ checkReference base.result)
              (pureTemporary base.supply (.ref type) (.fieldAddress base.result record index)))
        | _ => none
    | .index array index => do
        let array ← expression? interface scope array supply
        let index ← expression? interface scope index array.supply
        let next := NativeIR.fresh index.supply
        some ⟨array.code ++ index.code ++
          [.helper (some (.temporary next.1 (.ref type))) (.index array.result index.result type),
           .checkContext], .temporary next.1 (.ref type), next.2⟩
    | .load reference => do
        let reference ← expression? interface scope reference supply
        some ⟨reference.code ++ checkReference reference.result, reference.result, reference.supply⟩
    | _ => none
  termination_by 2 * sizeOf location
  decreasing_by
    all_goals simp +unfoldPartialApp +zetaDelta -failIfUnchanged [-Nat.mul_lt_mul_left]
    all_goals omega

  def arguments? (interface : Interface) (scope : Scope) (arguments : List Expr)
      (supply : Supply) : Option Arguments :=
    match arguments with
    | [] => some ⟨[], [], supply⟩
    | first :: rest => do
        let first ← expression? interface scope first supply
        let rest ← arguments? interface scope rest first.supply
        some ⟨first.code ++ rest.code, first.result :: rest.results, rest.supply⟩
  termination_by 2 * sizeOf arguments
  decreasing_by
    all_goals simp +unfoldPartialApp +zetaDelta -failIfUnchanged [-Nat.mul_lt_mul_left]
    all_goals omega
end

mutual
  def block? (interface : Interface) (result : NativeType) (loops : List LoopLabels)
      (scope : Scope) (body : List Statement) (supply : Supply) : Option Block :=
    match body with
    | [] => some ⟨[], scope, supply⟩
    | first :: rest => do
        let first ← statement? interface result loops scope first supply
        let rest ← block? interface result loops first.scope rest first.supply
        some ⟨first.code ++ rest.code, rest.scope, rest.supply⟩
  termination_by sizeOf body
  decreasing_by all_goals simp_wf; all_goals omega

  def statement? (interface : Interface) (result : NativeType) (loops : List LoopLabels)
      (scope : Scope) (statement : Statement) (supply : Supply) : Option Block := do
    let nextScope ← checkStatement interface result loops.length scope statement
    match statement with
    | .declare name type initializer => do
        let value ← expression? interface scope initializer supply
        some ⟨value.code ++ [.declareLocal name type value.result], nextScope, value.supply⟩
    | .set location value => do
        let location ← location? interface scope location supply
        let value ← expression? interface scope value location.supply
        some ⟨location.code ++ value.code ++ [.write location.result value.result],
          nextScope, value.supply⟩
    | .branch condition whenTrue whenFalse => do
        let condition ← expression? interface scope condition supply
        let whenTrue ← block? interface result loops scope whenTrue condition.supply
        let whenFalse ← block? interface result loops scope whenFalse whenTrue.supply
        some ⟨condition.code ++
          [.branch (.value condition.result) whenTrue.code whenFalse.code], nextScope, whenFalse.supply⟩
    | .while condition body => do
        let entry := NativeIR.fresh supply
        let exit := NativeIR.fresh entry.2
        let labels : LoopLabels := ⟨⟨.entry, entry.1⟩, ⟨.exit, exit.1⟩⟩
        let condition ← expression? interface scope condition exit.2
        let body ← block? interface result (labels :: loops) scope body condition.supply
        some ⟨[.label labels.entry,
          .scope (condition.code ++ [.branch (.negated condition.result) [.jump labels.exit] []] ++
            body.code ++ [.jump labels.entry]), .label labels.exit], nextScope, body.supply⟩
    | .switch selector cases otherwise => do
        let selector ← expression? interface scope selector supply
        let cases ← cases? interface result loops scope cases selector.supply
        let otherwise ← block? interface result loops scope otherwise cases.supply
        some ⟨selector.code ++ [.switch selector.result cases.cases otherwise.code],
          nextScope, otherwise.supply⟩
    | .break => match loops with
        | [] => none
        | current :: _ => some ⟨[.jump current.exit], nextScope, supply⟩
    | .continue => match loops with
        | [] => none
        | current :: _ => some ⟨[.jump current.entry], nextScope, supply⟩
    | .effect expression => do
        let expression ← expression? interface scope expression supply
        some ⟨expression.code, nextScope, expression.supply⟩
    | .free expression => do
        let type ← inferExpr interface scope expression
        let expression ← expression? interface scope expression supply
        match type with
        | .ref element | .array element =>
            some ⟨expression.code ++ [.helper none (.release expression.result element), .checkContext],
              nextScope, expression.supply⟩
        | _ => none
    | .return none => some ⟨[.return .unit], nextScope, supply⟩
    | .return (some expression) => do
        let expression ← expression? interface scope expression supply
        some ⟨expression.code ++ [.return expression.result], nextScope, expression.supply⟩
    | .block body => do
        let body ← block? interface result loops scope body supply
        some ⟨[.scope body.code], nextScope, body.supply⟩
  termination_by sizeOf statement
  decreasing_by all_goals simp_wf; all_goals omega

  def cases? (interface : Interface) (result : NativeType) (loops : List LoopLabels)
      (scope : Scope) (cases : List (NativeWord64.Word × List Statement)) (supply : Supply) :
      Option Cases :=
    match cases with
    | [] => some ⟨[], supply⟩
    | (selector, body) :: rest => do
        let body ← block? interface result loops scope body supply
        let rest ← cases? interface result loops scope rest body.supply
        some ⟨(NativeWord64.encode selector, body.code) :: rest.cases, rest.supply⟩
  termination_by sizeOf cases
  decreasing_by all_goals simp_wf; all_goals omega
end

def function? (interface : Interface) (function : NativeOps.Function) : Option NativeIR.Function := do
  if !checkFunction interface function then none else
    let scope := function.header.parameters.map (fun parameter => (parameter.name, parameter.type))
    let body ← block? interface function.header.result [] scope function.body ⟨0⟩
    let suffix := if function.header.result = .unit then [Instruction.return .unit] else []
    some ⟨function.header, [.checkContextExists, .checkContext] ++ body.code ++ suffix,
      body.supply.next⟩

def program? (program : NativeOps.Program) : Option NativeIR.Program := do
  let functions ← program.functions.mapM (function? program.interface)
  some ⟨program.name, program.interface, functions⟩

theorem literal_temporary_is_fresh (supply : Supply) (value : NativeWord64.Word) :
    (pureTemporary supply .word (.word (NativeWord64.encode value))).result =
      .temporary (supply.next + 1) .word := rfl

theorem unchecked_numeric_operations_have_no_refusal_guard (right : Atom) :
    numericGuard (.word .add) right = [] ∧ numericGuard (.word .mul) right = [] := ⟨rfl, rfl⟩

theorem division_retains_explicit_refusal_guard (right : Atom) :
    numericGuard (.word .div) right = [.checkedNumericGuard .div right] := rfl

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeLowering
