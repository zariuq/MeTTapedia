import Mettapedia.GSLT.LanguageDef.NativeOpsSyntax

/-!
# Admission of typed native expressions and lexical blocks

The checks follow the operational source compiler's required fragment.  An
address of a field of a value record requires a genuine location for the
record; a reference record permits an evaluated base.  Blocks extend local
scope only within the block, and declarations cannot shadow an active name.
Switches do not create a loop scope for `break` and `continue`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

def lookupVariable (scope : Scope) (name : String) : Option NativeType :=
  (scope.find? (fun binding => binding.1 == name)).map Prod.snd

mutual
  def inferExpr (interface : Interface) (scope : Scope) : Expr → Option NativeType
    | .word _ => some .word
    | .byte _ => some .byte
    | .bool _ => some .bool
    | .variable name => lookupVariable scope name
    | .zero type => if validType interface type true then some type else none
    | .null type => match type with
        | .ref _ => if validType interface type false then some type else none
        | _ => none
    | .new type => match type with
        | .ref _ => none
        | _ => if validType interface type true then some (.ref type) else none
    | .newArray element count => do
        if !(validType interface element true) then none else
          let countType ← inferExpr interface scope count
          if countType = .word then some (.array element) else none
    | .field base field => do
        let baseType ← inferExpr interface scope base
        match baseType with
        | .named record | .ref (.named record) => lookupField interface record field
        | _ => none
    | .index array index => do
        let arrayType ← inferExpr interface scope array
        let indexType ← inferExpr interface scope index
        match arrayType with
        | .array element => if indexType = .word then some element else none
        | _ => none
    | .length array => do
        let arrayType ← inferExpr interface scope array
        match arrayType with
        | .array _ => some .word
        | _ => none
    | .slice array start count => do
        let arrayType ← inferExpr interface scope array
        let startType ← inferExpr interface scope start
        let countType ← inferExpr interface scope count
        match arrayType with
        | .array _ => if startType = .word ∧ countType = .word then some arrayType else none
        | _ => none
    | .address location => (inferLocation interface scope location).map NativeType.ref
    | .load reference => do
        let referenceType ← inferExpr interface scope reference
        match referenceType with
        | .ref element => if validType interface element true then some element else none
        | _ => none
    | .call name arguments => do
        let header ← lookupFunction interface name
        let argumentsTypes ← inferExprList interface scope arguments
        if argumentsTypes = header.parameters.map Parameter.type then some header.result else none
    | .unary operation operand => do
        let type ← inferExpr interface scope operand
        unaryType operation type
    | .binary operation left right => do
        let leftType ← inferExpr interface scope left
        let rightType ← inferExpr interface scope right
        if leftType = rightType then binaryType operation leftType else none
  termination_by expression => 2 * sizeOf expression
  decreasing_by
    all_goals simp +unfoldPartialApp +zetaDelta -failIfUnchanged [-Nat.mul_lt_mul_left]
    all_goals omega

  def inferExprList (interface : Interface) (scope : Scope) : List Expr → Option (List NativeType)
    | [] => some []
    | expression :: rest => do
        let type ← inferExpr interface scope expression
        let tail ← inferExprList interface scope rest
        pure (type :: tail)
  termination_by expressions => 2 * sizeOf expressions
  decreasing_by
    all_goals simp +unfoldPartialApp +zetaDelta -failIfUnchanged [-Nat.mul_lt_mul_left]
    all_goals omega

  def inferLocation (interface : Interface) (scope : Scope) : Expr → Option NativeType
    | .variable name => lookupVariable scope name
    | .field base field => do
        let baseType ← inferExpr interface scope base
        match baseType with
        | .ref (.named record) => lookupField interface record field
        | .named record => do
            let _ ← inferLocation interface scope base
            lookupField interface record field
        | _ => none
    | .index array index => inferExpr interface scope (.index array index)
    | .load reference => inferExpr interface scope (.load reference)
    | _ => none
  termination_by expression => 2 * sizeOf expression + 1
  decreasing_by
    all_goals simp +unfoldPartialApp +zetaDelta -failIfUnchanged [-Nat.mul_lt_mul_left]
    all_goals omega
end

mutual
  def checkBlock (interface : Interface) (result : NativeType) (loops : Nat)
      (scope : Scope) : List Statement → Option Scope
    | [] => some scope
    | statement :: rest => do
        let next ← checkStatement interface result loops scope statement
        checkBlock interface result loops next rest
  termination_by body => sizeOf body
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def checkStatement (interface : Interface) (result : NativeType) (loops : Nat)
      (scope : Scope) : Statement → Option Scope
    | .declare name type initializer => do
        if (lookupVariable scope name).isSome || !(validType interface type true) then none else
          let actual ← inferExpr interface scope initializer
          if actual = type then some ((name, type) :: scope) else none
    | .set location value => do
        let locationType ← inferLocation interface scope location
        let valueType ← inferExpr interface scope value
        if locationType = valueType then some scope else none
    | .branch condition thenBody elseBody => do
        let conditionType ← inferExpr interface scope condition
        if conditionType ≠ .bool then none else
          let _ ← checkBlock interface result loops scope thenBody
          let _ ← checkBlock interface result loops scope elseBody
          some scope
    | .while condition body => do
        let conditionType ← inferExpr interface scope condition
        if conditionType ≠ .bool then none else
          let _ ← checkBlock interface result (loops + 1) scope body
          some scope
    | .switch selector cases default => do
        let selectorType ← inferExpr interface scope selector
        if selectorType ≠ .word ∨ ¬(cases.map Prod.fst).Nodup then none else
          let _ ← checkCases interface result loops scope cases
          let _ ← checkBlock interface result loops scope default
          some scope
    | .break | .continue => if loops = 0 then none else some scope
    | .effect expression => do
        let _ ← inferExpr interface scope expression
        some scope
    | .free expression => do
        let type ← inferExpr interface scope expression
        match type with
        | .ref element | .array element =>
            if validType interface element true then some scope else none
        | _ => none
    | .return none => if result = .unit then some scope else none
    | .return (some expression) => do
        let type ← inferExpr interface scope expression
        if type = result ∧ result ≠ .unit then some scope else none
    | .block body => do
        let _ ← checkBlock interface result loops scope body
        some scope
  termination_by statement => sizeOf statement
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def checkCases (interface : Interface) (result : NativeType) (loops : Nat)
      (scope : Scope) : List (NativeWord64.Word × List Statement) → Option Unit
    | [] => some ()
    | (_, body) :: rest => do
        let _ ← checkBlock interface result loops scope body
        checkCases interface result loops scope rest
  termination_by cases => sizeOf cases
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

mutual
  def returnsBlock : List Statement → Bool
    | [] => false
    | statement :: rest => returnsStatement statement || returnsBlock rest
  termination_by body => sizeOf body
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def returnsStatement : Statement → Bool
    | .return _ => true
    | .block body => returnsBlock body
    | .branch _ thenBody elseBody => returnsBlock thenBody && returnsBlock elseBody
    | .switch _ cases default => returnsBlock default && returnsCases cases
    | _ => false
  termination_by statement => sizeOf statement
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def returnsCases : List (NativeWord64.Word × List Statement) → Bool
    | [] => true
    | (_, body) :: rest => returnsBlock body && returnsCases rest
  termination_by cases => sizeOf cases
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

def checkFunction (interface : Interface) (function : Function) : Bool :=
  let header := function.header
  (header.parameters.map Parameter.name).Nodup &&
    header.parameters.all (fun parameter => validType interface parameter.type true) &&
    validType interface header.result (header.result != .unit) &&
    (checkBlock interface header.result 0
      (header.parameters.map fun parameter => (parameter.name, parameter.type)) function.body).isSome &&
    (header.result == .unit || returnsBlock function.body)

end Mettapedia.GSLT.LanguageDef.NativeOps
