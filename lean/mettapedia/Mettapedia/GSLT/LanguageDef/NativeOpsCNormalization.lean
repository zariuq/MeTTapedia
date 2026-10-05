import Mettapedia.GSLT.LanguageDef.NativeOpsCValues
import Mettapedia.GSLT.LanguageDef.NativeOpsZeroNormalization

/-!
# Control and storage normalization of the emitted C fragment

This reader consumes actual target syntax. It checks the typed context guards,
raw default returns, shared helper operands, external catalogue symbols,
lexical scopes, loop labels and switch exits. It contains no guest semantic
body and no dispatch on guest function names. Operational adequacy is separate
from successful artifact normalization.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

open NativeIR (Atom Place Instruction MemoryOperation CallTarget)

deriving instance DecidableEq for NativeIR.PureOperation
deriving instance DecidableEq for NativeIR.MemoryOperation

structure Normalized where
  code : List Instruction
  environment : Environment
  deriving Repr

def ctxExpression (expression : CExpr) : Bool := match expression with
  | .identifier name => name == "ctx".toList
  | _ => false

def arrayComponent? (representation : Representation) (environment : Environment)
    (expression : CExpr) (field : Name) : Option (Atom × NativeType) := do
  match expression with
  | .field value name false =>
      if name != field then none else do
        let value ← atom? representation environment value
        match value.type with | .array element => some (value, element) | _ => none
  | _ => none

def arrayPair? (representation : Representation) (environment : Environment)
    (data length : CExpr) : Option (Atom × NativeType) := do
  let first ← arrayComponent? representation environment data "data".toList
  let second ← arrayComponent? representation environment length "length".toList
  if first = second then some first else none

def sizeMatches (representation : Representation) (element : NativeType) (expression : CExpr) : Bool :=
  match expression with
  | .sizeOf type => sourceType? representation element == some type
  | _ => false

def freePointer? (representation : Representation) (environment : Environment)
    (pointer count : CExpr) (element : NativeType) : Option Atom :=
  match arrayPair? representation environment pointer count with
  | some (array, declared) => if declared = element then some array else none
  | none => do
      let pointer ← typedAtom? representation environment pointer (.ref element)
      match count with
      | .conditional (.binary .eq compared .null) (.word zero) (.word one) =>
          let compared ← typedAtom? representation environment compared (.ref element)
          if compared = pointer && zero = 0 && one = 1 then some pointer else none
      | _ => none

def memoryCall? (representation : Representation) (environment : Environment)
    (expression : CExpr) (result : NativeType) : Option MemoryOperation :=
  match expression with
  | .call name [context, pointer] =>
      if name == "cetta_gslt_native_ops_reference_v1".toList && ctxExpression context && result = .unit then do
        let pointer ← atom? representation environment pointer
        match pointer.type with | .ref _ => some (.reference pointer) | _ => none
      else none
  | .call name [context, count, width] =>
      if name == "cetta_gslt_native_ops_alloc_v1".toList && ctxExpression context then
        match result with
        | .ref element => do
            let count ← typedAtom? representation environment count .word
            if sizeMatches representation element width then some (.allocate count element) else none
        | _ => none
      else none
  | .call name [context, data, length, index, width] =>
      if name == "cetta_gslt_native_ops_index_v1".toList && ctxExpression context then
        match result with
        | .ref element => do
            let (array, declared) ← arrayPair? representation environment data length
            let index ← typedAtom? representation environment index .word
            if declared = element && sizeMatches representation element width then some (.index array index element)
            else none
        | _ => none
      else none
  | .call name [context, data, length, first, count, width] =>
      if name == "cetta_gslt_native_ops_slice_v1".toList && ctxExpression context then
        match result with
        | .ref element => do
            let (array, declared) ← arrayPair? representation environment data length
            let first ← typedAtom? representation environment first .word
            let count ← typedAtom? representation environment count .word
            if declared = element && sizeMatches representation element width then
              some (.slice array first count element) else none
        | _ => none
      else none
  | .call name [context, pointer, count, .sizeOf type] =>
      if name == "cetta_gslt_native_ops_free_v1".toList && ctxExpression context && result = .unit then do
        let element ← nativeType? representation type
        let pointer ← freePointer? representation environment pointer count element
        some (.release pointer element)
      else none
  | _ => none

def typedArguments? (representation : Representation) (environment : Environment) :
    List Parameter → List CExpr → Option (List Atom)
  | [], [] => some []
  | parameter :: rest, expression :: expressions => do
      let first ← typedAtom? representation environment expression parameter.type
      let others ← typedArguments? representation environment rest expressions
      some (first :: others)
  | _, _ => none

def functionCall? (representation : Representation) (environment : Environment)
    (expression : CExpr) (result : NativeType) : Option (CallTarget × List Atom) := do
  match expression with
  | .call name arguments =>
      match representation.interface.functions.find?
          (fun header => (functionSymbol representation.moduleName header.name).toList == name) with
      | some header =>
          if header.result != result then none else
            match arguments with
            | context :: arguments =>
                if !ctxExpression context then none else do
                  let values ← typedArguments? representation environment header.parameters arguments
                  some (.function header.name, values)
            | [] => none
      | none => do
          let declaration ← representation.interface.externals.find? (fun declaration => declaration.cSymbol.toList == name)
          if declaration.header.result != result then none else do
            let values ← typedArguments? representation environment declaration.header.parameters arguments
            some (.external declaration.header.name, values)
  | _ => none

def defaultExpression (representation : Representation) (result : NativeType) (expression : CExpr) : Bool :=
  match result, expression with
  | .word, .decimal 0 | .byte, .decimal 0 | .word, .word 0 | .byte, .byte 0 | .bool, .bool false => true
  | .ref _, .null => true
  | .named _, .zero type | .array _, .zero type => sourceType? representation result == some type
  | _, _ => false

def defaultReturn (representation : Representation) (result : NativeType) : CStatement → Bool
  | .return none => result == .unit
  | .return (some expression) => defaultExpression representation result expression
  | _ => false

def contextCheck? (representation : Representation) (result : NativeType) : CStatement → Option Instruction
  | .branch (.binary .eq context .null) [returned] [] =>
      if ctxExpression context && defaultReturn representation result returned then some .checkContextExists else none
  | .branch (.binary .ne (.field context field true) (.identifier status)) [returned] [] =>
      if ctxExpression context && field == "fault".toList &&
          status == "CETTA_GSLT_NATIVE_OPS_OK_V1".toList && defaultReturn representation result returned then
        some .checkContext else none
  | _ => none

def nextNumericOperation? (representation : Representation) (environment : Environment)
    (following : List CStatement) : Option (NativeWord64.WordOp × Atom) :=
  match following with
  | .declare _ _ (.binary operation _ right) :: _ => do
      let operation ← nativeBinary? operation
      match operation with
      | .word .div | .word .mod | .word .shl | .word .shr => do
          let right ← typedAtom? representation environment right .word
          match operation with | .word operation => some (operation, right) | _ => none
      | _ => none
  | _ => none

def numericCheck? (representation : Representation) (environment : Environment) (result : NativeType)
    (statement : CStatement) (following : List CStatement) : Option Instruction := do
  let (operation, right) ← nextNumericOperation? representation environment following
  match statement with
  | .branch condition [.effect (.call fault [context, .identifier code]), returned] [] =>
      if fault != "cetta_gslt_native_ops_fault_v1".toList || !ctxExpression context ||
          !defaultReturn representation result returned then none else do
        match operation, condition with
        | .div, .binary .eq compared (.decimal 0) | .mod, .binary .eq compared (.decimal 0) =>
            let compared ← typedAtom? representation environment compared .word
            if compared = right && code == "CETTA_GSLT_NATIVE_OPS_DIVISION_BY_ZERO_V1".toList then
              some (.checkedNumericGuard operation right) else none
        | .shl, .binary .ge compared (.word 64) | .shr, .binary .ge compared (.word 64) =>
            let compared ← typedAtom? representation environment compared .word
            if compared = right && code == "CETTA_GSLT_NATIVE_OPS_SHIFT_OUT_OF_RANGE_V1".toList then
              some (.checkedNumericGuard operation right) else none
        | _, _ => none
  | _ => none

def label? (name : Name) : Option NativeIR.Label :=
  match numberedName? "gslt_loop".toList name with
  | some identity => some ⟨.entry, identity⟩
  | none => (numberedName? "gslt_end".toList name).map (fun identity => ⟨.exit, identity⟩)

def trailingSwitchBreak? (body : List CStatement) : Option (List CStatement) :=
  match body.reverse with
  | .break :: rest => some rest.reverse
  | _ => none

def pureDiscard (environment : Environment) : CExpr → Bool
  | .cast ⟨name, 0⟩ (.identifier value) => name == "void".toList &&
      ((identifierAtom? environment value).isSome || (localBinding? environment value).isSome)
  | _ => false

def declare? (representation : Representation) (environment : Environment)
    (cType : CType) (name : Name) (value : CExpr) : Option Normalized := do
  let type ← nativeType? representation cType
  match numberedName? "gslt_v".toList name with
  | some identity =>
      if environment.temporaries.any (fun entry => entry.1 == identity) then none else do
        let instruction ← match memoryCall? representation environment value type with
          | some operation => some (Instruction.helper (some (.temporary identity type)) operation)
          | none => match functionCall? representation environment value type with
              | some (target, arguments) => some (Instruction.call (some (.temporary identity type)) target arguments)
              | none => (pureOperation? representation environment type value).map (Instruction.temporary identity type)
        some ⟨[instruction], {environment with temporaries := (identity, type) :: environment.temporaries}⟩
  | none => do
      let source ← localName? name
      if environment.locals.any (fun entry => entry.1 == source) then none else do
        let value ← typedAtom? representation environment value type
        some ⟨[.declareLocal source type value], {environment with locals := (source, type) :: environment.locals}⟩

def assignment? (representation : Representation) (environment : Environment)
    (location value : CExpr) : Option Instruction :=
  match location with
  | .unary .dereference pointer => do
      let pointer ← atom? representation environment pointer
      match pointer.type with
      | .ref element => do
          let value ← typedAtom? representation environment value element
          some (.write pointer value)
      | _ => none
  | .index (.field array name false) index =>
      if name != "data".toList then none else do
        let array ← atom? representation environment array
        match array.type with
        | .array element => do
            let index ← typedAtom? representation environment index .word
            let value ← typedAtom? representation environment value element
            some (.writeElement array index value)
        | _ => none
  | .field array name false => do
      let array ← atom? representation environment array
      match array.type with
      | .array element =>
          if name == "data".toList then do
            let operation ← memoryCall? representation environment value (.ref element)
            some (.helper (some (.arrayData array element)) operation)
          else if name == "length".toList then do
            let value ← typedAtom? representation environment value .word
            some (.assign (.arrayLength array) value)
          else none
      | _ => none
  | .identifier name => do
      let destination ← identifierAtom? environment name
      match destination with
      | .temporary identity type => do
          let value ← typedAtom? representation environment value type
          some (.assign (.temporary identity type) value)
      | _ => none
  | _ => none

mutual
  def normalizeStatements? (representation : Representation) (result : NativeType)
      (environment : Environment) (body : List CStatement) : Option Normalized :=
    match body with
    | [] => some ⟨[], environment⟩
    | first :: rest => do
        let first ← normalizeStatement? representation result environment first rest
        let others ← normalizeStatements? representation result first.environment rest
        some ⟨first.code ++ others.code, others.environment⟩
  termination_by sizeOf body
  decreasing_by all_goals simp_wf; all_goals omega

  def normalizeStatement? (representation : Representation) (result : NativeType)
      (environment : Environment) (statement : CStatement) (following : List CStatement) : Option Normalized :=
    match contextCheck? representation result statement with
    | some check => some ⟨[check], environment⟩
    | none => match numericCheck? representation environment result statement following with
      | some check => some ⟨[check], environment⟩
      | none => match statement with
        | .empty => some ⟨[], environment⟩
        | .declare type name value => declare? representation environment type name value
        | .assign location value => do
            let instruction ← assignment? representation environment location value
            some ⟨[instruction], environment⟩
        | .effect value =>
            if pureDiscard environment value then some ⟨[], environment⟩ else
              do
              let actual ← match value with
                | .cast ⟨name, 0⟩ value => if name == "void".toList then some value else none
                | .cast _ _ => none
                | value => some value
              match memoryCall? representation environment actual .unit with
              | some operation => some ⟨[.helper none operation], environment⟩
              | none => do
                  let (target, arguments) ← functionCall? representation environment actual .unit
                  some ⟨[.call none target arguments], environment⟩
        | .branch condition yes no => do
            let condition ← condition? representation environment condition
            let yes ← normalizeStatements? representation result environment yes
            let no ← normalizeStatements? representation result environment no
            some ⟨[.branch condition yes.code no.code], environment⟩
        | .block body => do
            let body ← normalizeStatements? representation result environment body
            some ⟨[.scope body.code], environment⟩
        | .switch selector arms otherwise => do
            let selector ← typedAtom? representation environment selector .word
            let arms ← normalizeCases? representation result environment arms
            let otherwise ← normalizeArm? representation result environment otherwise
            some ⟨[.switch selector arms otherwise.code], environment⟩
        | .forLoop type name (.decimal 0) (.binary .lt (.identifier compared) bound)
            (.unary .increment (.identifier incremented)) body => do
            if type != ⟨"uint64_t".toList, 0⟩ || compared != name || incremented != name then none else do
              let counter ← numberedName? "gslt_init".toList name
              if environment.counters.contains counter || environment.temporaries.any (fun entry => entry.1 == counter) then none
              else do
                let bound ← typedAtom? representation environment bound .word
                let body ← normalizeStatements? representation result
                  {environment with counters := counter :: environment.counters} body
                some ⟨[.forWord counter bound body.code], environment⟩
        | .label name => do
            let label ← label? name
            some ⟨[.label label], environment⟩
        | .jump name => do
            let label ← label? name
            some ⟨[.jump label], environment⟩
        | .return none => if result = .unit then some ⟨[.return .unit], environment⟩ else none
        | .return (some value) => do
            let value ← typedAtom? representation environment value result
            some ⟨[.return value], environment⟩
        | _ => none
  termination_by sizeOf statement
  decreasing_by all_goals simp_wf; all_goals omega

  def normalizeArm? (representation : Representation) (result : NativeType)
      (environment : Environment) (body : List CStatement) : Option Normalized :=
    match body with
    | [.break] => some ⟨[], environment⟩
    | [] => none
    | first :: rest => do
        let first ← normalizeStatement? representation result environment first rest
        let others ← normalizeArm? representation result first.environment rest
        some ⟨first.code ++ others.code, others.environment⟩
  termination_by sizeOf body
  decreasing_by all_goals simp_wf; all_goals omega

  def normalizeCases? (representation : Representation) (result : NativeType)
      (environment : Environment) (arms : List (CExpr × List CStatement)) :
      Option (List (BitVec 64 × List Instruction)) := match arms with
    | [] => some []
    | (.word selector, body) :: rest => do
        let body ← normalizeArm? representation result environment body
        let rest ← normalizeCases? representation result environment rest
        some ((selector, body.code) :: rest)
    | _ => none
  termination_by sizeOf arms
  decreasing_by all_goals simp_wf; all_goals omega
end

mutual
  def maximumIdentity (code : List Instruction) : Nat := match code with
    | [] => 0
    | first :: rest => max (instructionMaximumIdentity first) (maximumIdentity rest)
  termination_by sizeOf code
  decreasing_by all_goals simp_wf; all_goals omega

  def instructionMaximumIdentity (instruction : Instruction) : Nat := match instruction with
    | .temporary identity _ _ | .helper (some (.temporary identity _)) _ |
        .call (some (.temporary identity _)) _ _ => identity
    | .forWord counter _ body => max counter (maximumIdentity body)
    | .branch _ yes no => max (maximumIdentity yes) (maximumIdentity no)
    | .switch _ arms otherwise => max (armsMaximumIdentity arms) (maximumIdentity otherwise)
    | .scope body => maximumIdentity body
    | .label label => label.identity
    | _ => 0
  termination_by sizeOf instruction
  decreasing_by all_goals simp_wf; all_goals omega

  def armsMaximumIdentity (arms : List (BitVec 64 × List Instruction)) : Nat := match arms with
    | [] => 0
    | (_, body) :: rest => max (maximumIdentity body) (armsMaximumIdentity rest)
  termination_by sizeOf arms
  decreasing_by all_goals simp_wf; all_goals omega
end

def normalizeFunction? (representation : Representation) (function : CFunction) : Option NativeIR.Function := do
  let header ← representation.interface.functions.find?
    (fun header => (functionSymbol representation.moduleName header.name).toList == function.name)
  let prototype ← sourcePrototype? representation header function.name true
  if prototype != .prototype function.result function.name function.parameters then none else do
    let body ← normalizeStatements? representation header.result
      ⟨header.parameters.map (fun parameter => (parameter.name, parameter.type)), [], []⟩ function.body
    some ⟨header, body.code, maximumIdentity body.code⟩

def normalizeUnit? (representation : Representation) (expectedHeader : Name) (unit : CUnit) :
    Option NativeIR.Program :=
  if unit.includeHeader != expectedHeader then none else do
    let functions ← unit.functions.mapM (normalizeFunction? representation)
    if functions.map (fun function => function.header.name) != representation.interface.functions.map Header.name then none
    else some ⟨representation.moduleName, representation.interface, functions⟩

private def emptyRepresentation : Representation := ⟨"Empty", ⟨[], [], [], []⟩, []⟩
/-! ## Immutable-parameter scalar C profile

This reader accepts ordinary C parameter names and explicitly admitted macro
values. Parameter atoms are immutable values in the caller-supplied target
frame, not source-visible storage locations. Pointer writes remain actual IR
writes, whose operational judgment requires a defined live destination.
Calls require an explicit typed external catalogue. With an empty catalogue,
no call is accepted. Scalar conditions use typed zero/null comparisons;
conjunction, disjunction and conditional returns retain their selected branch.
Logical results are represented as Booleans, admitting condition and Boolean
return contexts without treating C's `int` result as an unsigned arithmetic
operand. Allocation, casts and unknown expressions
remain outside this profile. Arithmetic uses the shared scalar primitives.
-/

abbrev PrimitiveBindings := List (Name × Atom)

/-- Ordinary C field reads use the admitted record layout. A pointer field
forms its actual positional address and loads it; this does not insert a
reference guard absent from the authored C. Defined storage is a separate
execution premise. The child code and its complete supply are retained. -/
def primitiveFieldRead? (representation : Representation)
    (base : NativeLowering.Expression) (member : Name) (throughPointer : Bool) :
    Option NativeLowering.Expression := do
  match base.result.type, throughPointer with
  | .ref (.named record), true =>
      let (index, type) ← authoredField? representation record member
      let address := NativeLowering.pureTemporary base.supply (.ref type)
        (.fieldAddress base.result record index)
      let value := NativeLowering.pureTemporary address.supply type
        (.indirectRead address.result)
      some (NativeLowering.prependCode (base.code ++ address.code) value)
  | .named record, false =>
      let (index, type) ← authoredField? representation record member
      some (NativeLowering.prependCode base.code
        (NativeLowering.pureTemporary base.supply type (.fieldValue base.result record index)))
  | _, _ => none

/-- An authored field destination retains its positional address. No load,
null check or ownership claim is inserted on the destination path. -/
def primitiveFieldAddress? (representation : Representation)
    (base : NativeLowering.Expression) (member : Name) :
    Option NativeLowering.Expression := do
  match base.result.type with
  | .ref (.named record) =>
      let (index, type) ← authoredField? representation record member
      some (NativeLowering.prependCode base.code
        (NativeLowering.pureTemporary base.supply (.ref type)
          (.fieldAddress base.result record index)))
  | _ => none

mutual
  def primitiveExpression? (bindings : PrimitiveBindings) (fuel : Nat)
      (expression : CExpr) (supply : NativeIR.Supply) (catalogue : List External := [])
      (representation : Representation := emptyRepresentation) :
      Option NativeLowering.Expression :=
    match fuel with
    | 0 => none
    | fuel + 1 => match expression with
      | .identifier name => do
          let atom ← (bindings.find? (fun binding => binding.1 == name)).map Prod.snd
          some ⟨[], atom, supply⟩
      | .word value => some ⟨[], .word value, supply⟩
      | .bool value => some (NativeLowering.pureTemporary supply .bool (.bool value))
      | .field base member throughPointer => do
          let base ← primitiveExpression? bindings fuel base supply catalogue representation
          primitiveFieldRead? representation base member throughPointer
      | .unary .dereference pointer => do
          let pointer ← primitiveExpression? bindings fuel pointer supply catalogue representation
          match pointer.result.type with
          | .ref type => some (NativeLowering.prependCode pointer.code
              (NativeLowering.pureTemporary pointer.supply type (.indirectRead pointer.result)))
          | _ => none
      | .binary (operator@.and) left right | .binary (operator@.or) left right => do
          let left ← primitiveExpression? bindings fuel left supply catalogue representation
          let left ← NativeLowering.scalarCondition? left
          let copied := NativeLowering.pureTemporary left.supply .bool (.copy left.result)
          let right ← primitiveExpression? bindings fuel right copied.supply catalogue representation
          let right ← NativeLowering.scalarCondition? right
          some (shortCircuitOutput (operator == .and) left right)
      | .unary .not operand => do
          let operand ← primitiveExpression? bindings fuel operand supply catalogue representation
          let condition ← NativeLowering.scalarCondition? operand
          some (NativeLowering.prependCode condition.code
            (NativeLowering.pureTemporary condition.supply .bool (.unary .not condition.result)))
      | .binary operator left right => do
          let operation ← nativeBinary? operator
          let left ← primitiveExpression? bindings fuel left supply catalogue representation
          let right ← primitiveExpression? bindings fuel right left.supply catalogue representation
          if left.result.type != right.result.type then none else do
            let type ← binaryType operation left.result.type
            let result := NativeLowering.pureTemporary right.supply type
              (.binary operation left.result right.result)
            some (NativeLowering.prependCode
              (left.code ++ right.code ++ NativeLowering.numericGuard operation right.result) result)
      | .call name arguments => do
          let declaration ← match catalogue.filter (fun candidate => candidate.cSymbol.toList == name) with
            | [declaration] => some declaration
            | _ => none
          if (catalogue.filter (fun candidate =>
              candidate.header.name == declaration.header.name)).length != 1 then none else do
            let arguments ← primitiveArguments? bindings fuel declaration.header.parameters
              arguments supply catalogue representation
            let next := NativeIR.fresh arguments.supply
            some ⟨arguments.code ++ [.call
              (some (.temporary next.1 declaration.header.result))
              (.external declaration.header.name) arguments.results],
              .temporary next.1 declaration.header.result, next.2⟩
      | _ => none

  /-- Actual argument syntax is evaluated in order and checked against every
  declared parameter. A missing or extra argument cannot disappear. -/
  def primitiveArguments? (bindings : PrimitiveBindings) (fuel : Nat)
      (parameters : List Parameter) (arguments : List CExpr) (supply : NativeIR.Supply)
      (catalogue : List External) (representation : Representation := emptyRepresentation) :
      Option NativeLowering.Arguments :=
    match parameters, arguments with
    | [], [] => some ⟨[], [], supply⟩
    | parameter :: parameters, argument :: arguments => match fuel with
      | 0 => none
      | fuel + 1 => do
          let first ← primitiveExpression? bindings fuel argument supply catalogue representation
          if first.result.type != parameter.type then none else do
            let rest ← primitiveArguments? bindings fuel parameters arguments first.supply catalogue representation
            some ⟨first.code ++ rest.code, first.result :: rest.results, rest.supply⟩
    | _, _ => none
end

/-- The immutable-parameter profile cannot authorize a call merely by
recognizing its syntax, for any arguments, bindings or reader budget. -/
theorem primitiveExpression_call_refused (bindings : PrimitiveBindings) (fuel : Nat)
    (name : Name) (arguments : List CExpr) (supply : NativeIR.Supply)
    (representation : Representation := emptyRepresentation) :
    primitiveExpression? bindings fuel (.call name arguments) supply [] representation = none := by
  cases fuel <;> rfl

private def observedWord : External :=
  ⟨⟨"observe", [⟨"value", .word⟩], .word⟩, "observe", .effect, none⟩

/-- Positive catalogue control: the actual argument remains an operand of
the emitted call. This is admission, with action semantics still separate. -/
theorem primitive_declared_call_keeps_argument :
    primitiveExpression? [("x".toList, .temporary 1 .word)] 10
      (.call "observe".toList [.identifier "x".toList]) ⟨1⟩ [observedWord] =
      some ⟨[.call (some (.temporary 2 .word)) (.external "observe")
        [.temporary 1 .word]], .temporary 2 .word, ⟨2⟩⟩ := by rfl

theorem primitive_declared_call_wrong_type_refused :
    primitiveExpression? [] 10 (.call "observe".toList [.bool true]) ⟨0⟩
      [observedWord] = none := by rfl

theorem primitive_declared_call_extra_argument_refused :
    primitiveExpression? [] 10 (.call "observe".toList [.word 1, .word 2]) ⟨0⟩
      [observedWord] = none := by rfl

theorem primitive_ambiguous_catalogue_refused :
    primitiveExpression? [] 10 (.call "observe".toList [.word 1]) ⟨0⟩
      [observedWord, observedWord] = none := by rfl

mutual
  def primitiveStatements? (bindings : PrimitiveBindings) (result : NativeType)
      (fuel : Nat) (body : List CStatement) (supply : NativeIR.Supply)
      (catalogue : List External := []) (representation : Representation := emptyRepresentation) :
      Option (List Instruction × NativeIR.Supply) :=
    match body with
    | [] => some ([], supply)
    | first :: rest => match fuel with
      | 0 => none
      | fuel + 1 => do
          let first ← primitiveStatement? bindings result fuel first supply catalogue representation
          let rest ← primitiveStatements? bindings result fuel rest first.2 catalogue representation
          some (first.1 ++ rest.1, rest.2)

  def primitiveStatement? (bindings : PrimitiveBindings) (result : NativeType)
      (fuel : Nat) (statement : CStatement) (supply : NativeIR.Supply)
      (catalogue : List External := []) (representation : Representation := emptyRepresentation) :
      Option (List Instruction × NativeIR.Supply) :=
    match fuel with
    | 0 => none
    | fuel + 1 => match statement with
      | .return (some (.cast ⟨['u', 'n', 's', 'i', 'g', 'n', 'e', 'd'], 0⟩ (.decimal 0))) =>
          if result = .word then some ([.return (.word 0)], supply) else none
      | .return (some (.unsignedInteger 0)) =>
          if result = .word then some ([.return (.word 0)], supply) else none
      | .return (some (.conditional condition whenTrue whenFalse)) => do
          let condition ← primitiveExpression? bindings fuel condition supply catalogue representation
          let condition ← NativeLowering.scalarCondition? condition
          let first ← primitiveStatement? bindings result fuel (.return (some whenTrue))
            condition.supply catalogue representation
          let second ← primitiveStatement? bindings result fuel (.return (some whenFalse))
            first.2 catalogue representation
          some (condition.code ++ [.branch (.value condition.result) first.1 second.1], second.2)
      | .return (some expression) => do
          let value ← primitiveExpression? bindings fuel expression supply catalogue representation
          if value.result.type = result then
            some (value.code ++ [.return value.result], value.supply)
          else none
      | .assign (.unary .dereference pointer) expression => do
          let pointer ← primitiveExpression? bindings fuel pointer supply catalogue representation
          let value ← primitiveExpression? bindings fuel expression pointer.supply catalogue representation
          if pointer.result.type = .ref value.result.type then
            some (pointer.code ++ value.code ++ [.write pointer.result value.result], value.supply)
          else none
      | .assign (.field base member true) expression => do
          let base ← primitiveExpression? bindings fuel base supply catalogue representation
          let pointer ← primitiveFieldAddress? representation base member
          let value ← primitiveExpression? bindings fuel expression pointer.supply catalogue representation
          if pointer.result.type = .ref value.result.type then
            some (pointer.code ++ value.code ++ [.write pointer.result value.result], value.supply)
          else none
      | .return none =>
          if result = .unit then some ([.return .unit], supply) else none
      | .branch condition whenTrue whenFalse => do
          let condition ← primitiveExpression? bindings fuel condition supply catalogue representation
          let condition ← NativeLowering.scalarCondition? condition
          let first ← primitiveStatements? bindings result fuel whenTrue condition.supply catalogue representation
          let second ← primitiveStatements? bindings result fuel whenFalse first.2 catalogue representation
          some (condition.code ++ [.branch (.value condition.result) first.1 second.1], second.2)
      | _ => none
end

/-- Returning an unsupported call does not turn it into an admitted body. -/
theorem primitiveStatements_return_call_refused (bindings : PrimitiveBindings)
    (result : NativeType) (fuel : Nat) (name : Name) (arguments : List CExpr)
    (supply : NativeIR.Supply) :
    primitiveStatements? bindings result fuel [.return (some (.call name arguments))]
      supply = none := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          simp only [primitiveStatements?, primitiveStatement?,
            primitiveExpression_call_refused]
          rfl

/-- Full syntax consumption precedes typed normalization. Unknown tokens or
operations cannot disappear into an otherwise recognized body. -/
def primitiveBodyText? (names : TypeNames) (bindings : PrimitiveBindings)
    (result : NativeType) (characters : List Char) (supply : NativeIR.Supply)
    (catalogue : List External := []) (representation : Representation := emptyRepresentation) :
    Option (List Instruction × NativeIR.Supply) := do
  let statements ← blockText? names characters
  primitiveStatements? bindings result (characters.length + 1) statements supply catalogue representation

theorem unsigned_zero_return_exact : primitiveStatement? [] .word 5
    (.return (some (.cast ⟨"unsigned".toList, 0⟩ (.decimal 0)))) ⟨0⟩ =
      some ([.return (.word 0)], ⟨0⟩) := by rfl

theorem unsigned_zero_literal_return_exact : primitiveStatement? [] .word 5
    (.return (some (.unsignedInteger 0))) ⟨0⟩ =
      some ([.return (.word 0)], ⟨0⟩) := by rfl

/-- Recognizing an unsigned suffix supplies no width conversion in arithmetic,
regardless of the reader budget, bindings or external declarations. -/
theorem unsigned_literal_arithmetic_not_widened (bindings : PrimitiveBindings)
    (fuel value : Nat) (supply : NativeIR.Supply) (catalogue : List External)
    (representation : Representation) :
    primitiveExpression? bindings fuel (.unsignedInteger value) supply catalogue
      representation = none := by
  cases fuel <;> rfl

/-- The narrow literal conversion is admitted at the declared word return,
not in arbitrary arithmetic. Widening the source expression would silently
change cases such as unsigned shifts and complements. -/
theorem unsigned_zero_arithmetic_not_widened : primitiveExpression? [] 5
    (.cast ⟨"unsigned".toList, 0⟩ (.decimal 0)) ⟨0⟩ = none := by rfl

theorem conditional_return_retains_call_arm : primitiveStatement? [] .word 10
    (.return (some (.conditional (.bool false)
      (.call "observe".toList [.word 1])
      (.cast ⟨"unsigned".toList, 0⟩ (.decimal 0))))) ⟨0⟩ [observedWord] =
    some ([.temporary 1 .bool (.bool false),
      .branch (.value (.temporary 1 .bool))
        [.call (some (.temporary 2 .word)) (.external "observe") [.word 1],
         .return (.temporary 2 .word)] [.return (.word 0)]], ⟨2⟩) := by rfl

/-- Immutable ordinary parameters are read from their actual invocation
cells before the scalar body runs. Their private identities follow declaration
order; the body starts above every identity used by this capture. -/
def primitiveParameterCapture (parameters : List Parameter) : List Instruction :=
  parameters.mapIdx fun index parameter =>
    .temporary (index + 1) parameter.type (.readLocal parameter.name)

def primitiveParameterBindings (parameters : List Parameter) : PrimitiveBindings :=
  parameters.mapIdx fun index parameter =>
    (parameter.name.toList, .temporary (index + 1) parameter.type)

def primitiveParametersMatch (representation : Representation) :
    List Parameter → List CParameter → Bool
  | [], [] => true
  | expected :: rest, actual :: others =>
      actual.name == expected.name.toList &&
        nativeType? representation actual.type == some expected.type &&
        primitiveParametersMatch representation rest others
  | _, _ => false

/-- The complete ordinary prototype is checked against a separately supplied
header. Macro bindings cannot shadow a parameter, and duplicate parameter
names are refused. This profile admits the scalar body rather than the
generated-C context protocol used by `normalizeFunction?`. -/
def primitiveFunction? (representation : Representation) (header : Header)
    (macros : PrimitiveBindings) (fuel : Nat) (function : CFunction) :
    Option NativeIR.Function := do
  let result ← nativeType? representation function.result
  if function.name != header.name.toList || result != header.result ||
      !primitiveParametersMatch representation header.parameters function.parameters then none else do
    if (header.parameters.map Parameter.name).eraseDups.length != header.parameters.length ||
        macros.any (fun macroBinding =>
          header.parameters.any (fun parameter => parameter.name.toList == macroBinding.1)) then none else do
      let body ← primitiveStatements?
        (primitiveParameterBindings header.parameters ++ macros) result fuel function.body
        ⟨header.parameters.length⟩ representation.interface.externals representation
      some ⟨header, primitiveParameterCapture header.parameters ++ body.1, body.2.next⟩

/-- Local linkage and inline spelling are accepted once, in either order.
The shared function parser consumes the whole source;
neither an extra function nor trailing tokens are silently ignored. -/
def primitiveFunctionText? (representation : Representation) (names : TypeNames)
    (header : Header) (macros : PrimitiveBindings) (characters : List Char) :
    Option NativeIR.Function := do
  let function ← ordinaryFunctionText? names characters
  primitiveFunction? representation header macros (characters.length + 1) function

/-- Ordinary typedef spellings for separately declared records. The mapping
does not certify a physical layout; that remains an execution boundary. -/
abbrev RecordAliases := List (Name × String)

def recordAliasesValid (representation : Representation) (aliases : RecordAliases) : Bool :=
  (aliases.map Prod.fst).eraseDups.length == aliases.length &&
    aliases.all (fun entry =>
      (nativeBaseType? representation entry.1).isNone &&
      (lookupRecord representation.interface entry.2).isSome)

def canonicalPrototypeType? (representation : Representation) (aliases : RecordAliases)
    (type : CType) : Option CType :=
  if (nativeType? representation type).isSome then some type else do
    let (_, record) ← aliases.find? (fun entry => entry.1 == type.name)
    some { type with name := recordName representation.moduleName record }

/-- Calls require an individually declared pure service. That declaration
is an obligation, not a proof that the service preserves memory. -/
def readOnlyExpression (catalogue : List External) : Nat → CExpr → Bool
  | 0, _ => false
  | fuel + 1, expression => match expression with
    | .identifier _ | .decimal _ | .unsignedInteger _ | .word _ | .byte _ | .bool _ | .null |
        .zero _ | .sizeOf _ => true
    | .aggregate _ _ | .sizeOfExpr _ => false
    | .call name arguments =>
        (match catalogue.filter (fun declaration => declaration.cSymbol.toList == name) with
          | [declaration] => declaration.effect == .pure
          | _ => false) && arguments.all (readOnlyExpression catalogue fuel)
    | .unary .increment _ | .postIncrement _ => false
    | .unary _ operand | .cast _ operand | .field operand _ _ =>
        readOnlyExpression catalogue fuel operand
    | .binary _ left right | .index left right =>
        readOnlyExpression catalogue fuel left && readOnlyExpression catalogue fuel right
    | .conditional condition whenTrue whenFalse =>
        readOnlyExpression catalogue fuel condition &&
        readOnlyExpression catalogue fuel whenTrue && readOnlyExpression catalogue fuel whenFalse

def readOnlyStatement (catalogue : List External) : Nat → CStatement → Bool
  | 0, _ => false
  | fuel + 1, statement => match statement with
    | .empty | .return none => true
    | .return (some value) => readOnlyExpression catalogue fuel value
    | .branch condition whenTrue whenFalse =>
        readOnlyExpression catalogue fuel condition &&
        whenTrue.all (readOnlyStatement catalogue fuel) &&
        whenFalse.all (readOnlyStatement catalogue fuel)
    | .block body => body.all (readOnlyStatement catalogue fuel)
    | _ => false

/-- Pointee qualifiers are checked against the requested profile before
typedef normalization and ordinary body lowering. This deliberately narrower
reader admits no authored stores, even through an unqualified alias. -/
def qualifiedReadOnlyFunction? (representation : Representation) (header : Header)
    (aliases : RecordAliases) (qualifications : List Bool) (macros : PrimitiveBindings)
    (fuel : Nat) (function : CQualifiedFunction) : Option NativeIR.Function := do
  if !recordAliasesValid representation aliases ||
      function.parameters.map CQualifiedParameter.pointeeConst != qualifications ||
      !function.body.all (readOnlyStatement representation.interface.externals fuel) then none else do
    let unqualified := function.unqualified
    let result ← canonicalPrototypeType? representation aliases unqualified.result
    let parameters ← unqualified.parameters.mapM fun parameter => do
      let type ← canonicalPrototypeType? representation aliases parameter.type
      some { parameter with type := type }
    primitiveFunction? representation header macros fuel
      ⟨result, unqualified.name, parameters, unqualified.body⟩

def qualifiedReadOnlyFunctionText? (representation : Representation) (names : TypeNames)
    (header : Header) (aliases : RecordAliases) (qualifications : List Bool)
    (macros : PrimitiveBindings) (characters : List Char) : Option NativeIR.Function := do
  let function ← qualifiedFunctionText? names characters
  qualifiedReadOnlyFunction? representation header aliases qualifications macros
    (characters.length + 1) function

/-- A stored destination must be rooted in one explicit, unqualified pointer
parameter. This is a syntactic const discipline, not a memory permission.
Local aliases and arbitrary computed destinations are outside this profile. -/
def parameterStoreAllowed (parameters : List CQualifiedParameter) : CExpr → Bool
  | .field (.identifier root) _ true | .unary .dereference (.identifier root) =>
      match parameters.filter (fun parameter => parameter.parameter.name == root) with
      | [parameter] => !parameter.pointeeConst && parameter.parameter.type.pointers > 0
      | _ => false
  | _ => false

def parameterStoreStatement (parameters : List CQualifiedParameter)
    (catalogue : List External) : Nat → CStatement → Bool
  | 0, _ => false
  | fuel + 1, statement => match statement with
    | .assign location value =>
        parameterStoreAllowed parameters location && readOnlyExpression catalogue fuel value
    | .branch condition whenTrue whenFalse =>
        readOnlyExpression catalogue fuel condition &&
        whenTrue.all (parameterStoreStatement parameters catalogue fuel) &&
        whenFalse.all (parameterStoreStatement parameters catalogue fuel)
    | _ => readOnlyStatement catalogue (fuel + 1) statement

/-- The mutable counterpart of the immutable-parameter profile checks every
pointee qualification before lowering the complete body. Falling off a void
C function returns unit; the epilogue cannot run after an explicit return.
Caller storage validity, aliasing and service contracts remain operational
obligations of the independently defined target semantics. -/
def qualifiedParameterStoreFunction? (representation : Representation) (header : Header)
    (aliases : RecordAliases) (qualifications : List Bool) (macros : PrimitiveBindings)
    (fuel : Nat) (function : CQualifiedFunction) : Option NativeIR.Function := do
  if !recordAliasesValid representation aliases ||
      function.parameters.map CQualifiedParameter.pointeeConst != qualifications ||
      !function.body.all (parameterStoreStatement function.parameters
        representation.interface.externals fuel) then none else do
    let unqualified := function.unqualified
    let result ← canonicalPrototypeType? representation aliases unqualified.result
    let parameters ← unqualified.parameters.mapM fun parameter => do
      let type ← canonicalPrototypeType? representation aliases parameter.type
      some { parameter with type := type }
    let lowered ← primitiveFunction? representation header macros fuel
      ⟨result, unqualified.name, parameters, unqualified.body⟩
    some { lowered with body := lowered.body ++
      (if header.result = .unit then [.return .unit] else []) }

def qualifiedParameterStoreFunctionText? (representation : Representation) (names : TypeNames)
    (header : Header) (aliases : RecordAliases) (qualifications : List Bool)
    (macros : PrimitiveBindings) (characters : List Char) : Option NativeIR.Function := do
  let function ← qualifiedFunctionText? names characters
  qualifiedParameterStoreFunction? representation header aliases qualifications macros
    (characters.length + 1) function

private def wordEnvironment : Environment := ⟨[], [(1, .word), (2, .word)], []⟩

theorem mismatched_array_views_refused : arrayPair? emptyRepresentation
    ⟨[], [(1, .array .word), (2, .array .word)], []⟩
    (.field (.identifier "gslt_v1".toList) "data".toList false)
    (.field (.identifier "gslt_v2".toList) "length".toList false) = none := by rfl

theorem numeric_fault_return_keeps_function_type : numericCheck? emptyRepresentation wordEnvironment .word
    (.branch (.binary .eq (.identifier "gslt_v2".toList) (.decimal 0))
      [.effect (.call "cetta_gslt_native_ops_fault_v1".toList
        [.identifier "ctx".toList, .identifier "CETTA_GSLT_NATIVE_OPS_DIVISION_BY_ZERO_V1".toList]),
        .return (some (.decimal 0))] [])
    [.declare ⟨"uint64_t".toList, 0⟩ "gslt_v3".toList
      (.binary .div (.identifier "gslt_v1".toList) (.identifier "gslt_v2".toList))] =
    some (.checkedNumericGuard .div (.temporary 2 .word)) := by rfl

theorem wrong_default_return_refused : contextCheck? emptyRepresentation .word
    (.branch (.binary .eq (.identifier "ctx".toList) .null)
      [.return (some (.bool false))] []) = none := by rfl

theorem missing_switch_exit_refused : trailingSwitchBreak? [.return none] = none := by rfl

private def authoredFieldRepresentation (fields : List Parameter) : Representation :=
  ⟨"ReadControl", ⟨[⟨"Cache", fields⟩], [], [], []⟩, []⟩

private def cacheFieldRepresentation : Representation :=
  authoredFieldRepresentation [⟨"before", .word⟩, ⟨"cache_state", .word⟩]

/-- Original underscore spelling selects the second declared field and emits
its actual address/read pair without a generated-name rewrite. -/
theorem authored_underscore_field_read :
    primitiveFieldRead? cacheFieldRepresentation
      ⟨[], .temporary 1 (.ref (.named "Cache")), ⟨1⟩⟩ "cache_state".toList true =
      some ⟨[.temporary 2 (.ref .word)
        (.fieldAddress (.temporary 1 (.ref (.named "Cache"))) "Cache" 1),
        .temporary 3 .word (.indirectRead (.temporary 2 (.ref .word)))],
        .temporary 3 .word, ⟨3⟩⟩ := by rfl

theorem generated_field_spelling_is_distinct :
    cField? cacheFieldRepresentation "Cache" "cache_u_state".toList = some (1, .word) ∧
      cField? cacheFieldRepresentation "Cache" "cache_state".toList = none := by
  exact ⟨rfl, rfl⟩

theorem generated_alias_is_not_authored_field :
    primitiveFieldRead? cacheFieldRepresentation
      ⟨[], .temporary 1 (.ref (.named "Cache")), ⟨1⟩⟩ "cache_u_state".toList true = none := by rfl

theorem ambiguous_authored_field_refused :
    primitiveFieldRead? (authoredFieldRepresentation
      [⟨"cache_state", .word⟩, ⟨"cache_state", .bool⟩])
      ⟨[], .temporary 1 (.ref (.named "Cache")), ⟨1⟩⟩ "cache_state".toList true = none := by rfl

theorem missing_authored_field_refused :
    primitiveFieldRead? cacheFieldRepresentation
      ⟨[], .temporary 1 (.ref (.named "Cache")), ⟨1⟩⟩ "missing".toList true = none := by rfl

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
