import Mettapedia.GSLT.LanguageDef.NativeOpsCHeader
import Mettapedia.GSLT.LanguageDef.NativeOpsIR
import Mettapedia.GSLT.LanguageDef.NativeOpsLowering

/-!
# Typed operands of admitted native C

Names are resolved through the separately checked scalar/record/array layouts
and current C scope. Address taking is restricted to source-visible locals
and record fields. Compiler-private temporaries have no exposed addresses.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

open NativeIR (Atom PureOperation)

structure Environment where
  locals : Scope
  temporaries : List (Nat × NativeType)
  counters : List Nat
  deriving DecidableEq, Repr

def stripPrefix? (leading name : Name) : Option Name :=
  if leading.isPrefixOf name then some (name.drop leading.length) else none

def encodedCharacters? : Name → Option Name
  | [] => some []
  | '_' :: 'u' :: '_' :: rest => (encodedCharacters? rest).map ('_' :: ·)
  | '_' :: 'h' :: '_' :: rest => (encodedCharacters? rest).map ('-' :: ·)
  | '_' :: _ => none
  | character :: rest => (encodedCharacters? rest).map (character :: ·)

def sourceLetter (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

def sourceName? (name : Name) : Option String := do
  let encoded := (stripPrefix? "gslt_keyword_".toList name).getD name
  let characters ← encodedCharacters? encoded
  let encoded := cIdentifierCharacters characters
  let canonical := if cKeywords.any (fun keyword => keyword.toList == encoded) then
    "gslt_keyword_".toList ++ encoded else encoded
  let valid := match characters with
    | [] => false
    | first :: rest => sourceLetter first &&
        rest.all (fun c => sourceLetter c || ('0' ≤ c && c ≤ '9') || c == '_' || c == '-')
  if valid && canonical == name then some (String.ofList characters) else none

def localName? (name : Name) : Option String := do
  let encoded ← stripPrefix? "local_".toList name
  sourceName? encoded

def numberedName? (leading : Name) (name : Name) : Option Nat := do
  let digits ← stripPrefix? leading name
  let value ← decimalChars? digits
  if 0 < value && (leading ++ (toString value).toList) == name then some value else none

def nativeBaseType? (representation : Representation) (name : Name) : Option NativeType :=
  if name == "void".toList then some .unit else
  if name == "uint64_t".toList then some .word else
  if name == "uint8_t".toList then some .byte else
  if name == "bool".toList then some .bool else
  if name == "CettaGsltNativeOpsBytesV1".toList then some (.array .byte) else
  match representation.interface.records.find?
      (fun record => recordName representation.moduleName record.name == name) with
  | some record => some (.named record.name)
  | none => match representation.interface.opaques.find? (fun opaqueDecl => opaqueDecl.cType.toList == name) with
      | some opaqueDecl => some (.named opaqueDecl.name)
      | none => (representation.arrayAliases.find? (fun entry => entry.2 == name)).map
          (fun entry => .array entry.1)

def nativeType? (representation : Representation) (type : CType) : Option NativeType := do
  let base ← nativeBaseType? representation type.name
  some ((List.replicate type.pointers ()).foldl (fun element _ => .ref element) base)

def localBinding? (environment : Environment) (name : Name) : Option (String × NativeType) := do
  let source ← localName? name
  let type ← (environment.locals.find? (fun entry => entry.1 == source)).map Prod.snd
  some (source, type)

def identifierAtom? (environment : Environment) (name : Name) : Option Atom :=
  match numberedName? "gslt_v".toList name with
  | some identity => do
      let type ← (environment.temporaries.find? (fun entry => entry.1 == identity)).map Prod.snd
      some (.temporary identity type)
  | none => do
      let identity ← numberedName? "gslt_init".toList name
      if environment.counters.contains identity then some (.iterationCounter identity) else none

def atom? (representation : Representation) (environment : Environment) : CExpr → Option Atom
  | .identifier name => identifierAtom? environment name
  | .unary .address (.identifier name) => do
      let (source, type) ← localBinding? environment name
      some (.localAddress source type)
  | .word value => some (.word value)
  | .zero type => (nativeType? representation type).map Atom.zero
  | _ => none

def typedAtom? (representation : Representation) (environment : Environment)
    (expression : CExpr) (type : NativeType) : Option Atom :=
  match expression with
  | .decimal 0 => match type with
      | .word | .byte => some (.zero type)
      | _ => none
  | .bool false => if type = .bool then some (.zero .bool) else none
  | .null => match type with
      | .ref _ => some (.zero type)
      | _ => none
  | _ => do
      let atom ← atom? representation environment expression
      if atom.type = type then some atom else none

def cField? (representation : Representation) (record : String) (name : Name) :
    Option (Nat × NativeType) := do
  let declaration ← lookupRecord representation.interface record
  let index ← declaration.fields.findIdx? (fun field => (cIdentifier field.name).toList == name)
  let field ← declaration.fields[index]?
  some (index, field.type)

/-- Authored C fields use their declared spelling. Generated C has a separate
encoded-name lookup. Repeated matching declarations are ambiguous and refused. -/
def authoredField? (representation : Representation) (record : String) (name : Name) :
    Option (Nat × NativeType) := do
  let declaration ← lookupRecord representation.interface record
  match declaration.fields.zipIdx.filter (fun entry => entry.1.name.toList == name) with
  | [(field, index)] => some (index, field.type)
  | _ => none

def nativeBinary? : BinaryOperator → Option Binary
  | .add => some (.word .add) | .sub => some (.word .sub) | .mul => some (.word .mul)
  | .div => some (.word .div) | .mod => some (.word .mod)
  | .shiftLeft => some (.word .shl) | .shiftRight => some (.word .shr)
  | .bitAnd => some (.word .band) | .bitOr => some (.word .bor) | .bitXor => some (.word .bxor)
  | .eq => some (.compare .eq) | .ne => some (.compare .ne)
  | .lt => some (.compare .lt) | .le => some (.compare .le)
  | .gt => some (.compare .gt) | .ge => some (.compare .ge)
  | .and | .or => none

def pureOperation? (representation : Representation) (environment : Environment)
    (type : NativeType) (expression : CExpr) : Option PureOperation :=
  match expression with
  | .word value => if type = .word then some (.word value) else none
  | .byte value => if type = .byte then some (.byte value) else none
  | .bool value => if type = .bool then some (.bool value) else none
  | .decimal 0 => match type with
      | .word => some (.word 0) | .byte => some (.byte 0) | _ => none
  | .null => match type with | .ref _ => some (.zero type) | _ => none
  | .zero cType => do
      let initialized ← nativeType? representation cType
      if initialized = type && validType representation.interface type true then some (.zero type) else none
  | .identifier name => match localBinding? environment name with
      | some (source, declared) => if declared = type then some (.readLocal source) else none
      | none => do
          let atom ← identifierAtom? environment name
          if atom.type = type then some (.copy atom) else none
  | .unary .address (.field base name true) => do
      let base ← atom? representation environment base
      match base.type with
      | .ref (.named record) => do
          let (index, declared) ← cField? representation record name
          if type = .ref declared then some (.fieldAddress base record index) else none
      | _ => none
  | .unary .address (.identifier name) => do
      let (source, declared) ← localBinding? environment name
      if type = .ref declared then some (.copy (.localAddress source declared)) else none
  | .unary .dereference pointer => do
      let pointer ← atom? representation environment pointer
      if pointer.type = .ref type then some (.indirectRead pointer) else none
  | .field base name false => do
      let base ← atom? representation environment base
      match base.type with
      | .named record => do
          let (index, declared) ← cField? representation record name
          if declared = type then some (.fieldValue base record index) else none
      | .array _ => if name == "length".toList && type = .word then some (.length base) else none
      | _ => none
  | .unary .not operand => do
      let operand ← typedAtom? representation environment operand .bool
      if type = .bool then some (.unary .not operand) else none
  | .unary .complement operand => do
      let operand ← typedAtom? representation environment operand .word
      if type = .word then some (.unary .complement operand) else none
  | .cast cType operand => do
      let result ← nativeType? representation cType
      if result = .word && type = .word then do
        let operand ← typedAtom? representation environment operand .byte
        some (.unary .toWord operand)
      else if result = .byte && type = .byte then do
        let operand ← typedAtom? representation environment operand .word
        some (.unary .toByte operand)
      else none
  | .binary operation first second => do
      let operation ← nativeBinary? operation
      let first ← atom? representation environment first
      let second ← typedAtom? representation environment second first.type
      if first.type = second.type && binaryType operation first.type = some type then
        some (.binary operation first second)
      else none
  | _ => none

def condition? (representation : Representation) (environment : Environment) :
    CExpr → Option NativeIR.Condition
  | .unary .not expression => (typedAtom? representation environment expression .bool).map .negated
  | expression => (typedAtom? representation environment expression .bool).map .value

theorem source_local_encoding_is_unambiguous :
    localName? "local_depth_h_limit".toList = some "depth-limit" ∧
    localName? "local_depth_u_limit".toList = some "depth_limit" := by decide +kernel

theorem noncanonical_temporary_name_refused : numberedName? "gslt_v".toList "gslt_v01".toList = none := by cbv

theorem private_temporary_address_refused : atom? ⟨"Empty", ⟨[], [], [], []⟩, []⟩
    ⟨[], [(1, .word)], []⟩ (.unary .address (.identifier "gslt_v1".toList)) = none := by cbv

theorem byte_pointer_is_not_word_operand : typedAtom? ⟨"Empty", ⟨[], [], [], []⟩, []⟩
    ⟨[], [(1, .ref .byte)], []⟩ (.identifier "gslt_v1".toList) (.ref .word) = none := by cbv

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
