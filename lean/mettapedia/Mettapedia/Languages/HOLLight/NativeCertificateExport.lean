import Mettapedia.Languages.HOLLight.SharedCertificateExport
import Mettapedia.Languages.HOLLight.PrimitiveTransport

/-!
# Native HOL certificate serialization

An untrusted writer for the existing HOLRPLY1 receiver. It serializes typed
source commands and retained primitive receipts, sharing names, types and
named terms. The receiver independently checks every inference, expected
sequent and axiom dependency. Encoding is not a verdict or a refinement proof
for the receiver implementation. Symbol provenance remains supplied by the
registered declaration history.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.NativeCertificateExport
open Mettapedia.Languages.OpenTheory Lean
open SharedCertificateExport (TypeNode NamedNode)

inductive Policy where | unrestricted | standard | sealed
  deriving DecidableEq, Repr

def Policy.number : Policy → Nat
  | .unrestricted => 0 | .standard => 1 | .sealed => 2

private def hexDigit (digit : Nat) : Char :=
  Char.ofNat (if digit < 10 then 48 + digit else 87 + digit)

private def hex4 (value : Nat) : String :=
  String.ofList [hexDigit (value / 4096 % 16), hexDigit (value / 256 % 16),
    hexDigit (value / 16 % 16), hexDigit (value % 16)]

private def asciiChar (c : Char) : String :=
  if c == '"' then "\\\"" else if c == '\\' then "\\\\"
  else if c == '\n' then "\\n" else if c == '\r' then "\\r"
  else if c == '\t' then "\\t" else if c.toNat == 8 then "\\b"
  else if c.toNat == 12 then "\\f" else if c.toNat < 32 || c.toNat > 126 then
    if c.toNat < 65536 then "\\u" ++ hex4 c.toNat
    else let n := c.toNat - 65536
         "\\u" ++ hex4 (55296 + n / 1024) ++ "\\u" ++ hex4 (56320 + n % 1024)
  else String.singleton c

def asciiQuoted (text : String) : String :=
  "\"" ++ String.join (text.toList.map asciiChar) ++ "\""

def nativeName (name : Mettapedia.Languages.OpenTheory.Name) : String :=
  if name.namespaceComponents.isEmpty && !name.component.startsWith "$" then name.component
  else "$[[" ++ String.intercalate "," (name.namespaceComponents.map asciiQuoted) ++
    "]," ++ asciiQuoted name.component ++ "]"

/-- Unsigned LEB128. The receiver's admitted integer range is checked when
an instruction is emitted. -/
def varint (value : Nat) : ByteArray := Id.run do
  let mut value := value
  let mut result := ByteArray.empty
  repeat
    let byte := value % 128
    value := value / 128
    result := result.push (UInt8.ofNat (byte + if value == 0 then 0 else 128))
    if value == 0 then break
  return result

private def digestBytes (text : String) : Except String ByteArray := do
  unless text.length == 64 do throw "invalid source digest length"
  let digits := text.toList.toArray
  let mut bytes := ByteArray.empty
  for index in [:32] do
    let high := digits[index * 2]!.toNat
    let low := digits[index * 2 + 1]!.toNat
    let decode := fun n => if 48 ≤ n && n ≤ 57 then some (n - 48)
      else if 97 ≤ n && n ≤ 102 then some (n - 87) else none
    let some high := decode high | throw "invalid source digest digit"
    let some low := decode low | throw "invalid source digest digit"
    bytes := bytes.push (UInt8.ofNat (16 * high + low))
  return bytes

structure State where
  bytes : ByteArray := .empty
  records : Nat := 0
  names : Std.HashMap String Nat := {}
  types : Std.HashMap TypeNode Nat := {}
  terms : Std.HashMap NamedNode Nat := {}
  namedPointers : Std.HashMap USize Nat := {}
  retainedNamed : Array SourceTerm := #[]
  canonicalPointers : Std.HashMap USize Nat := {}
  retainedCanonical : Array DBTerm := #[]
  declaredTypes : Std.HashSet String := {"bool", "fun"}
  declaredConstants : Std.HashSet String := {"="}
  theorems : Nat := 0
  axioms : Array (Nat × Sequent) := #[]

abbrev Write := StateT State (Except String)

def initial (policy : Policy) (sourceDigest : String) : Except String State := do
  let digest ← digestBytes sourceDigest
  return {bytes := "HOLRPLY1".toUTF8 ++ digest ++ varint 1 ++ varint 0 ++
    varint policy.number ++ varint 0}

private def append (bytes : ByteArray) : Write Unit :=
  modify fun state => {state with bytes := state.bytes ++ bytes}

def record (opcode : UInt8) (arguments : List Nat) : Write Unit := do
  let mut bytes := ByteArray.empty.push opcode
  for argument in arguments do
    unless argument < 2^62 do throw "native integer range exceeded"
    bytes := bytes ++ varint argument
  append bytes
  modify fun state => {state with records := state.records + 1}

def internName (name : String) : Write Nat := do
  if let some index := (← get).names[name]? then return index
  let index := (← get).names.size
  let word := name.toUTF8
  append ((ByteArray.empty.push 1) ++ varint word.size ++ word)
  modify fun state => {state with
    records := state.records + 1
    names := state.names.insert name index}
  return index

partial def internType : Ty → Write Nat
  | .var name => do
      let name ← internName (nativeName name)
      let key := TypeNode.variable name
      if let some index := (← get).types[key]? then return index
      record 2 [name]
      let index := (← get).types.size
      modify fun state => {state with types := state.types.insert key index}
      return index
  | .op (.mk name _) arguments => do
      let name := nativeName name
      let name := if name == "->" then "fun" else name
      unless (← get).declaredTypes.contains name do throw s!"undeclared native type {name}"
      let name ← internName name
      let arguments ← arguments.mapM internType
      let key := TypeNode.operator name arguments
      if let some index := (← get).types[key]? then return index
      record 3 (name :: arguments.length :: arguments)
      let index := (← get).types.size
      modify fun state => {state with types := state.types.insert key index}
      return index

private def internNode (key : NamedNode) : Write Nat := do
  if let some index := (← get).terms[key]? then return index
  match key with
  | .variable name type => record 4 [name, type]
  | .constant name type => record 5 [name, type]
  | .application function argument => record 6 [function, argument]
  | .abstraction name type body =>
      let binder ← internNode (.variable name type)
      record 7 [binder, body]
  let index := (← get).terms.size
  modify fun state => {state with terms := state.terms.insert key index}
  return index
termination_by match key with | .abstraction .. => 1 | _ => 0

unsafe def internTerm (term : SourceTerm) : Write Nat := do
  let pointer := ptrAddrUnsafe term
  if let some index := (← get).namedPointers[pointer]? then return index
  let index ← match term with
  | .var name type => internNode (.variable (← internName (nativeName name)) (← internType type))
  | .const (.mk name _) type => do
      let name := nativeName name
      unless (← get).declaredConstants.contains name do throw s!"undeclared native constant {name}"
      internNode (.constant (← internName name) (← internType type))
  | .app function argument => internNode (.application (← internTerm function) (← internTerm argument))
  | .abs name type body =>
      internNode (.abstraction (← internName (nativeName name)) (← internType type) (← internTerm body))
  modify fun state => {state with
    namedPointers := state.namedPointers.insert pointer index
    retainedNamed := state.retainedNamed.push term}
  return index

unsafe def internCanonical (term : CanonicalTerm) : Write Nat := do
  let pointer := ptrAddrUnsafe term.term
  if let some index := (← get).canonicalPointers[pointer]? then return index
  let index ← internTerm (PrimitiveTransport.checkedSource term).source
  modify fun state => {state with
    canonicalPointers := state.canonicalPointers.insert pointer index
    retainedCanonical := state.retainedCanonical.push term.term}
  return index

def State.clearPointers (state : State) : State :=
  {state with namedPointers := {}, retainedNamed := #[], canonicalPointers := {}, retainedCanonical := #[]}

def declareType (name : Mettapedia.Languages.OpenTheory.Name) (arity : Nat) : Write Unit := do
  let name := nativeName name
  let name := if name == "->" then "fun" else name
  if (← get).declaredTypes.contains name then
    unless (name == "fun" && arity == 2) || (name == "bool" && arity == 0) do
      throw s!"duplicate native type {name}"
    return
  record 0x20 [← internName name, arity]
  modify fun state => {state with declaredTypes := state.declaredTypes.insert name}

def declareConstant (name : Mettapedia.Languages.OpenTheory.Name) (type : Ty) : Write Unit := do
  let name := nativeName name
  if (← get).declaredConstants.contains name then
    unless name == "=" do throw s!"duplicate native constant {name}"
    return
  record 0x21 [← internName name, ← internType type]
  modify fun state => {state with declaredConstants := state.declaredConstants.insert name}

private def existing (index : Nat) : Write Unit := do
  unless index < (← get).theorems do throw s!"future native theorem reference {index}"

private def allocate (count : Nat) : Write Nat := do
  let index := (← get).theorems
  modify fun state => {state with theorems := state.theorems + count}
  return index

unsafe def checkTheorem (index : Nat) (fact : Theorem) : Write Unit := do
  existing index
  let hypotheses ← fact.sequent.hyp.val.unquot.mapM internCanonical
  let conclusion ← internCanonical fact.sequent.concl
  record 0x35 (index :: hypotheses.length :: hypotheses ++ [conclusion])
  let dependencies ← fact.axioms.val.unquot.mapM fun premise => do
    let some source := (← get).axioms.find? (fun source => source.2 == premise) |
      throw "unregistered native axiom dependency"
    return source.1
  record 0x34 (index :: dependencies.length :: dependencies)

unsafe def receipt (node : ProofExecution.Receipt) (checkOutput : Bool := true) : Write Nat := do
  for parent in node.parents do existing parent
  let arity := node.witness.premises.length
  unless node.parents.length == arity do throw "wrong native receipt arity"
  match node.witness with
  | .axiom sequent =>
      unless sequent.hyp.card == 0 do throw "native axiom has hypotheses"
      if let some source := (← get).axioms.find? (fun source => source.2 == sequent) then
        record 0x19 [0, source.1]
      else
        record 0x22 [← internCanonical sequent.concl]
        modify fun state => {state with axioms := state.axioms.push (state.theorems, sequent)}
  | .inference request =>
      match request with
      | .refl term => record 0x10 [← internCanonical term]
      | .trans .. => record 0x11 node.parents
      | .mkComb .. => record 0x12 node.parents
      | .abs binder _ => record 0x13 ((← internTerm (.var binder.name binder.ty)) :: node.parents)
      | .beta term => record 0x14 [← internTerm term.source]
      | .assume term => record 0x15 [← internCanonical term]
      | .eqMp .. => record 0x16 node.parents
      | .deductAntisym .. => record 0x17 node.parents
      | .instType entries _ =>
          let pairs ← entries.mapM fun (replacement, original) => do
            return [← internType replacement, ← internType original]
          record 0x18 (entries.length :: pairs.flatten ++ node.parents)
      | .inst entries _ =>
          let pairs ← entries.mapM fun (replacement, original) => do
            return [← internTerm replacement.source, ← internTerm original]
          record 0x19 (entries.length :: pairs.flatten ++ node.parents)
  let index ← allocate 1
  if checkOutput then checkTheorem index node.conclusion
  return index

unsafe def command (item : ProofExecution.Registered.CommandReceipt) : Write Unit := do
  let start := (← get).theorems
  let expected ← match item.command with
    | .proof node _ => do
        let _ ← receipt node false
        pure 1
    | .constant _ name body _ => do
        let some type := body.inferType | throw "ill-typed definition body"
        let equality := SourceTerm.const Const.equality (Ty.function type (Ty.function type Ty.bool))
        let equation := SourceTerm.app (.app equality (.var name type)) body
        record 0x23 [← internTerm equation]
        let _ ← allocate 1
        modify fun state => {state with declaredConstants := state.declaredConstants.insert (nativeName name)}
        pure 1
    | .typeDefinition _ request existenceIndex _ => do
        existing existenceIndex
        let typeName := nativeName request.typeName
        let typeName := if typeName == "->" then "fun" else typeName
        record 0x24 [← internName typeName,
          ← internName (nativeName request.abstractionName),
          ← internName (nativeName request.representationName), existenceIndex]
        let _ ← allocate 2
        modify fun state => {state with
          declaredTypes := state.declaredTypes.insert typeName
          declaredConstants := (state.declaredConstants.insert (nativeName request.abstractionName)).insert
            (nativeName request.representationName)}
        pure 2
  unless item.outputs.length == expected do throw "wrong native command output count"
  for (fact, offset) in item.outputs.zipIdx do checkTheorem (start + offset) fact

/-- Ask the receiver to publish an already allocated theorem occurrence. -/
def emitRoot (index : Nat) : Write Unit := do
  existing index
  record 0x32 [index]

def finish (state : State) : ByteArray := Id.run do
  let mut checksum : UInt64 := 14695981039346656037
  for byte in state.bytes do checksum := (checksum ^^^ byte.toUInt64) * 1099511628211
  let mut bytes := state.bytes ++ (ByteArray.empty.push 0x7f) ++ varint state.records
  for offset in [:8] do bytes := bytes.push (checksum >>> (8 * offset).toUInt64).toUInt8
  return bytes

end Mettapedia.Languages.HOLLight.NativeCertificateExport
