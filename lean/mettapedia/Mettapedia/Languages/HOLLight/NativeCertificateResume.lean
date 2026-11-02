import Mettapedia.Languages.HOLLight.NativeCertificateExport

/-!
# Resuming the native certificate producer from its interned wire prefix

This reconstructs producer dictionaries and allocation counters. It accepts
the writer's canonical interned representation and checks bounds, framing and
the existing checksum. It does not check proof inferences. The complete joined
stream must still be replayed by the native receiver, with exact assertions
for every imported theorem value used by a later proof.

Axiom sequents, when present, are supplied explicitly by the caller. Their
indices must match the wire allocations; their contents remain untrusted
until asserted and checked by the receiver. Definitions and type definitions
restore declaration inventories without adding another inference engine.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.NativeCertificateResume
open Mettapedia.Languages.OpenTheory
open SharedCertificateExport (TypeNode NamedNode)
open NativeCertificateExport

structure Restored where
  writer : NativeCertificateExport.State
  roots : Array Nat

private structure Cursor where
  input : ByteArray
  offset : Nat
  writer : NativeCertificateExport.State
  nameValues : Array String := #[]
  termValues : Array NamedNode := #[]
  roots : Array Nat := #[]

private abbrev Read := StateT Cursor (Except String)

private def byte : Read UInt8 := do
  let cursor ← get
  let some value := cursor.input[cursor.offset]? | throw "truncated native certificate"
  set {cursor with offset := cursor.offset + 1}
  return value

private def remaining : Read Nat := do
  let cursor ← get
  return cursor.input.size - cursor.offset

private def take (count : Nat) : Read ByteArray := do
  let cursor ← get
  unless count ≤ cursor.input.size - cursor.offset do throw "truncated native byte field"
  set {cursor with offset := cursor.offset + count}
  return cursor.input.extract cursor.offset (cursor.offset + count)

private def nat : Read Nat := do
  let start := (← get).offset
  let rec go : Nat → Nat → Nat → Read Nat
    | 0, _, _ => throw "native integer is too wide"
    | fuel + 1, shift, value => do
      let next ← byte
      let value := value + (next.toNat % 128) * 2^shift
      if next.toNat < 128 then
        unless value < 2^62 do throw "native integer range exceeded"
        return value
      go fuel (shift + 7) value
  let value ← go 9 0 0
  let cursor ← get
  unless cursor.input.extract start cursor.offset == varint value do throw "noncanonical native integer"
  return value

private def reference (bound : Nat) (kind : String) : Read Nat := do
  let value ← nat
  unless value < bound do throw s!"future native {kind} reference"
  return value
private def nameRef : Read Nat := do reference (← get).nameValues.size "name"
private def typeRef : Read Nat := do reference (← get).writer.types.size "type"
private def termRef : Read Nat := do reference (← get).termValues.size "term"
private def theoremRef : Read Nat := do reference (← get).writer.theorems "theorem"

private def counted (action : Read Nat) : Read (List Nat) := do
  let count ← nat
  unless count ≤ (← remaining) do throw "oversized native reference list"
  let mut values := []
  for _ in [:count] do values := (← action) :: values
  return values.reverse

private def addType (node : TypeNode) : Read Unit := do
  let cursor ← get
  if cursor.writer.types.contains node then throw "duplicate interned native type"
  set {cursor with writer := {cursor.writer with types := cursor.writer.types.insert node cursor.writer.types.size}}

private def addTerm (node : NamedNode) : Read Unit := do
  let cursor ← get
  if cursor.writer.terms.contains node then throw "duplicate interned native term"
  set {cursor with writer := {cursor.writer with terms := cursor.writer.terms.insert node cursor.termValues.size}, termValues := cursor.termValues.push node}

private def allocate (count : Nat) : Read Unit :=
  modify fun cursor => {cursor with writer := {cursor.writer with theorems := cursor.writer.theorems + count}}

private def declareTypeName (name : Nat) : Read Unit := do
  let cursor ← get
  let some word := cursor.nameValues[name]? | throw "unknown native type name"
  if cursor.writer.declaredTypes.contains word then throw "duplicate native type declaration"
  set {cursor with writer := {cursor.writer with declaredTypes := cursor.writer.declaredTypes.insert word}}
private def declareConstantName (name : Nat) : Read Unit := do
  let cursor ← get
  let some word := cursor.nameValues[name]? | throw "unknown native constant name"
  if cursor.writer.declaredConstants.contains word then throw "duplicate native constant declaration"
  set {cursor with writer := {cursor.writer with declaredConstants := cursor.writer.declaredConstants.insert word}}

private def definitionName (term : Nat) : Read Nat := do
  let cursor ← get
  let some (.application left _) := cursor.termValues[term]? | throw "invalid native definition equation"
  let some (.application equality lhs) := cursor.termValues[left]? | throw "invalid native definition lhs"
  let some (.constant name _) := cursor.termValues[equality]? | throw "invalid native definition equality"
  unless cursor.nameValues[name]? == some "=" do throw "invalid native definition equality name"
  let some (.variable name _) := cursor.termValues[lhs]? | throw "invalid native defined variable"
  return name

private def instruction (axioms : Array (Nat × Sequent)) (opcode : UInt8) : Read Unit := do
  match opcode.toNat with
  | 1 =>
    let count ← nat
    let word ← take count
    let some word := String.fromUTF8? word | throw "invalid native UTF-8 name"
    let cursor ← get
    if cursor.writer.names.contains word then throw "duplicate interned native name"
    set {cursor with nameValues := cursor.nameValues.push word, writer := {cursor.writer with names := cursor.writer.names.insert word cursor.nameValues.size}}
  | 2 => do addType (.variable (← nameRef))
  | 3 =>
    let name ← nameRef
    let arguments ← counted typeRef
    let some word := (← get).nameValues[name]? | throw "unknown native operator name"
    unless (← get).writer.declaredTypes.contains word do throw "undeclared native type operator"
    addType (.operator name arguments)
  | 4 => do addTerm (.variable (← nameRef) (← typeRef))
  | 5 =>
    let name ← nameRef
    let type ← typeRef
    let some word := (← get).nameValues[name]? | throw "unknown native constant name"
    unless (← get).writer.declaredConstants.contains word do throw "undeclared native term constant"
    addTerm (.constant name type)
  | 6 => do addTerm (.application (← termRef) (← termRef))
  | 7 =>
    let binder ← termRef
    let body ← termRef
    let some (.variable name type) := (← get).termValues[binder]? | throw "native abstraction binder is not a variable"
    addTerm (.abstraction name type body)
  | 0x10 | 0x14 | 0x15 =>
    let _ ← termRef
    allocate 1
  | 0x11 | 0x12 | 0x16 | 0x17 =>
    let _ ← theoremRef
    let _ ← theoremRef
    allocate 1
  | 0x13 =>
    let _ ← termRef
    let _ ← theoremRef
    allocate 1
  | 0x18 | 0x19 =>
    let count ← nat
    unless count * 2 + 1 ≤ (← remaining) do throw "oversized native substitution"
    for _ in [:count] do
      let _ ← if opcode.toNat == 0x18 then typeRef else termRef
      let _ ← if opcode.toNat == 0x18 then typeRef else termRef
    let _ ← theoremRef
    allocate 1
  | 0x20 =>
    let name ← nameRef
    let _arity ← nat
    declareTypeName name
  | 0x21 =>
    let name ← nameRef
    let _type ← typeRef
    declareConstantName name
  | 0x22 =>
    let _conclusion ← termRef
    let cursor ← get
    let some (index,sequent) := axioms[cursor.writer.axioms.size]? | throw "missing native axiom manifest"
    unless index == cursor.writer.theorems do throw "native axiom manifest index mismatch"
    set {cursor with writer := {cursor.writer with axioms := cursor.writer.axioms.push (index,sequent)}}
    allocate 1
  | 0x23 =>
    let equation ← termRef
    declareConstantName (← definitionName equation)
    allocate 1
  | 0x24 =>
    let name ← nameRef
    let abstraction ← nameRef
    let representation ← nameRef
    let _existence ← theoremRef
    declareTypeName name
    declareConstantName abstraction
    declareConstantName representation
    allocate 2
  | 0x32 =>
    let root ← theoremRef
    modify fun cursor => {cursor with roots := cursor.roots.push root}
  | 0x34 =>
    let _source ← theoremRef
    let dependencies ← counted theoremRef
    for dependency in dependencies do
      unless (← get).writer.axioms.any (fun source => source.1 == dependency) do
        throw "native dependency is not a declared axiom"
  | 0x35 =>
    let _source ← theoremRef
    let _hypotheses ← counted termRef
    let _conclusion ← termRef
  | _ => throw "unknown native certificate opcode"
  modify fun cursor => {cursor with writer := {cursor.writer with records := cursor.writer.records + 1}}

private def scan (axioms : Array (Nat × Sequent)) : Nat → Read Restored
  | 0 => throw "native certificate has no footer"
  | fuel + 1 => do
    let start := (← get).offset
    let opcode ← byte
    if opcode.toNat == 0x7f then
      let count ← nat
      let _checksum ← take 8
      let cursor ← get
      unless cursor.offset == cursor.input.size do throw "trailing native certificate bytes"
      unless count == cursor.writer.records do throw "native record count mismatch"
      unless cursor.writer.axioms.size == axioms.size do throw "unused native axiom manifest entry"
      let writer := {cursor.writer with bytes := cursor.input.extract 0 start}
      unless finish writer == cursor.input do throw "native checksum or framing mismatch"
      return ⟨writer.clearPointers,cursor.roots⟩
    instruction axioms opcode
    scan axioms fuel

/-- Restore only producer state. Proof validity and imported theorem values
are established by replaying the complete stream in the native receiver. -/
def restore (policy : Policy) (sourceDigest : String) (input : ByteArray)
    (axioms : Array (Nat × Sequent) := #[]) : Except String Restored := do
  let writer ← initial policy sourceDigest
  unless writer.bytes == input.extract 0 writer.bytes.size do throw "native prefix header mismatch"
  let cursor : Cursor := {input := input,offset := writer.bytes.size,writer := writer}
  return (← (scan axioms input.size).run cursor).1

end Mettapedia.Languages.HOLLight.NativeCertificateResume
