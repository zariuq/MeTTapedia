import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Declared binary record decoding

The direct native reader consumes a prefix byte, bounded little-endian word
payloads, counted byte views and counted word views. This module gives those
operations a language-independent observation: decoded values, the exact
remaining suffix, or the first decoding failure. Payload decoding uses a
bulk prefix/suffix split, independently of recursive certificate parsers.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.BinaryRecordCodec

structure WordCodec where
  inlineMax : Nat
  payloadMax : Nat
  requireShortest : Bool
  deriving DecidableEq, Repr

def WordCodec.Valid (codec : WordCodec) : Prop :=
  codec.inlineMax ≤ 254 ∧ 1 ≤ codec.payloadMax ∧ codec.payloadMax ≤ 8 ∧
    codec.inlineMax + codec.payloadMax ≤ 255

instance (codec : WordCodec) : Decidable codec.Valid :=
  inferInstanceAs (Decidable (codec.inlineMax ≤ 254 ∧ 1 ≤ codec.payloadMax ∧
    codec.payloadMax ≤ 8 ∧ codec.inlineMax + codec.payloadMax ≤ 255))

inductive Error where
  | truncatedWord
  | truncatedBytes
  | invalidHeader
  | noncanonicalWord
  | unknownOpcode (opcode : Nat)
  deriving DecidableEq, Repr

abbrev Reader (α : Type) := List UInt8 → Except Error (α × List UInt8)

def pure {α : Type} (value : α) : Reader α := fun bytes => .ok (value, bytes)

def bind {α β : Type} (reader : Reader α) (next : α → Reader β) : Reader β :=
  fun bytes => match reader bytes with
    | .error error => .error error
    | .ok (value, rest) => next value rest

def map {α β : Type} (f : α → β) (reader : Reader α) : Reader β :=
  bind reader (fun value => pure (f value))

@[simp] theorem bind_pure_left {α β : Type} (value : α) (next : α → Reader β) :
    bind (pure value) next = next value := rfl

@[simp] theorem bind_pure_right {α : Type} (reader : Reader α) :
    bind reader pure = reader := by
  funext bytes
  cases decoded : reader bytes <;> simp [bind, pure, decoded]

theorem bind_assoc {α β γ : Type} (reader : Reader α) (next : α → Reader β)
    (following : β → Reader γ) :
    bind (bind reader next) following =
      bind reader (fun value => bind (next value) following) := by
  funext bytes
  cases decoded : reader bytes <;> simp [bind, decoded]

@[simp] theorem bind_map {α β γ : Type} (f : α → β) (reader : Reader α)
    (next : β → Reader γ) :
    bind (map f reader) next = bind reader (fun value => next (f value)) := by
  rw [map, bind_assoc]
  rfl

def littleEndian : List UInt8 → Nat
  | [] => 0
  | byte :: bytes => byte.toNat + 256 * littleEndian bytes

def payload (count : Nat) : Reader Nat := fun bytes =>
  if bytes.length < count then .error .truncatedWord
  else .ok (littleEndian (bytes.take count), bytes.drop count)

def word (codec : WordCodec) : Reader Nat := fun bytes =>
  match bytes with
  | [] => .error .truncatedWord
  | header :: bytes =>
    if header.toNat ≤ codec.inlineMax then .ok (header.toNat, bytes)
    else
      let count := header.toNat - codec.inlineMax
      if count > codec.payloadMax then .error .invalidHeader
      else bind (payload count) (fun value => fun rest =>
        if codec.requireShortest &&
            (value ≤ codec.inlineMax || (bytes.take count).getLast? == some 0) then
          .error .noncanonicalWord
        else .ok (value, rest)) bytes

def words (codec : WordCodec) : Nat → Reader (List Nat)
  | 0 => pure []
  | count + 1 => bind (word codec) (fun value =>
      bind (words codec count) (fun values => pure (value :: values)))

def raw (count : Nat) : Reader (List UInt8) := fun bytes =>
  if bytes.length < count then .error .truncatedBytes
  else .ok (bytes.take count, bytes.drop count)

inductive OperandKind where
  | word | countedBytes | countedWords
  deriving DecidableEq, Repr

structure OperandLayout where
  kind : OperandKind
  role : String
  deriving DecidableEq, Repr

structure OpcodeLayout where
  opcode : Nat
  label : String
  operands : List OperandLayout
  deriving DecidableEq, Repr

structure Grammar where
  codec : WordCodec
  opcodes : List OpcodeLayout
  deriving DecidableEq, Repr

inductive Operand where
  | word (value : Nat)
  | bytes (value : List UInt8)
  | words (value : List Nat)
  deriving DecidableEq, Repr

def operand (codec : WordCodec) : OperandKind → Reader Operand
  | .word => map Operand.word (word codec)
  | .countedBytes => map Operand.bytes (bind (word codec) raw)
  | .countedWords => map Operand.words (bind (word codec) (words codec))

def fields (codec : WordCodec) : List OperandLayout → Reader (List Operand)
  | [] => pure []
  | field :: rest => bind (operand codec field.kind) (fun value =>
      bind (fields codec rest) (fun values => pure (value :: values)))

structure Record where
  opcode : Nat
  operands : List Operand
  deriving DecidableEq, Repr

def lookup (grammar : Grammar) (opcode : Nat) : Option OpcodeLayout :=
  grammar.opcodes.find? (fun layout => layout.opcode == opcode)

def operands (grammar : Grammar) (opcode : Nat) : Reader Record :=
  match lookup grammar opcode with
  | none => fun _ => .error (.unknownOpcode opcode)
  | some layout => map (Record.mk opcode) (fields grammar.codec layout.operands)

def record (grammar : Grammar) : Reader Record := fun bytes =>
  match bytes with
  | [] => .error .truncatedWord
  | opcode :: rest => operands grammar opcode.toNat rest

def Consumes {α : Type} (reader : Reader α) : Prop :=
  ∀ bytes value rest, reader bytes = .ok (value, rest) → rest.length ≤ bytes.length

@[simp] theorem pure_consumes {α : Type} (value : α) : Consumes (pure value) := by
  intro bytes value' rest accepted
  simp only [pure, Except.ok.injEq, Prod.mk.injEq] at accepted
  rw [← accepted.2]

theorem bind_consumes {α β : Type} {reader : Reader α} {next : α → Reader β}
    (first : Consumes reader) (following : ∀ value, Consumes (next value)) :
    Consumes (bind reader next) := by
  intro bytes value rest accepted
  unfold bind at accepted
  split at accepted
  · contradiction
  · rename_i current middle decoded
    exact (following current middle value rest accepted).trans
      (first bytes current middle decoded)

theorem map_consumes {α β : Type} (f : α → β) {reader : Reader α}
    (first : Consumes reader) : Consumes (map f reader) :=
  bind_consumes first (fun _ => pure_consumes _)

theorem payload_consumes (count : Nat) : Consumes (payload count) := by
  intro bytes value rest accepted
  unfold payload at accepted
  split at accepted
  · contradiction
  · cases accepted
    simp

theorem raw_consumes (count : Nat) : Consumes (raw count) := by
  intro bytes value rest accepted
  unfold raw at accepted
  split at accepted
  · contradiction
  · cases accepted
    simp

theorem littleEndian_lt (bytes : List UInt8) :
    littleEndian bytes < 256 ^ bytes.length := by
  induction bytes with
  | nil => simp [littleEndian]
  | cons byte bytes ih =>
    have bound : byte.toNat < 256 := byte.toNat_lt
    simp only [littleEndian, List.length_cons, pow_succ]
    omega

theorem payload_value_bound {count : Nat} {bytes rest : List UInt8} {value : Nat}
    (accepted : payload count bytes = .ok (value, rest)) : value < 256 ^ count := by
  unfold payload at accepted
  split at accepted
  · contradiction
  · rename_i enough
    cases accepted
    have count_le : count ≤ bytes.length := by omega
    simpa [List.length_take, Nat.min_eq_left count_le] using littleEndian_lt (bytes.take count)

theorem payload_zero (bytes : List UInt8) : payload 0 bytes = .ok (0, bytes) := by
  simp [payload, littleEndian]

theorem payload_succ_empty (count : Nat) :
    payload (count + 1) [] = .error .truncatedWord := by
  simp [payload]

theorem payload_succ (count : Nat) (byte : UInt8) (bytes : List UInt8) :
    payload (count + 1) (byte :: bytes) =
      bind (payload count) (fun high => pure (byte.toNat + 256 * high)) bytes := by
  simp only [payload, bind, pure, List.length_cons]
  by_cases truncated : bytes.length < count
  · simp [truncated, show bytes.length + 1 < count + 1 by omega]
  · simp [truncated, show ¬ bytes.length + 1 < count + 1 by omega,
      List.take_succ_cons, List.drop_succ_cons, littleEndian]

example : word ⟨247, 8, false⟩ [248, 0] = .ok (0, []) := by decide

example : word ⟨247, 8, true⟩ [248, 0] = .error .noncanonicalWord := by decide

example : word ⟨247, 8, false⟩ [255, 0] = .error .truncatedWord := by decide

end Mettapedia.GSLT.Parsing.BinaryRecordCodec
