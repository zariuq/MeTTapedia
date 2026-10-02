import Mettapedia.Languages.VibeITP.Native.BinarySourceAdmission
import Mettapedia.Languages.VibeITP.Native.BinaryFile

/-!
# Source-admitted certificate file agreement

The source reader obtains a grammar from actual text. The generic record
interpreter then decodes each instruction with that grammar, preserving one
whole-file error on a malformed suffix. This endpoint composes source admission
with independent instruction and complete-file correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.SourceFileAgreement

open Mettapedia.GSLT.Parsing
open BinaryRecordCodec

def instruction (grammar : Grammar) : Reader Spec.Instr :=
  bind (record grammar) fun item =>
    match BinaryInstruction.instruction? item with
    | none => fun _ => .error (.unknownOpcode item.opcode)
    | some value => pure value

def stream (grammar : Grammar) : Nat → List UInt8 → Except Error (List Spec.Instr)
  | _, [] => .ok []
  | 0, _ :: _ => .ok []
  | fuel + 1, bytes =>
    match instruction grammar bytes with
    | .error error => .error error
    | .ok (value, rest) =>
      match stream grammar fuel rest with
      | .error error => .error error
      | .ok tail => .ok (value :: tail)

def fromSource (source : String) (bytes : List UInt8) : Option (Except Error (List Spec.Instr)) :=
  (BinaryRecordSource.binaryText? source).map fun grammar => stream grammar bytes.length bytes

theorem instruction_authored (opcode : UInt8) (bytes : List UInt8) :
    instruction GeneratedBinarySource.grammar (opcode :: bytes) =
      BinaryInstruction.readOperands opcode.toNat bytes := by
  unfold instruction record BinaryInstruction.readOperands BinaryRecordCodec.bind
  dsimp only
  cases decoded : operands GeneratedBinarySource.grammar opcode.toNat bytes with
  | error error => rfl
  | ok pair =>
    rcases pair with ⟨item, rest⟩
    have opcodeExact : item.opcode = opcode.toNat := by
      unfold operands at decoded
      cases lookupRead : lookup GeneratedBinarySource.grammar opcode.toNat with
      | none => simp [lookupRead] at decoded
      | some layout =>
        simp only [lookupRead] at decoded
        unfold BinaryRecordCodec.map BinaryRecordCodec.bind at decoded
        cases fieldsRead : fields GeneratedBinarySource.grammar.codec layout.operands bytes with
        | error error => simp [fieldsRead] at decoded
        | ok result =>
          rcases result with ⟨values, leftover⟩
          simp only [fieldsRead, BinaryRecordCodec.pure, Except.ok.injEq, Prod.mk.injEq] at decoded
          have itemEq := decoded.1
          exact (congrArg Record.opcode itemEq).symm
    cases value : BinaryInstruction.instruction? item <;> simp [value, opcodeExact]

theorem stream_authored (fuel : Nat) (bytes : List UInt8) :
    stream GeneratedBinarySource.grammar fuel bytes = BinaryFile.stream fuel bytes := by
  induction fuel generalizing bytes with
  | zero => cases bytes <;> rfl
  | succ fuel ih =>
    cases bytes with
    | nil => rfl
    | cons opcode bytes =>
      simp only [stream, BinaryFile.stream, instruction_authored]
      cases decoded : BinaryInstruction.readOperands opcode.toNat bytes with
      | error error => rfl
      | ok result =>
        rcases result with ⟨value, rest⟩
        dsimp only
        rw [ih]
        rfl

theorem fromSource_of_admitted (source : String) (grammar : Grammar) (bytes : List UInt8)
    (admitted : BinaryRecordSource.binaryText? source = some grammar) :
    fromSource source bytes = some (stream grammar bytes.length bytes) := by
  unfold fromSource
  rw [admitted]
  rfl

theorem authored_source_file_correct (bytes : List UInt8) :
    fromSource GeneratedBinarySource.authoredBinaryText bytes =
      some (BinaryFile.embed (Spec.decodeFile bytes)) := by
  rw [fromSource_of_admitted _ _ _ BinarySourceAdmission.authored_binary_source_exact,
    stream_authored]
  exact congrArg some (BinaryFile.file_correct bytes)

end Mettapedia.Languages.VibeITP.Native.SourceFileAgreement
