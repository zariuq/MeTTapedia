import Mettapedia.Languages.VibeITP.Native.BinaryInstruction

/-!
# Complete byte-stream correspondence

The declared binary reader and strict instruction projection are iterated to
the end of a file. The recursion bound is the number of input bytes, justified
by consumption of an opcode on every iteration; it is not a guest limit.
Malformed input returns one failure for the whole file.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.BinaryFile

open Mettapedia.GSLT.Parsing

def embed {α : Type} : Except Spec.DecodeError α → Except BinaryRecordCodec.Error α
  | .error error => .error (BinaryDecoder.embedError error)
  | .ok value => .ok value

def stream : Nat → List UInt8 → Except BinaryRecordCodec.Error (List Spec.Instr)
  | _, [] => .ok []
  | 0, _ :: _ => .ok []
  | fuel + 1, opcode :: bytes =>
      match BinaryInstruction.readOperands opcode.toNat bytes with
      | .error error => .error error
      | .ok (instruction, rest) =>
          match stream fuel rest with
          | .error error => .error error
          | .ok instructions => .ok (instruction :: instructions)

def file (bytes : List UInt8) : Except BinaryRecordCodec.Error (List Spec.Instr) :=
  stream bytes.length bytes

theorem stream_correct (fuel : Nat) (bytes : List UInt8) :
    stream fuel bytes = embed (Spec.decodeStream fuel bytes) := by
  induction fuel generalizing bytes with
  | zero => cases bytes <;> rfl
  | succ fuel ih =>
    cases bytes with
    | nil => rfl
    | cons opcode bytes =>
      simp only [stream, BinaryInstruction.operands_correct, Spec.decodeStream]
      cases decoded : Spec.decodeOperands opcode.toNat bytes with
      | error error => simp [BinaryDecoder.lift, embed, decoded]
      | ok result =>
        rcases result with ⟨instruction, rest⟩
        rw [show BinaryDecoder.lift (Spec.decodeOperands opcode.toNat) bytes =
            .ok (instruction, rest) by simp [BinaryDecoder.lift, decoded]]
        dsimp only
        rw [ih]
        cases remainder : Spec.decodeStream fuel rest <;> rfl

theorem file_correct (bytes : List UInt8) : file bytes = embed (Spec.decodeFile bytes) :=
  stream_correct bytes.length bytes

theorem successful_file_iff (bytes : List UInt8) (instructions : List Spec.Instr) :
    file bytes = .ok instructions ↔ Spec.decodeFile bytes = .ok instructions := by
  rw [file_correct]
  cases decoded : Spec.decodeFile bytes <;> simp [embed]

theorem rejected_file_iff (bytes : List UInt8) (error : Spec.DecodeError) :
    file bytes = .error (BinaryDecoder.embedError error) ↔
      Spec.decodeFile bytes = .error error := by
  rw [file_correct]
  cases decoded : Spec.decodeFile bytes with
  | ok instructions => simp [embed]
  | error found =>
    cases found <;> cases error <;> simp [embed, BinaryDecoder.embedError]

theorem recursion_bound_irrelevant (fuel fuel' : Nat) (bytes : List UInt8)
    (enough : bytes.length ≤ fuel) (enough' : bytes.length ≤ fuel') :
    stream fuel bytes = stream fuel' bytes := by
  rw [stream_correct, stream_correct, Spec.decodeStream_fuel fuel fuel' bytes enough enough']

theorem complete_file_not_published_after_late_error :
    file [0, 0, 1, 26] = .error (.unknownOpcode 26) := by
  rw [file_correct]
  decide

theorem nonshortest_file_accepted :
    file [0, 248, 0, 247] = .ok [.fvarNew 0 247] := by
  rw [file_correct]
  decide

theorem truncated_word_refused : file [0, 255, 0] = .error .truncatedWord := by
  rw [file_correct]
  decide

theorem truncated_literal_refused : file [5, 2, 10] = .error .truncatedBytes := by
  rw [file_correct]
  decide

theorem truncated_counted_words_refused : file [1, 2, 0] = .error .truncatedWord := by
  rw [file_correct]
  decide

end Mettapedia.Languages.VibeITP.Native.BinaryFile
