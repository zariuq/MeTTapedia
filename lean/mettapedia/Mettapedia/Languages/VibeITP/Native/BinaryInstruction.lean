import Mettapedia.Languages.VibeITP.Native.BinaryDecoder

/-! Declared binary records correspond to all 26 independent instructions. -/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace Mettapedia.Languages.VibeITP.Native.BinaryInstruction

open Mettapedia.GSLT.Parsing
open BinaryRecordCodec

def instruction? : Record → Option Spec.Instr
  | ⟨0, [.word arity, .word dst]⟩ => some (.fvarNew arity dst)
  | ⟨1, [.words binders, .word dst]⟩ => some (.constNew binders dst)
  | ⟨2, [.word first, .word second]⟩ => some (.symbolSwap first second)
  | ⟨3, [.word slot]⟩ => some (.symbolFree slot)
  | ⟨4, [.word index, .word dst]⟩ => some (.termNewBVar index dst)
  | ⟨5, [.bytes bytes, .word dst]⟩ => some (.termNewLiteral bytes dst)
  | ⟨6, [.word symbol, .words arguments, .word dst]⟩ => some (.termNewApp symbol arguments dst)
  | ⟨7, [.word first, .word second]⟩ => some (.termSwap first second)
  | ⟨8, [.word slot]⟩ => some (.termFree slot)
  | ⟨9, [.word statement, .word dst]⟩ => some (.addAxiom statement dst)
  | ⟨10, [.word theoremSlot, .word statement]⟩ => some (.thmExchange theoremSlot statement)
  | ⟨11, [.word slot]⟩ => some (.thmFree slot)
  | ⟨12, [.word first, .word second]⟩ => some (.thmSwap first second)
  | ⟨13, [.word statement, .word dst]⟩ => some (.challengeAdd statement dst)
  | ⟨14, [.word challenge, .word theoremSlot]⟩ => some (.challengeSatisfy challenge theoremSlot)
  | ⟨15, [.word implication, .word premise, .word dst]⟩ => some (.modusPonens implication premise dst)
  | ⟨16, [.word theoremSlot, .word fvar, .word value, .word dst]⟩ =>
      some (.thmInstantiate theoremSlot fvar value dst)
  | ⟨17, [.words fvars, .words hints, .word value, .word dstSymbol, .word dstTheorem]⟩ =>
      some (.defineConst fvars hints value dstSymbol dstTheorem)
  | ⟨18, [.word value, .word dst]⟩ => some (.litIsNat value dst)
  | ⟨19, [.word first, .word second, .word dst]⟩ => some (.litLt first second dst)
  | ⟨20, [.word first, .word second, .word dst]⟩ => some (.litAdd first second dst)
  | ⟨21, [.word first, .word second, .word dst]⟩ => some (.litMul first second dst)
  | ⟨22, [.word first, .word second, .word dst]⟩ => some (.litDiv first second dst)
  | ⟨23, [.word term, .word dst]⟩ => some (.litLength term dst)
  | ⟨24, [.word term, .word index, .word dst]⟩ => some (.litGet term index dst)
  | ⟨25, [.word safe, .word dst, .word dstTerm]⟩ => some (.jit safe dst dstTerm)
  | _ => none

def readOperands (opcode : Nat) : Reader Spec.Instr :=
  bind (operands GeneratedBinarySource.grammar opcode) (fun record =>
    match instruction? record with
    | none => fun _ => .error (.unknownOpcode opcode)
    | some instruction => pure instruction)

theorem unknown_lookup (opcode : Nat) (unknown : 26 ≤ opcode) :
    lookup GeneratedBinarySource.grammar opcode = none := by
  apply List.find?_eq_none.mpr
  intro layout member
  have inventory : GeneratedBinarySource.grammar.opcodes.map OpcodeLayout.opcode =
      List.range 26 := by decide
  have opcodeMember : layout.opcode ∈ List.range 26 := by
    rw [← inventory]
    exact List.mem_map.mpr ⟨layout, member, rfl⟩
  have bound := List.mem_range.mp opcodeMember
  simp [show layout.opcode ≠ opcode by omega]

theorem operands_correct (opcode : Nat) :
    readOperands opcode = BinaryDecoder.lift (Spec.decodeOperands opcode) := by
  by_cases known : opcode < 26
  · interval_cases opcode <;>
      simp [readOperands, operands, lookup, GeneratedBinarySource.grammar,
        fields, operand, map, bind_assoc, instruction?,
        BinaryDecoder.word_pinned_correct, BinaryDecoder.raw_correct,
        BinaryDecoder.words_pinned_correct, Spec.decodeOperands, Spec.Parser.counted,
        BinaryDecoder.lift_bind, BinaryDecoder.lift_pure]
  · obtain ⟨extra, rfl⟩ : ∃ extra, opcode = extra + 26 := ⟨opcode - 26, by omega⟩
    rw [readOperands, operands, unknown_lookup (extra + 26) (by omega)]
    rfl

example : instruction? ⟨25, [.word 7, .word 8, .word 9]⟩ = some (.jit 7 8 9) := rfl

example : instruction? ⟨25, [.word 7, .bytes [8], .word 9]⟩ = none := rfl

end Mettapedia.Languages.VibeITP.Native.BinaryInstruction
