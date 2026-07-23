import Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
import Metamath.Verify

/-!
# Compressed action decoding agreement with mm-lean4

This file begins the implementation-refinement direction at the raw compressed
byte boundary.  The source decoder is independent.  The universal byte theorem
below relates it to the named per-byte transition used by the implementation;
the iterator and whole-program lifts remain separate theorems.
-/

namespace Mettapedia.Languages.Metamath.SourceGSLTCompressedMMLean4

open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Metamath.Verify

def toMMLean4Action :
    CompressedAction → ParserState.CompressedAction
  | .step index => .step index
  | .save => .save
  | .unknown => .unknown

theorem toMMLean4Action_injective :
    Function.Injective toMMLean4Action := by
  intro left right equal
  cases left <;> cases right <;> simp_all [toMMLean4Action]

def toMMLean4DecodeResult
    (result : Option (List CompressedAction × Nat)) :
    Except ProofCheckFail
      (List ParserState.CompressedAction × Nat) :=
  match result with
  | some (actions, accumulator) =>
      .ok (actions.map toMMLean4Action, accumulator)
  | none =>
      .error (.proofCheck .proofParseError)

def toMMLean4StepResult
    (reversedPrefix : List ParserState.CompressedAction)
    (result : Option (List CompressedAction × Nat)) :
    Except ProofCheckFail
      (List ParserState.CompressedAction × Nat) :=
  match result with
  | some (actions, accumulator) =>
      .ok (actions.reverse.map toMMLean4Action ++ reversedPrefix, accumulator)
  | none =>
      .error (.proofCheck .proofParseError)

/-- Universal local preservation and reflection theorem for every byte and
every incoming reverse-action prefix and numeric accumulator. -/
theorem decodeByte_mmLean4_agrees
    (reversedPrefix : List ParserState.CompressedAction)
    (accumulator : Nat) (byte : UInt8) :
    ParserState.decodeCompressedByte reversedPrefix accumulator byte =
      toMMLean4StepResult reversedPrefix
        (decodeByte accumulator byte) := by
  by_cases hAT : 65 ≤ byte.toNat ∧ byte.toNat ≤ 84
  · simp [ParserState.decodeCompressedByte, toMMLean4StepResult,
      decodeByte, toMMLean4Action, hAT]
  · by_cases hUY : 85 ≤ byte.toNat ∧ byte.toNat ≤ 89
    · simp [ParserState.decodeCompressedByte, toMMLean4StepResult,
        decodeByte, hAT, hUY]
    · by_cases hZ : byte.toNat = 90
      · simp [ParserState.decodeCompressedByte, toMMLean4StepResult,
          decodeByte, toMMLean4Action, hZ]
      · by_cases hUnknown : byte.toNat = 63
        · simp [ParserState.decodeCompressedByte, toMMLean4StepResult,
            decodeByte, toMMLean4Action, hUnknown]
        · simp [ParserState.decodeCompressedByte, toMMLean4StepResult,
            decodeByte, hAT, hUY, hZ, hUnknown]

/-- The exact byte sequence traversed by `decodeCompressedLoop`.  The
definition follows the implementation's remaining-count recursion, so no
external token ledger is assumed by the refinement theorem. -/
def sliceBytesLoop (tk : ByteSlice) :
    (remaining : Nat) → remaining ≤ tk.size → List UInt8
  | 0, _ => []
  | remaining + 1, h =>
      have hi : tk.size - 1 - remaining < tk.size := by omega
      tk[tk.size - 1 - remaining] ::
        sliceBytesLoop tk remaining (Nat.le_of_succ_le h)

def sliceBytes (tk : ByteSlice) : List UInt8 :=
  sliceBytesLoop tk tk.size (Nat.le_refl _)

theorem sliceBytesLoop_length
    (tk : ByteSlice) (remaining : Nat) (h : remaining ≤ tk.size) :
    (sliceBytesLoop tk remaining h).length = remaining := by
  induction remaining with
  | zero => rfl
  | succ remaining ih =>
      simp [sliceBytesLoop, ih]

theorem sliceBytes_length (tk : ByteSlice) :
    (sliceBytes tk).length = tk.size := by
  exact sliceBytesLoop_length tk tk.size (Nat.le_refl _)

/-- The complete implementation iterator preserves and reflects the source
decoder while maintaining the implementation's reverse-action accumulator. -/
theorem decodeLoop_mmLean4_agrees
    (tk : ByteSlice) (remaining : Nat) (h : remaining ≤ tk.size)
    (reversedPrefix : List ParserState.CompressedAction)
    (accumulator : Nat) :
    ParserState.decodeCompressedLoop tk remaining h
        reversedPrefix accumulator =
      toMMLean4StepResult reversedPrefix
        (decodeWord (sliceBytesLoop tk remaining h) accumulator) := by
  induction remaining generalizing reversedPrefix accumulator with
  | zero =>
      simp [ParserState.decodeCompressedLoop, sliceBytesLoop,
        decodeWord, toMMLean4StepResult]
  | succ remaining ih =>
      simp only [ParserState.decodeCompressedLoop, sliceBytesLoop,
        decodeWord]
      let byte := tk[tk.size - 1 - remaining]
      rw [decodeByte_mmLean4_agrees]
      cases decodeByte accumulator byte with
      | none =>
          simp [toMMLean4StepResult]
      | some result =>
          rcases result with ⟨headActions, nextAccumulator⟩
          simp [toMMLean4StepResult]
          rw [ih]
          cases decodeWord
              (sliceBytesLoop tk remaining (Nat.le_of_succ_le h))
              nextAccumulator with
          | none =>
              simp [toMMLean4StepResult]
          | some tailResult =>
              rcases tailResult with
                ⟨tailActions, finalAccumulator⟩
              simp [toMMLean4StepResult, List.reverse_append,
                List.map_append, List.append_assoc]

/-- Whole-token preservation and reflection: mm-lean4's shipped decoder and
the independent source decoder return exactly corresponding actions,
accumulator, and failure verdict for every byte slice. -/
theorem decodeCompressed_mmLean4_agrees
    (tk : ByteSlice) (accumulator : Nat) :
    ParserState.decodeCompressed tk accumulator =
      toMMLean4DecodeResult
        (decodeWord (sliceBytes tk) accumulator) := by
  unfold ParserState.decodeCompressed sliceBytes
  rw [decodeLoop_mmLean4_agrees]
  cases decodeWord
      (sliceBytesLoop tk tk.size (Nat.le_refl tk.size))
      accumulator with
  | none =>
      simp [toMMLean4StepResult, toMMLean4DecodeResult]
  | some result =>
      rcases result with ⟨actions, finalAccumulator⟩
      simp [toMMLean4StepResult, toMMLean4DecodeResult,
        List.map_reverse]

/-- Decode a complete sequence of compressed proof tokens while threading the
numeric prefix accumulator between token boundaries. -/
def decodeCompressedTokens :
    List ByteSlice → Nat →
      Except ProofCheckFail
        (List ParserState.CompressedAction × Nat)
  | [], accumulator => .ok ([], accumulator)
  | token :: tokens, accumulator => do
      let (headActions, nextAccumulator) ←
        ParserState.decodeCompressed token accumulator
      let (tailActions, finalAccumulator) ←
        decodeCompressedTokens tokens nextAccumulator
      pure (headActions ++ tailActions, finalAccumulator)

/-- Universal multi-token preservation and reflection. The implementation
threads exactly the same prefix accumulator and emits exactly the image of
the source action sequence, including identical failure behavior. -/
theorem decodeCompressedTokens_mmLean4_agrees
    (tokens : List ByteSlice) (accumulator : Nat) :
    decodeCompressedTokens tokens accumulator =
      toMMLean4DecodeResult
        (decodeWords (tokens.map sliceBytes) accumulator) := by
  induction tokens generalizing accumulator with
  | nil =>
      simp [decodeCompressedTokens, decodeWords,
        toMMLean4DecodeResult]
  | cons token tokens ih =>
      simp only [decodeCompressedTokens, List.map_cons, decodeWords]
      rw [decodeCompressed_mmLean4_agrees]
      cases decodeWord (sliceBytes token) accumulator with
      | none =>
          simp [toMMLean4DecodeResult, bind, Except.bind]
      | some headResult =>
          rcases headResult with ⟨headActions, nextAccumulator⟩
          simp only [toMMLean4DecodeResult, bind, Except.bind,
            pure, Except.pure]
          rw [ih]
          cases tailDecoded :
              decodeWords (List.map sliceBytes tokens)
                nextAccumulator with
          | none =>
              simp [tailDecoded, toMMLean4DecodeResult]
          | some tailResult =>
              rcases tailResult with
                ⟨tailActions, finalAccumulator⟩
              simp [tailDecoded, toMMLean4DecodeResult,
                List.map_append]

def toMMLean4ProgramResult
    (result : Option (List CompressedAction)) :
    Except ProofCheckFail (List ParserState.CompressedAction) :=
  match result with
  | some actions => .ok (actions.map toMMLean4Action)
  | none => .error (.proofCheck .proofParseError)

/-- The implementation-facing complete-program boundary. A numeric prefix
may cross lexical token boundaries, but it may not remain unfinished at the
end of the compressed proof. -/
def decodeCompressedProgram (tokens : List ByteSlice) :
    Except ProofCheckFail (List ParserState.CompressedAction) :=
  match decodeCompressedTokens tokens 0 with
  | .error error => .error error
  | .ok (actions, accumulator) =>
      if accumulator = 0 then
        .ok actions
      else
        .error (.proofCheck .proofParseError)

/-- Complete-program preservation and reflection, including rejection of an
unfinished numeric prefix at end of input. -/
theorem decodeCompressedProgram_mmLean4_agrees
    (tokens : List ByteSlice) :
    decodeCompressedProgram tokens =
      toMMLean4ProgramResult
        (decodeProgram (tokens.map sliceBytes)) := by
  rw [decodeCompressedProgram, decodeCompressedTokens_mmLean4_agrees]
  unfold decodeProgram
  cases decoded : decodeWords (List.map sliceBytes tokens) 0 with
  | none =>
      simp [toMMLean4DecodeResult, toMMLean4ProgramResult]
  | some result =>
      rcases result with ⟨actions, accumulator⟩
      by_cases finished : accumulator = 0
      · simp [finished, toMMLean4DecodeResult,
          toMMLean4ProgramResult]
      · simp [finished, toMMLean4DecodeResult,
          toMMLean4ProgramResult]

/-- Positive cross-implementation witness covering a base-five prefix,
termination, save, and a later proof index. -/
theorem decodeCompressed_ordering_witness
    (tk : ByteSlice)
    (hbytes : sliceBytes tk = [85, 65, 90, 66]) :
    ParserState.decodeCompressed tk 0 =
      .ok
        ([ParserState.CompressedAction.step 20,
          ParserState.CompressedAction.save,
          ParserState.CompressedAction.step 1], 0) := by
  rw [decodeCompressed_mmLean4_agrees, hbytes]
  rfl

/-- Negative cross-implementation witness: a non-code byte is rejected at
the same boundary by the source decoder and mm-lean4. -/
theorem decodeCompressed_invalid_witness
    (tk : ByteSlice) (hbytes : sliceBytes tk = [97]) :
    ParserState.decodeCompressed tk 0 =
      .error (.proofCheck .proofParseError) := by
  rw [decodeCompressed_mmLean4_agrees, hbytes]
  rfl

/-- Negative reflection witness: an implementation action sequence cannot be
the image of two distinct source action sequences. -/
theorem actionMap_injective :
    Function.Injective (List.map toMMLean4Action) := by
  intro left
  induction left with
  | nil =>
      intro right equal
      cases right with
      | nil => rfl
      | cons head tail => simp at equal
  | cons head tail ih =>
      intro right equal
      cases right with
      | nil => simp at equal
      | cons other rest =>
          simp only [List.map_cons, List.cons.injEq] at equal
          exact congrArg₂ List.cons
            (toMMLean4Action_injective equal.1)
            (ih equal.2)

end Mettapedia.Languages.Metamath.SourceGSLTCompressedMMLean4
