import Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
import Mettapedia.Languages.Metamath.ByteSliceForInSupport
import Metamath.Verify
import Metamath.PrefixTraceCompressed

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

def toMMLean4MProdStepResult
    (reversedPrefix : List ParserState.CompressedAction)
    (result : Option (List CompressedAction × Nat)) :
    Except ProofCheckFail
      (MProd (List ParserState.CompressedAction) Nat) :=
  match result with
  | some (actions, accumulator) =>
      .ok ⟨actions.reverse.map toMMLean4Action ++ reversedPrefix,
        accumulator⟩
  | none => .error (.proofCheck .proofParseError)

/-- One desugared iteration of the shipped decoder. Keeping this step
separate exposes the exact fold computed by the implementation without
making it a second decoding authority. -/
def decodeCompressedStep
    (policy : CompressedInvalidBytePolicy)
    (state : MProd (List ParserState.CompressedAction) Nat)
    (byte : UInt8) :
    Except ProofCheckFail
      (MProd (List ParserState.CompressedAction) Nat) := do
  let acts := state.fst
  let accumulator := state.snd
  if 'A'.toUInt8 ≤ byte && byte ≤ 'Z'.toUInt8 then
    if byte ≤ 'T'.toUInt8 then
      let index :=
        20 * accumulator + (byte - 'A'.toUInt8).toNat
      pure ⟨ParserState.CompressedAction.step index :: acts, 0⟩
    else if byte < 'Z'.toUInt8 then
      pure ⟨acts,
        5 * accumulator + (byte - 'T'.toUInt8).toNat⟩
    else
      pure ⟨ParserState.CompressedAction.save :: acts, 0⟩
  else if byte = '?'.toUInt8 then
    pure ⟨ParserState.CompressedAction.unknown :: acts, 0⟩
  else
    match policy with
    | .reject => throw (.proofCheck .proofParseError)
    | .ignore => pure ⟨acts, accumulator⟩

/-- The exact `ForInStep` body produced by desugaring the mutable loop in
`ParserState.decodeCompressed`. -/
def decodeCompressedForInStep
    (policy : CompressedInvalidBytePolicy) (byte : UInt8)
    (state : MProd (List ParserState.CompressedAction) Nat) :
    Except ProofCheckFail
      (ForInStep (MProd (List ParserState.CompressedAction) Nat)) :=
  let acts := state.fst
  let accumulator := state.snd
  if (decide ('A'.toUInt8 ≤ byte) &&
      decide (byte ≤ 'Z'.toUInt8)) = true then
    if byte ≤ 'T'.toUInt8 then
      let index :=
        20 * accumulator + (byte - 'A'.toUInt8).toNat
      let acts := ParserState.CompressedAction.step index :: acts
      let accumulator := 0
      do
        pure PUnit.unit
        pure (ForInStep.yield ⟨acts, accumulator⟩)
    else if byte < 'Z'.toUInt8 then
      let accumulator :=
        5 * accumulator + (byte - 'T'.toUInt8).toNat
      do
        pure PUnit.unit
        pure (ForInStep.yield ⟨acts, accumulator⟩)
    else
      let acts := ParserState.CompressedAction.save :: acts
      let accumulator := 0
      do
        pure PUnit.unit
        pure (ForInStep.yield ⟨acts, accumulator⟩)
  else if byte = '?'.toUInt8 then
    let acts := ParserState.CompressedAction.unknown :: acts
    let accumulator := 0
    do
      pure PUnit.unit
      pure (ForInStep.yield ⟨acts, accumulator⟩)
  else
    match policy with
    | .reject => do
        throw (.proofCheck .proofParseError)
        pure (ForInStep.yield ⟨acts, accumulator⟩)
    | .ignore => do
        pure ()
        pure (ForInStep.yield ⟨acts, accumulator⟩)

open Mettapedia.Languages.Metamath.ByteSliceForInSupport

/-- The shipped imperative decoder is exactly an exception-aware fold of
its desugared byte step. -/
theorem decodeCompressed_eq_fold
    (tk : ByteSlice) (accumulator : Nat)
    (policy : CompressedInvalidBytePolicy) :
    ParserState.decodeCompressed tk accumulator policy = (do
      let result ← (sliceList tk).foldlM
        (decodeCompressedStep policy) ⟨[], accumulator⟩
      pure (result.fst.reverse, result.snd)) := by
  unfold ParserState.decodeCompressed
  change (do
    let result ← ByteSlice.forIn tk
      (⟨[], accumulator⟩ :
        MProd (List ParserState.CompressedAction) Nat)
      (decodeCompressedForInStep policy)
    pure (result.fst.reverse, result.snd)) = _
  rw [byteSlice_forIn_except_yield tk _
    (decodeCompressedStep policy)]
  intro byte state
  rcases state with ⟨acts, current⟩
  unfold decodeCompressedForInStep decodeCompressedStep
  split <;> rename_i hAZ
  · split <;> rename_i hAT
    · rfl
    · split <;> rfl
  · split <;> rename_i hQ
    · rfl
    · cases policy <;> rfl

theorem subA_toNat (byte : UInt8) (h : 65 ≤ byte.toNat) :
    (byte - 'A'.toUInt8).toNat = byte.toNat - 65 := by
  have hA : 'A'.toUInt8.toNat = 65 := by decide
  rw [UInt8.toNat_sub, hA]
  have hbound := UInt8.toNat_lt byte
  norm_num at hbound ⊢
  omega

theorem subT_toNat (byte : UInt8) (h : 84 ≤ byte.toNat) :
    (byte - 'T'.toUInt8).toNat = byte.toNat - 84 := by
  have hT : 'T'.toUInt8.toNat = 84 := by decide
  rw [UInt8.toNat_sub, hT]
  have hbound := UInt8.toNat_lt byte
  norm_num at hbound ⊢
  omega

/-- Universal local preservation and reflection theorem for every byte and
every incoming reverse-action prefix and numeric accumulator. -/
theorem decodeByte_mmLean4_agrees
    (reversedPrefix : List ParserState.CompressedAction)
    (accumulator : Nat) (byte : UInt8) :
    decodeCompressedStep .reject
        ⟨reversedPrefix, accumulator⟩ byte =
      toMMLean4MProdStepResult reversedPrefix
        (decodeByte accumulator byte) := by
  have hA : 'A'.toUInt8.toNat = 65 := by decide
  have hT : 'T'.toUInt8.toNat = 84 := by decide
  have hZ : 'Z'.toUInt8.toNat = 90 := by decide
  have hQ : '?'.toUInt8.toNat = 63 := by decide
  by_cases hAT : 65 ≤ byte.toNat ∧ byte.toNat ≤ 84
  · have hAZ : 'A'.toUInt8 ≤ byte ∧ byte ≤ 'Z'.toUInt8 := by
      constructor
      · exact UInt8.le_iff_toNat_le.mpr (by simpa [hA] using hAT.1)
      · exact UInt8.le_iff_toNat_le.mpr (by simpa [hZ] using
          (show byte.toNat ≤ 90 by omega))
    have hIT : byte ≤ 'T'.toUInt8 :=
      UInt8.le_iff_toNat_le.mpr (by simpa [hT] using hAT.2)
    simp [decodeCompressedStep, toMMLean4MProdStepResult, decodeByte,
      hAT, hAZ.1, hAZ.2, hIT, toMMLean4Action,
      subA_toNat byte hAT.1, pure, Except.pure]
  · by_cases hUY : 85 ≤ byte.toNat ∧ byte.toNat ≤ 89
    · have hAZ : 'A'.toUInt8 ≤ byte ∧ byte ≤ 'Z'.toUInt8 := by
        constructor
        · exact UInt8.le_iff_toNat_le.mpr (by simpa [hA] using
            (show 65 ≤ byte.toNat by omega))
        · exact UInt8.le_iff_toNat_le.mpr (by simpa [hZ] using
            (show byte.toNat ≤ 90 by omega))
      have hnT : ¬ byte ≤ 'T'.toUInt8 := by
        simpa only [UInt8.le_iff_toNat_le, hT] using
          (show ¬ byte.toNat ≤ 84 by omega)
      have hIZ : byte < 'Z'.toUInt8 := by
        simpa only [UInt8.lt_iff_toNat_lt, hZ] using
          (show byte.toNat < 90 by omega)
      simp [decodeCompressedStep, toMMLean4MProdStepResult, decodeByte,
        hAT, hUY, hAZ.1, hAZ.2, hnT, hIZ,
        subT_toNat byte (by omega), pure, Except.pure]
    · by_cases hCodeZ : byte.toNat = 90
      · have hAZ : 'A'.toUInt8 ≤ byte ∧ byte ≤ 'Z'.toUInt8 := by
          constructor <;>
            simp only [UInt8.le_iff_toNat_le, hA, hZ, hCodeZ] <;>
            omega
        have hnT : ¬ byte ≤ 'T'.toUInt8 := by
          simpa only [UInt8.le_iff_toNat_le, hT, hCodeZ] using
            (show ¬ 90 ≤ 84 by omega)
        have hnZ : ¬ byte < 'Z'.toUInt8 := by
          simpa only [UInt8.lt_iff_toNat_lt, hZ, hCodeZ] using
            (show ¬ 90 < 90 by omega)
        simp [decodeCompressedStep, toMMLean4MProdStepResult, decodeByte,
          hCodeZ, hAZ.1, hAZ.2, hnT, hnZ, toMMLean4Action,
          pure, Except.pure]
      · by_cases hUnknown : byte.toNat = 63
        · have hnAZ : ¬ ('A'.toUInt8 ≤ byte) := by
            simpa only [UInt8.le_iff_toNat_le, hA, hUnknown] using
              (show ¬ 65 ≤ 63 by omega)
          have hByteQ : byte = '?'.toUInt8 := by
            exact UInt8.toNat_inj.mp (by simpa [hQ] using hUnknown)
          unfold decodeCompressedStep
          split
          · rename_i hAZ
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hAZ
            exact (hnAZ hAZ.1).elim
          · simp [toMMLean4MProdStepResult, decodeByte, hUnknown,
              toMMLean4Action, pure, Except.pure]
        · have hNotQ : byte ≠ '?'.toUInt8 := by
            intro h
            apply hUnknown
            rw [h, hQ]
          by_cases hAZ :
              'A'.toUInt8 ≤ byte ∧ byte ≤ 'Z'.toUInt8
          · have hNatAZ :
                65 ≤ byte.toNat ∧ byte.toNat ≤ 90 := by
              constructor
              · simpa only [UInt8.le_iff_toNat_le, hA] using hAZ.1
              · simpa only [UInt8.le_iff_toNat_le, hZ] using hAZ.2
            omega
          · unfold decodeCompressedStep
            split
            · rename_i hImplAZ
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hImplAZ
              exact (hAZ hImplAZ).elim
            · simp [toMMLean4MProdStepResult, decodeByte, hAT, hUY,
                hCodeZ, hUnknown]
              rfl

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

/-- The loop traversal is the corresponding drop/take of the underlying
byte array. -/
theorem sliceBytesLoop_eq_drop_take (tk : ByteSlice) :
    ∀ (remaining : Nat) (h : remaining ≤ tk.size),
      sliceBytesLoop tk remaining h =
        (tk.byteArray.data.toList.drop
          (tk.start + (tk.size - remaining))).take remaining
  | 0, _ => by
      rw [List.take_zero]
      rfl
  | remaining + 1, h => by
      have hstop := tk.stop_le_size_byteArray
      have hsize : tk.size = tk.stop - tk.start := rfl
      have hlen : tk.byteArray.data.toList.length = tk.byteArray.size := rfl
      have hbound : tk.start + (tk.size - 1 - remaining) <
          tk.byteArray.data.toList.length := by
        omega
      have h1 : tk.start + (tk.size - (remaining + 1)) =
          tk.start + (tk.size - 1 - remaining) := by omega
      have h2 : tk.start + (tk.size - remaining) =
          (tk.start + (tk.size - 1 - remaining)) + 1 := by omega
      simp only [sliceBytesLoop]
      rw [sliceBytesLoop_eq_drop_take tk remaining
        (Nat.le_of_succ_le h)]
      rw [h1, h2, List.drop_eq_getElem_cons hbound,
        List.take_succ_cons]
      congr 1

theorem sliceBytes_eq_sliceList (tk : ByteSlice) :
    sliceBytes tk = sliceList tk := by
  unfold sliceBytes
  rw [sliceBytesLoop_eq_drop_take, sliceList_def, Nat.sub_self,
    Nat.add_zero]

/-- The implementation fold preserves and reflects the source decoder while
maintaining the implementation's reverse-action accumulator. -/
theorem decodeFold_mmLean4_agrees
    (bytes : List UInt8)
    (reversedPrefix : List ParserState.CompressedAction)
    (accumulator : Nat) :
    bytes.foldlM (decodeCompressedStep .reject)
        ⟨reversedPrefix, accumulator⟩ =
      toMMLean4MProdStepResult reversedPrefix
        (decodeWord bytes accumulator) := by
  induction bytes generalizing reversedPrefix accumulator with
  | nil =>
      simp [decodeWord, toMMLean4MProdStepResult, pure, Except.pure]
  | cons byte bytes ih =>
      simp only [List.foldlM_cons, decodeWord]
      rw [decodeByte_mmLean4_agrees]
      cases headDecoded : decodeByte accumulator byte with
      | none =>
          simp [toMMLean4MProdStepResult, bind, Except.bind]
      | some headResult =>
          rcases headResult with ⟨headActions, nextAccumulator⟩
          simp only [toMMLean4MProdStepResult, bind, Except.bind, pure]
          rw [ih]
          cases tailDecoded : decodeWord bytes nextAccumulator with
          | none =>
              simp [tailDecoded, toMMLean4MProdStepResult]
          | some tailResult =>
              rcases tailResult with
                ⟨tailActions, finalAccumulator⟩
              simp [tailDecoded, toMMLean4MProdStepResult,
                List.reverse_append,
                List.map_append, List.append_assoc]

/-- Whole-token preservation and reflection: mm-lean4's shipped decoder and
the independent source decoder return exactly corresponding actions,
accumulator, and failure verdict for every byte slice. -/
theorem decodeCompressed_mmLean4_agrees
    (tk : ByteSlice) (accumulator : Nat) :
    ParserState.decodeCompressed tk accumulator =
      toMMLean4DecodeResult
        (decodeWord (sliceBytes tk) accumulator) := by
  rw [sliceBytes_eq_sliceList]
  rw [decodeCompressed_eq_fold]
  rw [decodeFold_mmLean4_agrees]
  cases decoded : decodeWord (sliceList tk) accumulator with
  | none =>
      simp [toMMLean4MProdStepResult, toMMLean4DecodeResult]
  | some result =>
      rcases result with ⟨actions, finalAccumulator⟩
      simp [toMMLean4MProdStepResult, toMMLean4DecodeResult,
        List.map_reverse]

/-- Once the rejecting decoder accepts one byte, the invalid-byte policy is
irrelevant for that step. -/
theorem decodeCompressedStep_policy_of_reject_ok
    (policy : CompressedInvalidBytePolicy)
    (initial next : MProd (List ParserState.CompressedAction) Nat)
    (byte : UInt8)
    (accepted : decodeCompressedStep .reject initial byte = .ok next) :
    decodeCompressedStep policy initial byte = .ok next := by
  cases policy with
  | reject => exact accepted
  | ignore =>
      rcases initial with ⟨acts, accumulator⟩
      unfold decodeCompressedStep at accepted ⊢
      by_cases hAZ :
          (decide ('A'.toUInt8 ≤ byte) &&
            decide (byte ≤ 'Z'.toUInt8)) = true
      · by_cases hAT : byte ≤ 'T'.toUInt8
        · simpa [hAZ, hAT] using accepted
        · by_cases hZ : byte < 'Z'.toUInt8
          · simpa [hAZ, hAT, hZ] using accepted
          · simpa [hAZ, hAT, hZ] using accepted
      · by_cases hQ : byte = '?'.toUInt8
        · simpa [hAZ, hQ] using accepted
        · simp [hAZ, hQ] at accepted

/-- A successful rejecting fold contains no invalid byte, so every configured
policy computes the same successful fold. -/
theorem decodeFold_policy_of_reject_ok
    (policy : CompressedInvalidBytePolicy) (bytes : List UInt8)
    (initial next : MProd (List ParserState.CompressedAction) Nat)
    (accepted : bytes.foldlM (decodeCompressedStep .reject) initial =
      .ok next) :
    bytes.foldlM (decodeCompressedStep policy) initial = .ok next := by
  induction bytes generalizing initial with
  | nil => simpa using accepted
  | cons byte bytes ih =>
      simp only [List.foldlM_cons] at accepted ⊢
      cases headAccepted : decodeCompressedStep .reject initial byte with
      | error error =>
          rw [headAccepted] at accepted
          simp only [bind, Except.bind] at accepted
          cases accepted
      | ok middle =>
          rw [headAccepted] at accepted
          simp only [bind, Except.bind] at accepted
          rw [decodeCompressedStep_policy_of_reject_ok policy initial
            middle byte headAccepted]
          exact ih middle accepted

/-- If the spec-faithful decoder accepts a token, every invalid-byte policy
returns that same result; the policy only affects otherwise-invalid bytes. -/
theorem decodeCompressed_policy_of_reject_ok
    (tk : ByteSlice) (accumulator : Nat)
    (policy : CompressedInvalidBytePolicy)
    (result : List ParserState.CompressedAction × Nat)
    (accepted : ParserState.decodeCompressed tk accumulator = .ok result) :
    ParserState.decodeCompressed tk accumulator policy = .ok result := by
  rw [decodeCompressed_eq_fold] at accepted ⊢
  cases foldAccepted : (sliceList tk).foldlM
      (decodeCompressedStep .reject)
      (⟨[], accumulator⟩ :
        MProd (List ParserState.CompressedAction) Nat) with
  | error error => simp [foldAccepted] at accepted
  | ok final =>
      have foldPolicy := decodeFold_policy_of_reject_ok policy
        (sliceList tk) ⟨[], accumulator⟩ final foldAccepted
      rw [foldPolicy]
      simpa [foldAccepted] using accepted

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

/-- A concrete implementation token sequence representing an authored source
program decodes to exactly the mapped source actions, including the final
zero-accumulator check. -/
theorem decodeCompressedProgram_eq_ok_of_sliceBytes
    (tokens : List ByteSlice) (words : List (List UInt8))
    (actions : List CompressedAction)
    (bytes : tokens.map sliceBytes = words)
    (decoded : decodeProgram words = some actions) :
    decodeCompressedProgram tokens =
      .ok (actions.map toMMLean4Action) := by
  rw [decodeCompressedProgram_mmLean4_agrees, bytes, decoded]
  rfl

/-- Execute the implementation's inner compressed-token transition over an
ordered token list.  This is the exact `feedProof.go` operation used by the
parser, before its error-location wrapper. -/
def runCompressedTokenGo
    (parser : ParserState) (tokens : List ByteSlice)
    (initial : ProofState) : Except ProofCheckFail ProofState :=
  tokens.foldlM
    (fun current token => ParserState.feedProof.go parser token current)
    initial

/-- Successful complete-program decoding exposes both the ordered actions and
the required zero final accumulator. -/
theorem decodeCompressedTokens_eq_of_program_ok
    (tokens : List ByteSlice)
    (actions : List ParserState.CompressedAction)
    (decoded : decodeCompressedProgram tokens = .ok actions) :
    decodeCompressedTokens tokens 0 = .ok (actions, 0) := by
  unfold decodeCompressedProgram at decoded
  cases tokensDecoded : decodeCompressedTokens tokens 0 with
  | error error => simp [tokensDecoded] at decoded
  | ok result =>
      rcases result with ⟨decodedActions, accumulator⟩
      by_cases finished : accumulator = 0
      · subst accumulator
        simp only [tokensDecoded, ↓reduceIte, Except.ok.injEq] at decoded
        subst decodedActions
        rfl
      · simp [tokensDecoded, finished] at decoded

/-- Decoding and applying an entire token sequence at once is exactly the
same transition as the implementation's token-by-token compressed phase,
including the numeric accumulator threaded across token boundaries. -/
theorem runCompressedTokenGo_eq_of_decoded
    (parser : ParserState) (tokens : List ByteSlice)
    (accumulator finalAccumulator : Nat)
    (initial result : ProofState)
    (actions : List ParserState.CompressedAction)
    (decoded :
      decodeCompressedTokens tokens accumulator =
        .ok (actions, finalAccumulator))
    (applied :
      ParserState.applyCompressedActions parser.db initial actions =
        .ok result) :
    runCompressedTokenGo parser tokens
        { initial with ptp := .compressed accumulator } =
      .ok { result with ptp := .compressed finalAccumulator } := by
  induction tokens generalizing accumulator initial actions
      finalAccumulator result with
  | nil =>
      simp [decodeCompressedTokens] at decoded
      rcases decoded with ⟨rfl, rfl⟩
      simp [runCompressedTokenGo,
        ParserState.applyCompressedActions] at applied ⊢
      cases applied
      rfl
  | cons token tokens ih =>
      simp only [decodeCompressedTokens, bind, Except.bind] at decoded
      cases headDecoded : ParserState.decodeCompressed token accumulator with
      | error error => simp [headDecoded] at decoded
      | ok headResult =>
          rcases headResult with ⟨headActions, nextAccumulator⟩
          simp only [headDecoded] at decoded
          cases tailDecoded :
              decodeCompressedTokens tokens nextAccumulator with
          | error error => simp [tailDecoded] at decoded
          | ok tailResult =>
              rcases tailResult with ⟨tailActions, tailAccumulator⟩
              simp only [tailDecoded, pure, Except.pure,
                Except.ok.injEq, Prod.mk.injEq] at decoded
              rcases decoded with ⟨rfl, rfl⟩
              have appendExecution :
                  ParserState.applyCompressedActions parser.db initial
                      (headActions ++ tailActions) =
                    (do
                      let middle ←
                        ParserState.applyCompressedActions parser.db initial
                          headActions
                      ParserState.applyCompressedActions parser.db middle
                        tailActions) := by
                unfold ParserState.applyCompressedActions
                exact List.foldlM_append
              rw [appendExecution] at applied
              cases headApplied :
                  ParserState.applyCompressedActions parser.db initial
                    headActions with
              | error error =>
                  rw [headApplied] at applied
                  simp only [bind, Except.bind] at applied
                  cases applied
              | ok middle =>
                  have headExecution :
                      ParserState.applyCompressedActions parser.db initial
                          headActions = .ok middle := by
                    exact headApplied
                  have tailExecution :
                      ParserState.applyCompressedActions parser.db middle
                          tailActions = .ok result := by
                    rw [headApplied] at applied
                    simpa only [bind, Except.bind] using applied
                  have phaseHeadExecution :
                      ParserState.applyCompressedActions parser.db
                          { initial with
                            ptp := .compressed accumulator }
                          headActions =
                        .ok { middle with
                          ptp := .compressed accumulator } :=
                    Metamath.PrefixTraceCompressed.applyCA_ptp_ok
                      parser.db initial headActions
                        (.compressed accumulator) middle headExecution
                  have firstToken :
                      ParserState.feedProof.go parser token
                          { initial with
                          ptp := .compressed accumulator } =
                        .ok { middle with
                          ptp := .compressed nextAccumulator } := by
                    have headDecodedConfigured :
                        ParserState.decodeCompressed token accumulator
                            parser.db.config.compressedInvalidBytes =
                          .ok (headActions, nextAccumulator) :=
                      decodeCompressed_policy_of_reject_ok token accumulator
                        parser.db.config.compressedInvalidBytes
                        (headActions, nextAccumulator) headDecoded
                    unfold ParserState.feedProof.go
                    simp only [headDecodedConfigured, bind, Except.bind]
                    rw [phaseHeadExecution]
                    rfl
                  simp only [runCompressedTokenGo, List.foldlM_cons,
                    bind, Except.bind]
                  rw [firstToken]
                  exact ih nextAccumulator tailAccumulator middle result
                    tailActions tailDecoded tailExecution

/-- Complete-program specialization of token-by-token execution. -/
theorem runCompressedTokenGo_eq_of_program_ok
    (parser : ParserState) (tokens : List ByteSlice)
    (initial result : ProofState)
    (actions : List ParserState.CompressedAction)
    (decoded : decodeCompressedProgram tokens = .ok actions)
    (applied :
      ParserState.applyCompressedActions parser.db initial actions =
        .ok result) :
    runCompressedTokenGo parser tokens
        { initial with ptp := .compressed 0 } =
      .ok { result with ptp := .compressed 0 } := by
  exact runCompressedTokenGo_eq_of_decoded parser tokens 0 0
    initial result actions
      (decodeCompressedTokens_eq_of_program_ok tokens actions decoded)
      applied

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
