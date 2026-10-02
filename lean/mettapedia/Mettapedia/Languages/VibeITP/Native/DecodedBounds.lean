import Mettapedia.Languages.VibeITP.Spec.InstructionBounds
import Mettapedia.Languages.VibeITP.Native.BinaryDecoder

/-! Actual decoder outputs satisfy the kernel's machine-word input domain. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Mettapedia.Languages.VibeITP.Native.DecodedBounds

open Spec

theorem word_establishes :
    Spec.Parser.word.Establishes (fun value => value < wordBound) := by
  intro bytes value rest accepted
  have native : Mettapedia.GSLT.Parsing.BinaryRecordCodec.word
      GeneratedBinarySource.grammar.codec bytes = .ok (value, rest) := by
    rw [BinaryDecoder.word_correct]
    simp [BinaryDecoder.lift, accepted]
  exact BinaryDecoder.word_value_bound native

theorem words_establishes (count : Nat) :
    (Spec.Parser.words count).Establishes
      (fun values => values.length = count ∧ ∀ value ∈ values, value < wordBound) := by
  induction count with
  | zero =>
    exact Spec.Parser.pure_establishes [] _ ⟨rfl, by simp⟩
  | succ count ih =>
    rw [Spec.Parser.words]
    refine Spec.Parser.bind_establishes _ _ _ _ word_establishes ?_
    intro value bound
    refine Spec.Parser.bind_establishes _ _ _ _ ih ?_
    intro values valid
    apply Spec.Parser.pure_establishes
    constructor
    · simp [valid.1]
    · intro word member
      rcases List.mem_cons.mp member with same | previous
      · subst word
        exact bound
      · exact valid.2 word previous

theorem counted_establishes : Spec.Parser.counted.Establishes
    (fun values => values.length < wordBound ∧ ∀ value ∈ values, value < wordBound) := by
  unfold Spec.Parser.counted
  refine Spec.Parser.bind_establishes _ _ _ _ word_establishes ?_
  intro count bound bytes values rest accepted
  have valid := words_establishes count bytes values rest accepted
  exact ⟨by simpa [valid.1] using bound, valid.2⟩

theorem operands_establishes (opcode : Nat) :
    (Spec.decodeOperands opcode).Establishes Instr.MachineBounded := by
  unfold Spec.decodeOperands
  split
  next =>
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value0 valid0
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value1 valid1
    apply Spec.Parser.pure_establishes
    simp_all [Instr.MachineBounded, Instr.machineWords]
  next =>
    refine Spec.Parser.bind_establishes _ _ (fun values => values.length < wordBound ∧ ∀ value ∈ values, value < wordBound) _ counted_establishes ?_
    intro value0 valid0
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value1 valid1
    apply Spec.Parser.pure_establishes
    simp_all [Instr.MachineBounded, Instr.machineWords]
  next =>
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value0 valid0
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value1 valid1
    apply Spec.Parser.pure_establishes
    simp_all [Instr.MachineBounded, Instr.machineWords]
  next =>
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value0 valid0
    apply Spec.Parser.pure_establishes
    simp_all [Instr.MachineBounded, Instr.machineWords]
  next =>
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value0 valid0
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value1 valid1
    apply Spec.Parser.pure_establishes
    simp_all [Instr.MachineBounded, Instr.machineWords]
  next =>
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value0 valid0
    refine Spec.Parser.bind_establishes _ _ (fun bytes => bytes.length = value0) _ (Spec.Parser.raw_establishes value0) ?_
    intro value1 valid1
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value2 valid2
    apply Spec.Parser.pure_establishes
    simp_all [Instr.MachineBounded, Instr.machineWords]
  next =>
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value0 valid0
    refine Spec.Parser.bind_establishes _ _ (fun values => values.length < wordBound ∧ ∀ value ∈ values, value < wordBound) _ counted_establishes ?_
    intro value1 valid1
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value2 valid2
    apply Spec.Parser.pure_establishes
    simp_all [Instr.MachineBounded, Instr.machineWords]
  next =>
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value0 valid0
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value1 valid1
    apply Spec.Parser.pure_establishes
    simp_all [Instr.MachineBounded, Instr.machineWords]
  next =>
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value0 valid0
    apply Spec.Parser.pure_establishes
    simp_all [Instr.MachineBounded, Instr.machineWords]
  next =>
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value0 valid0
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value1 valid1
    apply Spec.Parser.pure_establishes
    simp_all [Instr.MachineBounded, Instr.machineWords]
  next =>
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value0 valid0
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value1 valid1
    apply Spec.Parser.pure_establishes
    simp_all [Instr.MachineBounded, Instr.machineWords]
  next =>
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value0 valid0
    apply Spec.Parser.pure_establishes
    simp_all [Instr.MachineBounded, Instr.machineWords]
  next =>
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value0 valid0
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value1 valid1
    apply Spec.Parser.pure_establishes
    simp_all [Instr.MachineBounded, Instr.machineWords]
  next =>
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value0 valid0
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value1 valid1
    apply Spec.Parser.pure_establishes
    simp_all [Instr.MachineBounded, Instr.machineWords]
  next =>
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value0 valid0
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value1 valid1
    apply Spec.Parser.pure_establishes
    simp_all [Instr.MachineBounded, Instr.machineWords]
  next =>
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value0 valid0
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value1 valid1
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value2 valid2
    apply Spec.Parser.pure_establishes
    simp_all [Instr.MachineBounded, Instr.machineWords]
  next =>
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value0 valid0
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value1 valid1
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value2 valid2
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value3 valid3
    apply Spec.Parser.pure_establishes
    simp_all [Instr.MachineBounded, Instr.machineWords]
  next =>
    refine Spec.Parser.bind_establishes _ _ (fun values => values.length < wordBound ∧ ∀ value ∈ values, value < wordBound) _ counted_establishes ?_
    intro value0 valid0
    refine Spec.Parser.bind_establishes _ _ (fun values => values.length < wordBound ∧ ∀ value ∈ values, value < wordBound) _ counted_establishes ?_
    intro value1 valid1
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value2 valid2
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value3 valid3
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value4 valid4
    apply Spec.Parser.pure_establishes
    simp_all [Instr.MachineBounded, Instr.machineWords]
    all_goals aesop
  next =>
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value0 valid0
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value1 valid1
    apply Spec.Parser.pure_establishes
    simp_all [Instr.MachineBounded, Instr.machineWords]
  next =>
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value0 valid0
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value1 valid1
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value2 valid2
    apply Spec.Parser.pure_establishes
    simp_all [Instr.MachineBounded, Instr.machineWords]
  next =>
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value0 valid0
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value1 valid1
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value2 valid2
    apply Spec.Parser.pure_establishes
    simp_all [Instr.MachineBounded, Instr.machineWords]
  next =>
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value0 valid0
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value1 valid1
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value2 valid2
    apply Spec.Parser.pure_establishes
    simp_all [Instr.MachineBounded, Instr.machineWords]
  next =>
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value0 valid0
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value1 valid1
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value2 valid2
    apply Spec.Parser.pure_establishes
    simp_all [Instr.MachineBounded, Instr.machineWords]
  next =>
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value0 valid0
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value1 valid1
    apply Spec.Parser.pure_establishes
    simp_all [Instr.MachineBounded, Instr.machineWords]
  next =>
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value0 valid0
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value1 valid1
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value2 valid2
    apply Spec.Parser.pure_establishes
    simp_all [Instr.MachineBounded, Instr.machineWords]
  next =>
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value0 valid0
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value1 valid1
    refine Spec.Parser.bind_establishes _ _ (fun value => value < wordBound) _ word_establishes ?_
    intro value2 valid2
    apply Spec.Parser.pure_establishes
    simp_all [Instr.MachineBounded, Instr.machineWords]
  next =>
    intro bytes instruction rest accepted
    simp [Spec.Parser.fail] at accepted

theorem stream_establishes : ∀ fuel bytes instructions,
    Spec.decodeStream fuel bytes = .ok instructions →
      ∀ instruction ∈ instructions, instruction.MachineBounded := by
  intro fuel
  induction fuel with
  | zero =>
    intro bytes instructions accepted
    cases bytes <;> simp [Spec.decodeStream] at accepted
    all_goals subst instructions; simp
  | succ fuel ih =>
    intro bytes instructions accepted
    cases bytes with
    | nil =>
      simp [Spec.decodeStream] at accepted
      subst instructions
      simp
    | cons opcode bytes =>
      simp only [Spec.decodeStream] at accepted
      cases parsed : Spec.decodeOperands opcode.toNat bytes with
      | error error => simp [parsed] at accepted
      | ok pair =>
        rcases pair with ⟨instruction, rest⟩
        simp only [parsed] at accepted
        cases decoded : Spec.decodeStream fuel rest with
        | error error => simp [decoded] at accepted
        | ok following =>
          simp only [decoded, Except.ok.injEq] at accepted
          subst instructions
          intro result member
          rcases List.mem_cons.mp member with same | previous
          · subst result
            exact operands_establishes opcode.toNat bytes instruction rest parsed
          · exact ih rest following decoded result previous

theorem file_establishes (bytes : List UInt8) (instructions : List Instr)
    (accepted : Spec.decodeFile bytes = .ok instructions) :
    ∀ instruction ∈ instructions, instruction.MachineBounded :=
  stream_establishes bytes.length bytes instructions accepted

end Mettapedia.Languages.VibeITP.Native.DecodedBounds
