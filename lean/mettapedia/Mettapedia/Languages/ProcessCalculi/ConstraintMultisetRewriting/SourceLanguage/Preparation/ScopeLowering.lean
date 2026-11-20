import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.BindingTemplates
import Mettapedia.Machines.TIsa.P1WordScalar

/-!
# Lowering a fresh scope to p1 words

The logical opening adds a relative position to the entry scope. Its
word code consists of an addition and an unsigned comparison. The
comparison recognizes precisely the non-wrapping case. Register choices
are parameters, and an entire admitted interval can use one width check.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.ScopeLowering

open Mettapedia.Machines.TIsa P1Source
open P1WordExecution (Registers)
open BindingTemplates (Refusal)

theorem carry_test {width : Nat} (base offset : BitVec width) :
    Comparison.lessEqualUnsigned.evaluate base (base + offset) = true ↔
      base.toNat + offset.toNat < 2 ^ width := by
  have baseFits := base.isLt
  have offsetFits := offset.isLt
  simp only [Comparison.evaluate, decide_eq_true_eq, BitVec.le_def, BitVec.toNat_add]
  by_cases fits : base.toNat + offset.toNat < 2 ^ width
  · rw [Nat.mod_eq_of_lt fits]
    exact iff_of_true (by omega) fits
  · have wraps : (base.toNat + offset.toNat) % (2 ^ width) =
        base.toNat + offset.toNat - 2 ^ width := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [wraps]
    exact iff_of_false (by omega) fits

def code (base offset result flag : Reg) : Stmt :=
  .seq (.instruction (.binary .add .u64 result base offset))
    (.instruction (.compare .lessEqualUnsigned .u64 flag base (.register result)))

theorem code_exact (registers : Registers) (base offset result flag : Reg)
    (baseRetained : base ≠ result) :
    P1WordScalar.executeScalar registers (code base offset result flag) =
      some (.following (Function.update (Function.update registers result (registers base + registers offset))
        flag (booleanWord (decide ((registers base).toNat + (registers offset).toNat < 2 ^ 64))))) := by
  have checked :
      Comparison.lessEqualUnsigned.evaluate (registers base) (registers base + registers offset) =
        decide ((registers base).toNat + (registers offset).toNat < 2 ^ 64) :=
    Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using carry_test (registers base) (registers offset))
  simp [code, P1WordScalar.executeScalar, Instr.destination?, Instr.reads, P1Scalar.evaluate,
    P1Scalar.boolInputs, P1Scalar.compareWords, P1Scalar.narrow, P1Scalar.normalize,
    Binary.evaluate, Function.update_of_ne baseRetained, checked]

def read (registers : Registers) (result flag : Reg) : Except Refusal Nat :=
  if registers flag = 1 then .ok (registers result).toNat else .error .scopeOverflow

theorem read_after_code (registers : Registers) (base offset result flag : Reg)
    (baseRetained : base ≠ result) (resultRetained : result ≠ flag) :
    (P1WordScalar.executeScalar registers (code base offset result flag)).map
      (fun ending => match ending with
        | .following after => read after result flag
        | .returned .. => .error .unrepresentable) =
      some (if (registers base).toNat + (registers offset).toNat < 2 ^ 64 then
        .ok ((registers base).toNat + (registers offset).toNat) else .error .scopeOverflow) := by
  rw [code_exact _ _ _ _ _ baseRetained]
  by_cases fits : (registers base).toNat + (registers offset).toNat < 2 ^ 64
  · rw [if_pos fits]
    simp only [Option.map_some, read, Function.update_self, booleanWord, decide_eq_true fits, if_true,
      Function.update_of_ne resultRetained, BitVec.toNat_add, Nat.mod_eq_of_lt fits]
  · rw [if_neg fits]
    simp only [Option.map_some, read, Function.update_self, booleanWord, decide_eq_false fits]
    rfl

theorem code_preserves_unwritten (registers : Registers) (base offset result flag other : Reg)
    (baseRetained : base ≠ result) (otherResult : other ≠ result) (otherFlag : other ≠ flag)
    {after : Registers}
    (ran : P1WordScalar.executeScalar registers (code base offset result flag) = some (.following after)) :
    after other = registers other := by
  rw [code_exact _ _ _ _ _ baseRetained] at ran
  cases ran
  simp [Function.update_of_ne otherFlag, Function.update_of_ne otherResult]

theorem p1_block (state : P1WordExecution.State) (base offset result flag : Reg)
    (baseRetained : base ≠ result) :
    P1WordExecution.execute state (code base offset result flag) =
      .continuing { state with
        registers := Function.update
          (Function.update state.registers result (state.registers base + state.registers offset))
          flag (booleanWord (decide ((state.registers base).toNat + (state.registers offset).toNat < 2 ^ 64))) } :=
  P1WordScalar.execute_agrees _ state _ (code_exact state.registers base offset result flag baseRetained)

/-- A guard for the entire allocation interval licences every addition
inside it, including reuse after the first opening. -/
theorem interval_additions_exact (origin count position : Nat)
    (room : origin + count ≤ 2 ^ 64) (inside : position < count) :
    Comparison.lessEqualUnsigned.evaluate (BitVec.ofNat 64 origin)
        (BitVec.ofNat 64 origin + BitVec.ofNat 64 position) = true ∧
      (BitVec.ofNat 64 origin + BitVec.ofNat 64 position).toNat = origin + position := by
  have originFits : origin < 2 ^ 64 := by omega
  have positionFits : position < 2 ^ 64 := by omega
  have sumFits : origin + position < 2 ^ 64 := by omega
  have decodedOrigin : (BitVec.ofNat 64 origin).toNat = origin := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt originFits]
  have decodedPosition : (BitVec.ofNat 64 position).toNat = position := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt positionFits]
  constructor
  · apply (carry_test _ _).mpr
    rw [decodedOrigin, decodedPosition]
    exact sumFits
  · rw [BitVec.toNat_add, decodedOrigin, decodedPosition, Nat.mod_eq_of_lt sumFits]

namespace Controls

theorem unsigned_guard_allows_crossing_the_signed_boundary :
    Comparison.lessEqualUnsigned.evaluate (0x7fffffffffffffff#64) (0x7fffffffffffffff#64 + 1) = true ∧
      Comparison.lessEqualSigned.evaluate (0x7fffffffffffffff#64) (0x7fffffffffffffff#64 + 1) = false := by
  decide +kernel

theorem addition_at_the_last_word_can_wrap :
    Comparison.lessEqualUnsigned.evaluate (0xffffffffffffffff#64) (0xffffffffffffffff#64 + 1) = false := by
  decide +kernel

end Controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.ScopeLowering
