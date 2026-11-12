import Mettapedia.Machines.TIsa.ModelImport
import Mettapedia.Machines.TIsa.Widths

/-!
# Scalar agreement with pinned riscv-lean definitions

Upstream: opencompl/riscv-lean, revision
0e3365ac7b670d79d70e9b4a8b7fba782607c44f, RISCV/Instructions.lean.
The actual file is elaborated without copying or changing its definitions.
These scalar equations do not yet prove instruction decoding or the separate
upstream Sail correspondence. Those require their own checked imports.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Pinned

tisa_model_source% "../../../repos/riscv-lean/RISCV/Instructions.lean"
  sha256 "b2f0381335adcefa62acfdc10bb51d89de984e434aecb4759ef02b3bdc3c24e5"

-- The upstream file leaves its namespace open at end of file.
end RV64

end Mettapedia.Machines.TIsa.Pinned

namespace Mettapedia.Machines.TIsa.RV64Model

theorem add_agrees (left right : Word) : Binary.add.evaluate left right = Pinned.RV64.add right left := rfl
theorem sub_agrees (left right : Word) : Binary.sub.evaluate left right = Pinned.RV64.sub right left := rfl
theorem and_agrees (left right : Word) : Binary.band.evaluate left right = Pinned.RV64.and right left := rfl
theorem or_agrees (left right : Word) : Binary.bor.evaluate left right = Pinned.RV64.or right left := rfl
theorem xor_agrees (left right : Word) : Binary.bxor.evaluate left right = Pinned.RV64.xor right left := rfl
theorem mul_agrees (left right : Word) : Binary.mulLo.evaluate left right = Pinned.RV64.mul right left := by
  simp [Binary.evaluate, Pinned.RV64.mul, BitVec.mul_comm]

theorem shl_agrees (value : Word) (amount : BitVec 6) :
    Shift.left.evaluate value amount.toNat = Pinned.RV64.sll (amount.zeroExtend 64) value := by
  simp [Shift.evaluate, Pinned.RV64.sll, BitVec.shiftLeft_eq']
  rw [Nat.mod_eq_of_lt amount.isLt]

theorem shr_agrees (value : Word) (amount : BitVec 6) :
    Shift.rightUnsigned.evaluate value amount.toNat = Pinned.RV64.srl (amount.zeroExtend 64) value := by
  simp [Shift.evaluate, Pinned.RV64.srl, BitVec.ushiftRight_eq']
  rw [Nat.mod_eq_of_lt amount.isLt]

theorem sar_agrees (value : Word) (amount : BitVec 6) :
    Shift.rightSigned.evaluate value amount.toNat = Pinned.RV64.sra (amount.zeroExtend 64) value := by
  simp [Shift.evaluate, Pinned.RV64.sra, BitVec.sshiftRight']
  rw [Nat.mod_eq_of_lt amount.isLt]

theorem slt_agrees (left right : Word) :
    booleanWord (Comparison.lessSigned.evaluate left right) = Pinned.RV64.slt right left := by
  change booleanWord (left.slt right) = (BitVec.ofBool (left.slt right)).setWidth 64
  cases left.slt right <;> rfl

theorem sltu_agrees (left right : Word) :
    booleanWord (Comparison.lessUnsigned.evaluate left right) = Pinned.RV64.sltu right left := by
  change booleanWord (left.ult right) = (BitVec.ofBool (left.ult right)).setWidth 64
  cases left.ult right <;> rfl

theorem addw_agrees (left right : Word) :
    (Scalar.binary .add).evaluate32 true [left, right] = some (Pinned.RV64.addw right left) := rfl

theorem subw_agrees (left right : Word) :
    (Scalar.binary .sub).evaluate32 true [left, right] = some (Pinned.RV64.subw right left) := rfl

#print axioms add_agrees
#print axioms sub_agrees

end Mettapedia.Machines.TIsa.RV64Model
