import Mettapedia.Machines.TIsa.X86PlacedArithmetic
import Mettapedia.Machines.TIsa.X86PlacedLogical
import Mettapedia.Machines.TIsa.X86PlacedRegisterMove
import Mettapedia.Machines.TIsa.X86PlacedLiteral
import Mettapedia.Machines.TIsa.PreparedWordGuards

/-! # Fetched signed addition and subtraction with an overflow edge -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

namespace Mettapedia.Machines.TIsa.X86PreparedSignedArithmetic

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (Code registerCode handlers)
open X86Arithmetic (DefinedOperation result)
local instance : MemoryPrimitives := X86Memory.ordinary

def overflows : DefinedOperation → Word → Word → Bool
  | .add => PreparedWordGuards.addOverflows
  | .sub => PreparedWordGuards.subOverflows

def signed : DefinedOperation → Int → Int → Int
  | .add => (· + ·)
  | .sub => (· - ·)

theorem overflow_exact (op : DefinedOperation) (left right : Word) :
    overflows op left right = true ↔ ¬ PreparedWordGuards.Fits (2^63) (signed op left.toInt right.toInt) := by
  cases op
  · exact PreparedWordGuards.add_overflow_exact left right
  · exact PreparedWordGuards.sub_overflow_exact left right

theorem result_exact (op : DefinedOperation) (left right : Word) (ok : overflows op left right = false) :
    (result op left right).toInt = signed op left.toInt right.toInt := by
  have inside : PreparedWordGuards.Fits (2^63) (signed op left.toInt right.toInt) := by
    by_contra outside
    have rejected := (overflow_exact op left right).mpr outside
    rw [ok] at rejected
    cases rejected
  cases op with
  | add =>
    change PreparedWordGuards.Fits (2^63) (left.toInt + right.toInt) at inside
    have exact := PreparedWordGuards.checked_add_exact left right
    simp only [PreparedWordGuards.checkedAdd, show PreparedWordGuards.addOverflows left right = false from ok,
      Bool.false_eq_true, if_false, Option.map_some, if_pos inside, Option.some.injEq] at exact
    exact exact
  | sub =>
    change PreparedWordGuards.Fits (2^63) (left.toInt - right.toInt) at inside
    have exact := PreparedWordGuards.checked_sub_exact left right
    simp only [PreparedWordGuards.checkedSub, show PreparedWordGuards.subOverflows left right = false from ok,
      Bool.false_eq_true, if_false, Option.map_some, if_pos inside, Option.some.injEq] at exact
    exact exact

private def leftMask (op : DefinedOperation) (left right : Word) : Word :=
  left ^^^ (match op with | .add => result op left right | .sub => right)

private def rightInput : DefinedOperation → Word → Word → Word
  | .add, _, right => right
  | .sub, left, _ => left

private def maskSteps : DefinedOperation → Nat
  | .add => 1
  | .sub => 2

structure Site where
  start : Nat
  operation : DefinedOperation
  success : Nat

def Site.rightXor (site : Site) : Nat := site.start + 9 + 3 * maskSteps site.operation
def Site.compareAt (site : Site) : Nat := site.rightXor + 6
def Site.declineAt (site : Site) : Nat := site.compareAt + 13
def Site.steps (site : Site) : Nat := 7 + maskSteps site.operation

private def MaskChecked (image : NativeImage.View) (start : Nat) : DefinedOperation → Prop
  | .add => Code image start (X86LogicalWord.code .xor 1 9)
  | .sub => Code image start (X86LogicalWord.code .xor 2 9) ∧ Code image (start + 3) (registerCode 0x89 6 2)

instance (image : NativeImage.View) (start : Nat) (op : DefinedOperation) :
    Decidable (MaskChecked image start op) := by cases op <;> unfold MaskChecked <;> infer_instance

def Checked (image : NativeImage.View) (site : Site) : Prop :=
  Code image site.start (registerCode 0x89 6 1) ∧
  Code image (site.start + 3) (registerCode (X86Arithmetic.opcode site.operation) 2 1) ∧
  Code image (site.start + 6) (registerCode 0x89 6 9) ∧
  MaskChecked image (site.start + 9) site.operation ∧
  Code image site.rightXor (X86LogicalWord.code .xor 1 2) ∧
  Code image (site.rightXor + 3) (X86LogicalWord.code .and 2 9) ∧
  X86PlacedLiteral.CompareBranch image site.compareAt site.success .lessSigned 9 (.nonnegative 0)

instance (image : NativeImage.View) (site : Site) : Decidable (Checked image site) :=
  inferInstanceAs (Decidable (_ ∧ _))

private abbrev maskWrites : Finset Register := {.rdx, .r9, .rflags, .rip}
abbrev writes : Finset Register := {.rcx, .rdx, .r9, .rflags, .rip}

private theorem stage_mask (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {native : State}
    {base : BitVec 48} {start : Nat} (point : At image native base start)
    (op : DefinedOperation) (checked : MaskChecked image start op)
    (extent : start + 3 * maskSteps op ≤ image.size) (left right : Word)
    (leftRead : lookup native 6 = some left) (copyRead : lookup native 9 = some left)
    (rightRead : lookup native 2 = some right) (sumRead : lookup native 1 = some (result op left right)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (maskSteps op)).run native = .ok () after ∧ RegisterFrame maskWrites native after ∧
      lookup after 9 = some (leftMask op left right) ∧ lookup after 2 = some (rightInput op left right) ∧
      Nonempty (At image after base (start + 3 * maskSteps op)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  cases op with
  | add =>
    obtain ⟨after, ran, frame, mask, next⟩ := X86PlacedLogical.executes (handlers other extra) vector point
      (by exact extent) .xor 1 9 left (result .add left right) sumRead copyRead checked
    exact ⟨after, ran, frame.mono (by decide), mask, (frame.lookup 2 (by decide)).trans rightRead, next⟩
  | sub =>
    obtain ⟨first, ran, frame, mask, ⟨atMove⟩⟩ := X86PlacedLogical.executes (handlers other extra) vector point
      (by change start + 6 ≤ image.size at extent; omega) .xor 2 9 left right rightRead copyRead checked.1
    obtain ⟨after, moved, moveFrame, second, next⟩ := X86PlacedRegisterMove.executes (handlers other extra) vector
      atMove extent 6 2 left ((frame.lookup 6 (by decide)).trans leftRead) checked.2
    exact ⟨after, @X86FuelPrefix.fetches_then (handlers other extra) vector 1 1 native first after ran moved,
      (frame.trans moveFrame).mono (by decide), (moveFrame.lookup 9 (by decide)).trans mask, second, next⟩

theorem branches (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {native : State} {base : BitVec 48} {site : Site}
    (point : At image native base site.start) (checked : Checked image site)
    (left right : Word) (leftRead : lookup native 6 = some left) (rightRead : lookup native 2 = some right) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches site.steps).run native = .ok () after ∧ RegisterFrame writes native after ∧
      lookup after 1 = some (result site.operation left right) ∧
      Nonempty (At image after base (if overflows site.operation left right then site.declineAt else site.success)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨copyCode, arithmetic, saveCode, maskCode, xorCode, andCode, branchCode⟩ := checked
  have extent := branchCode.1
  unfold Site.compareAt at extent
  have beforeMask : site.start + 9 ≤ image.size := by unfold Site.rightXor at extent; omega
  let wrapped := result site.operation left right
  obtain ⟨copied, copyRun, copyFrame, word, ⟨atOp⟩⟩ := X86PlacedRegisterMove.executes (handlers other extra)
    vector point (by omega) 6 1 left leftRead copyCode
  obtain ⟨added, arithmeticRun, arithmeticFrame, sum, ⟨atSave⟩⟩ := X86PlacedArithmetic.executes (handlers other extra)
    vector atOp (by omega) site.operation 2 1 left right ((copyFrame.lookup 2 (by decide)).trans rightRead) word arithmetic
  let pre := copyFrame.trans arithmeticFrame
  obtain ⟨saved, saveRun, saveFrame, savedLeft, ⟨atMask⟩⟩ := X86PlacedRegisterMove.executes (handlers other extra)
    vector atSave (by omega) 6 9 left ((pre.lookup 6 (by decide)).trans leftRead) saveCode
  let before := pre.trans saveFrame
  obtain ⟨masked, maskRun, maskFrame, maskLeft, maskRight, ⟨atXor⟩⟩ := stage_mask other extra vector atMask
    site.operation maskCode (by change site.rightXor ≤ image.size; omega) left right
    ((before.lookup 6 (by decide)).trans leftRead) savedLeft ((before.lookup 2 (by decide)).trans rightRead)
    ((saveFrame.lookup 1 (by decide)).trans sum)
  change At image masked base site.rightXor at atXor
  have sameSum := (maskFrame.lookup 1 (by decide)).trans ((saveFrame.lookup 1 (by decide)).trans sum)
  obtain ⟨xor, xorRun, xorFrame, tagged, ⟨atAnd⟩⟩ := X86PlacedLogical.executes (handlers other extra) vector
    atXor (by omega) .xor 1 2 (rightInput site.operation left right) wrapped sameSum maskRight xorCode
  obtain ⟨anded, andRun, andFrame, combined, ⟨atCompare⟩⟩ := X86PlacedLogical.executes (handlers other extra) vector
    atAnd (by omega) .and 2 9 (leftMask site.operation left right) (rightInput site.operation left right ^^^ wrapped)
    tagged ((xorFrame.lookup 9 (by decide)).trans maskLeft) andCode
  let combinedMask := leftMask site.operation left right &&& (rightInput site.operation left right ^^^ wrapped)
  obtain ⟨after, tested, testFrame, target⟩ := X86PlacedLiteral.compare_branch other extra vector atCompare .lessSigned
    9 (.nonnegative 0) branchCode combinedMask combined
  have signal : Comparison.lessSigned.evaluate combinedMask (X86CmpImmediate64.Literal.nonnegative 0).value =
      overflows site.operation left right := by
    unfold combinedMask wrapped
    cases site.operation <;> rfl
  rw [signal] at target
  let h := handlers other extra
  let n := maskSteps site.operation
  have r2 := @X86FuelPrefix.fetches_then h vector 1 1 native copied added copyRun arithmeticRun
  have r3 := @X86FuelPrefix.fetches_then h vector 2 1 native added saved r2 saveRun
  have rMask := @X86FuelPrefix.fetches_then h vector 3 n native saved masked r3 maskRun
  have rXor := @X86FuelPrefix.fetches_then h vector (3 + n) 1 native masked xor rMask xorRun
  have rAnd := @X86FuelPrefix.fetches_then h vector (3 + n + 1) 1 native xor anded rXor andRun
  have ran := @X86FuelPrefix.fetches_then h vector (3 + n + 1 + 1) 2 native anded after rAnd tested
  have total : (X86FuelPrefix.fetches site.steps).run native = .ok () after := by
    simpa only [Site.steps, n, show 3 + n + 1 + 1 + 2 = 7 + n by omega] using ran
  let tail := (xorFrame.trans andFrame).trans testFrame
  exact ⟨after, total, ((before.trans maskFrame).trans tail).mono (by decide),
    (tail.lookup 1 (by decide)).trans sameSum, target⟩

end Mettapedia.Machines.TIsa.X86PreparedSignedArithmetic
