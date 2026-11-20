import Mettapedia.Machines.TIsa.X86PlacedJcc
import Mettapedia.Machines.TIsa.X86GroupByte
import Mettapedia.Machines.TIsa.P1WordExecution

/-! # The checked short-immediate FUND prefix

The taken edge leaves the hardware allowance at its reached value.
Fallthrough pays once. The source balance relates that live allowance
to p1's explicit budget and spent receipt.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 340000

namespace Mettapedia.Machines.TIsa.X86PlacedFund

open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (Code handlers)
open X86SubByteImmediate (word)
local instance : MemoryPrimitives := X86Memory.ordinary

structure Layout where
  start : Nat
  exhausted : Nat
  units : Fin 128

def Layout.delta (layout : Layout) : BitVec 32 :=
  .ofInt 32 ((layout.exhausted : Int) - (layout.start + 10))

def Layout.sourceUnits (layout : Layout) : BitVec 32 := .ofNat 32 layout.units.val

def Layout.Checked (layout : Layout) (image : NativeImage.View) : Prop :=
  layout.start + 14 ≤ image.size ∧ layout.exhausted ≤ image.size ∧
  0 < layout.units.val ∧
  (layout.exhausted : Int) = layout.start + 10 + layout.delta.toInt ∧
  Code image layout.start (X86GroupByte.code .cmp 5 layout.units) ∧
  Code image (layout.start + 4) (X86NativeJcc.code (.ordinary .below) layout.delta) ∧
  Code image (layout.start + 10) (X86GroupByte.code .sub 5 layout.units)

instance (layout : Layout) (image : NativeImage.View) : Decidable (layout.Checked image) :=
  inferInstanceAs (Decidable (_ ∧ _))

abbrev writes : Finset Register := {.rbp, .rflags, .rip}

private theorem group (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {state : State} {base : BitVec 48}
    {offset : Nat} (point : At image state base offset) (inside : offset + 4 ≤ image.size)
    (kind : X86GroupByte.Kind) (units : Fin 128) (value : Word) (known : lookup state 5 = some value)
    (code : Code image offset (X86GroupByte.code kind 5 units)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run state = .ok () after ∧ RegisterFrame writes state after ∧
      lookup after 5 = some (if kind = .cmp then value else kind.result value (word units)) ∧
      ∃ reached : At image after base (offset + 4),
        X86NativeJcc.selects (.ordinary .below) reached.flags = kind.carry value (word units) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let origin := point.basis (by omega)
  let finish := address base.toInt (offset + 4)
  have slot (index byte : Nat) (present : (X86GroupByte.code kind 5 units)[index]? = some byte) :
      state.mem.get? ((address base.toInt (offset + index)).signExtend 52).toNat = some (.ofNat 8 byte) := by
    have found := point.bytes offset (by omega) _ code index byte present
    rwa [point.relative_address offset index (by omega)] at found
  obtain ⟨output, ran, carry⟩ := X86GroupByte.fetched (handlers other extra) vector state origin finish
    kind 5 units value point.flags (by
      change (address base.toInt (offset + 3)).toInt + 1 = (address base.toInt (offset + 4)).toInt
      rw [point.location _ (by omega), point.location _ inside]
      omega) known point.knownFlags point.quiet
    (by simpa only [origin, At.basis, Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      slot 0 (rex true kind.digit 5).toNat rfl)
    (by exact slot 1 0x83 rfl)
    (by simpa only [origin, At.basis, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      slot 2 (modRM kind.digit 5).toNat rfl)
    (by exact slot 3 units.val rfl)
  have installed : X86FrameIncrement.linkedHandlers (handlers other extra) = handlers other extra := rfl
  rw [installed] at ran
  let flags := X86Flags.mergeFlags point.flags output
  let updated := kind.updated state 5 value (word units)
  let after := X86Move.putPointer (X86Flags.putFlags updated flags) finish
  have kept : RegisterFrame writes state updated := by
    unfold updated X86GroupByte.Kind.updated
    split
    · exact RegisterFrame.refl _ _
    · exact (put_frame _ _ _).mono (by decide)
  have frame : RegisterFrame writes state after :=
    (kept.trans ((flags_frame _ _).trans (pointer_frame _ _))).mono (by decide)
  have flagRead : after.regs.get? .rflags = some flags := by
    rw [(pointer_frame _ _).registers .rflags (by decide)]
    simp [X86Flags.putFlags]
  refine ⟨after, X86FuelPrefix.fetches_one _ _ ran, frame, ?_,
    point.advance frame (by decide) (X86FuelPrefix.pointer_rip _ _) flags flagRead, ?_⟩
  · rw [X86Move.lookup_putPointer, (flags_frame _ _).lookup 5 (by decide)]
    unfold updated X86GroupByte.Kind.updated
    split
    · exact known
    · exact lookup_put_same ..
  · change ((1#1) == Functions._get_rflagsbits_cf flags) = _
    change Functions._get_rflagsbits_cf flags = _ at carry
    rw [carry]
    cases kind.carry value (word units) <;> rfl

theorem executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {state : State} {base : BitVec 48}
    {layout : Layout} (point : At image state base layout.start) (checked : layout.Checked image)
    (allowance : Word) (known : lookup state 5 = some allowance) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    let short := allowance < word layout.units
    ∃ after, (X86FuelPrefix.fetches (if short then 2 else 3)).run state = .ok () after ∧
      RegisterFrame writes state after ∧
      lookup after 5 = some (if short then allowance else allowance - word layout.units) ∧
      Nonempty (At image after base (if short then layout.exhausted else layout.start + 14)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨extent, target, _, jumps, cmp, branch, sub⟩ := checked
  obtain ⟨compared, comparison, compareFrame, same, choice, carry⟩ :=
    group other extra vector point (by omega) .cmp layout.units allowance known cmp
  obtain ⟨branched, jump, jumpFrame, reached⟩ :=
    X86PlacedJcc.executes other extra vector choice (target := layout.exhausted) (by omega) target
      (.ordinary .below) layout.delta (by omega) branch
  have total := @X86FuelPrefix.fetches_then (handlers other extra) vector 1 1 state compared branched comparison jump
  have kept := (compareFrame.trans jumpFrame).mono (by decide : writes ∪ {.rip} ⊆ writes)
  have available := (jumpFrame.lookup 5 (by decide)).trans (show lookup compared 5 = some allowance from same)
  have edge : Nonempty (At image branched base
      (if allowance < word layout.units then layout.exhausted else layout.start + 10)) := by
    simpa only [carry, X86GroupByte.Kind.carry, decide_eq_true_eq, BitVec.lt_def] using reached
  dsimp only
  by_cases short : allowance < word layout.units
  · simp only [if_pos short]
    exact ⟨branched, total, kept, available, by simpa only [if_pos short] using edge⟩
  · simp only [if_neg short]
    obtain ⟨atDebit⟩ : Nonempty (At image branched base (layout.start + 10)) := by
      simpa only [if_neg short] using edge
    obtain ⟨after, debit, written, balance, following, _⟩ :=
      group other extra vector atDebit (by exact extent) .sub layout.units allowance available sub
    have ran := @X86FuelPrefix.fetches_then (handlers other extra) vector 2 1 state branched after total debit
    exact ⟨after, ran, (kept.trans written).mono (by simp), balance, ⟨following⟩⟩

private theorem source_units (layout : Layout) :
    layout.sourceUnits.zeroExtend 64 = word layout.units := by
  apply BitVec.eq_of_toNat_eq
  rw [X86SubByteImmediate.word_nat]
  have fit := layout.units.isLt
  simp only [Layout.sourceUnits, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : layout.units.val < 2^32),
    Nat.mod_eq_of_lt (by omega : layout.units.val < 2^64)]

theorem refines (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {state : State} {base : BitVec 48}
    {layout : Layout} (point : At image state base layout.start) (checked : layout.Checked image)
    (model : P1WordExecution.State) (known : lookup state 5 = some (model.budget - model.spent)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, RegisterFrame writes state after ∧
      match P1WordExecution.fund model layout.sourceUnits with
      | .continuing paid =>
        (X86FuelPrefix.fetches 3).run state = .ok () after ∧
          lookup after 5 = some (paid.budget - paid.spent) ∧ Nonempty (At image after base (layout.start + 14))
      | .returned status payload reached =>
        status = .exhausted ∧ payload = .ofNat 64 4 ∧ reached = model ∧
          (X86FuelPrefix.fetches 2).run state = .ok () after ∧
          lookup after 5 = some (model.budget - model.spent) ∧ Nonempty (At image after base layout.exhausted) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, ran, frame, available, next⟩ := executes other extra vector point checked _ known
  refine ⟨after, frame, ?_⟩
  unfold P1WordExecution.fund
  rw [source_units]
  by_cases short : model.budget - model.spent < word layout.units
  · simp only [if_pos short] at ran available next ⊢
    exact ⟨rfl, rfl, rfl, ran, available, next⟩
  · simp only [if_neg short] at ran available next ⊢
    refine ⟨ran, ?_, next⟩
    simpa only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.add_assoc] using available

end Mettapedia.Machines.TIsa.X86PlacedFund
