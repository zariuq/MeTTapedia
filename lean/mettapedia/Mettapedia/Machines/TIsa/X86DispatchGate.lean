import Mettapedia.Machines.TIsa.X86PlacedInstruction
import Mettapedia.Machines.TIsa.X86PreparedCompare
import Mettapedia.Machines.TIsa.X86Immediate32

/-!
# Checked dispatch gates on a placed x86 image

A gate tests the native program-point register. A small key uses CMP with
a sign-extended immediate. An unsigned key outside that range first loads
the zero-extended immediate into the emitter's scratch register. Both
templates use the inverse Jcc to the false successor.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86DispatchGate

open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
open X86PlacedInstruction (At)
open X86PositiveImmediate (Immediate immediate64)
open X86PreparedCompare (BranchSite negative)

local instance : MemoryPrimitives := X86Memory.ordinary

def pointRegister : Fin 16 := 9
def literalRegister : Fin 16 := 14

inductive KeyEncoding where
  | small (literal : Immediate)
  | wide (literal : BitVec 32)
  deriving DecidableEq, Repr

def KeyEncoding.ofWord? (word : Word) : Option KeyEncoding :=
  if small : word.toNat < 2^31 then some (.small ⟨word.toNat, small⟩)
  else if word.toNat < 2^32 then some (.wide (word.setWidth 32)) else none

def KeyEncoding.word : KeyEncoding → Word
  | .small literal => immediate64 literal
  | .wide literal => literal.zeroExtend 64

theorem KeyEncoding.ofWord_exact {word : Word} {encoding : KeyEncoding}
    (chosen : ofWord? word = some encoding) : encoding.word = word := by
  unfold ofWord? at chosen
  split at chosen
  next short =>
    cases chosen
    apply BitVec.eq_of_toNat_eq
    exact X86PositiveImmediate.word_nat _
  next long =>
    split at chosen
    next fits =>
      cases chosen
      apply BitVec.eq_of_toNat_eq
      simp only [KeyEncoding.word, BitVec.zeroExtend, BitVec.toNat_setWidth,
        Nat.mod_eq_of_lt fits, Nat.mod_eq_of_lt word.isLt]
    next outside => cases chosen

theorem KeyEncoding.available (word : Word) (fits : word.toNat < 2^32) :
    ∃ encoding, ofWord? word = some encoding := by
  unfold ofWord?
  split <;> exact ⟨_, rfl⟩

/-- Register code occupies the lower half of the 32-bit numbering space.
    A head entry follows that code and uses a separately bounded index. -/
theorem prepared_head_key_fits (codeLength head : Nat)
    (codeBound : codeLength ≤ (2^32 - 1) / 2) (headBound : head < 4096) :
    codeLength + head < 2^32 := by omega

def KeyEncoding.materialize : KeyEncoding → List Nat
  | .small _ => []
  | .wide literal => X86Immediate32.code literalRegister literal

def KeyEncoding.compare : KeyEncoding → List Nat
  | .small literal => X86CmpImmediate64.code pointRegister (.nonnegative literal)
  | .wide _ =>
    [(rex true literalRegister pointRegister).toNat, 0x39,
      (modRM literalRegister pointRegister).toNat]

def KeyEncoding.instructions : KeyEncoding → Nat
  | .small _ => 2
  | .wide _ => 3

structure Gate where
  offset : Nat
  missed : Nat
  test : Comparison
  encoding : KeyEncoding
  deriving DecidableEq, Repr

def Gate.compareOffset (gate : Gate) : Nat := gate.offset + gate.encoding.materialize.length
def Gate.branchOffset (gate : Gate) : Nat := gate.compareOffset + gate.encoding.compare.length
def Gate.fallthrough (gate : Gate) : Nat := gate.branchOffset + 6
def Gate.delta (gate : Gate) : BitVec 32 := .ofInt 32 ((gate.missed : Int) - gate.fallthrough)
def Gate.branchCode (gate : Gate) : List Nat := X86NativeJcc.code (negative gate.test) gate.delta
def Gate.pick (gate : Gate) (key : Word) : Nat :=
  if gate.test.evaluate key gate.encoding.word then gate.fallthrough else gate.missed

def Gate.Valid (gate : Gate) (image : NativeImage.View) : Prop :=
  gate.fallthrough < image.size ∧ gate.missed < image.size ∧
    gate.delta.toInt = (gate.missed : Int) - gate.fallthrough ∧
    NativeImage.readRange? image gate.offset gate.encoding.materialize.length =
      some (gate.encoding.materialize.map (.ofNat 8)) ∧
    NativeImage.readRange? image gate.compareOffset gate.encoding.compare.length =
      some (gate.encoding.compare.map (.ofNat 8)) ∧
    NativeImage.readRange? image gate.branchOffset gate.branchCode.length =
      some (gate.branchCode.map (.ofNat 8))

instance (gate : Gate) (image : NativeImage.View) : Decidable (gate.Valid image) := by
  unfold Gate.Valid
  infer_instance

private theorem Gate.compare_inside (gate : Gate) (image : NativeImage.View) (valid : gate.Valid image) :
    gate.compareOffset + 3 ≤ image.size := by
  have extent := valid.1
  unfold fallthrough branchOffset at extent
  omega

private def branchSite {image : NativeImage.View} {state : State} {base : BitVec 48} {offset : Nat}
    (point : At image state base offset) (gate : Gate) (checked : gate.Valid image) :
    BranchSite state gate.test (address base.toInt gate.branchOffset) := by
  have fall := checked.1
  have miss := checked.2.1
  unfold Gate.fallthrough at fall
  refine { target := address base.toInt gate.missed, displacement := gate.delta, upper := ?_, jump := ?_, bytes := ?_ }
  · rw [point.location _ (by omega)]
    have upper := point.upper
    omega
  · rw [point.location _ miss.le, point.location _ (by omega), checked.2.2.1, Gate.fallthrough]
    omega
  · exact point.bytes gate.branchOffset (by omega) gate.branchCode checked.2.2.2.2.2

private theorem branch_selects {image : NativeImage.View} {state : State} {base : BitVec 48} {offset : Nat}
    (point : At image state base offset) (gate : Gate) (valid : gate.Valid image) (key : Word) :
    (if gate.test.evaluate key gate.encoding.word then address (address base.toInt gate.branchOffset).toInt 6
      else address base.toInt gate.missed) = address base.toInt (gate.pick key) := by
  have extent := valid.1
  unfold Gate.fallthrough at extent
  rw [point.relative_address gate.branchOffset 6 (by omega)]
  unfold Gate.pick Gate.fallthrough
  split <;> simp_all

noncomputable abbrev handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :=
  X86PreparedCompare.handlers (X86FrameStore.linkedHandlers other) extra

def writes : Finset Register := {.rip, .rflags, key literalRegister}

theorem writes_data : writes ⊆ dataRegisters := by decide

theorem keeps_point {before after : State} (frame : RegisterFrame writes before after) :
    lookup after pointRegister = lookup before pointRegister :=
  frame.lookup pointRegister (by decide)

private def decode_register_compare {image : NativeImage.View} {state : State} {base : BitVec 48}
    {offset : Nat} (point : At image state base offset) (inside : offset + 3 ≤ image.size)
    (code : codeLoaded state (address base.toInt offset).toInt
      [(rex true literalRegister pointRegister).toNat, 0x39, (modRM literalRegister pointRegister).toNat]) :
    X86LegacyFetch.Window state (0x39#8) true literalRegister pointRegister := by
  refine { toBasis := point.basis inside, prefixByte := ?_, opcodeByte := ?_, modrmByte := ?_ }
  · have read := code 0 (rex true literalRegister pointRegister).toNat (by rfl)
    rw [point.relative_address offset 0 (by omega)] at read
    change state.mem.get? ((address base.toInt offset).signExtend 52).toNat = _
    simpa only [Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] using read
  · have read := code 1 0x39 (by rfl)
    rw [point.relative_address offset 1 (by omega)] at read
    exact read
  · have read := code 2 (modRM literalRegister pointRegister).toNat (by rfl)
    rw [point.relative_address offset 2 (by omega)] at read
    change state.mem.get? ((address base.toInt (offset + 2)).signExtend 52).toNat = _
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using read

theorem Gate.executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {state : State} {base : BitVec 48}
    (gate : Gate) (checked : gate.Valid image) (point : At image state base gate.offset)
    (value : Word) (known : lookup state pointRegister = some value) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches gate.encoding.instructions).run state = .ok () after ∧
      RegisterFrame writes state after ∧ Nonempty (At image after base (gate.pick value)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  rcases gate with ⟨offset, missed, condition, encoding⟩
  cases encoding with
  | small literal =>
    let gate : Gate := ⟨offset, missed, condition, .small literal⟩
    let immediate : X86CmpImmediate64.Literal := .nonnegative literal
    have branchOffset : gate.branchOffset = offset + 7 := by
      simp [gate, Gate.branchOffset, Gate.compareOffset, KeyEncoding.materialize, KeyEncoding.compare,
        X86CmpImmediate64.code_length]
    have fits : offset + 7 + 6 < image.size := by
      have := checked.1
      rwa [Gate.fallthrough, branchOffset] at this
    let origin := point.basis (by omega : offset + 3 ≤ image.size)
    let branchAt := address base.toInt gate.branchOffset
    have code : codeLoaded state (address base.toInt offset).toInt (X86CmpImmediate64.code pointRegister immediate) :=
      point.bytes offset (by omega) _ checked.2.2.2.2.1
    have byte0 : state.mem.get? (origin.address.signExtend 52).toNat = some (rex true 7 pointRegister) := by
      have read := code 0 (rex true 7 pointRegister).toNat (by rfl)
      rw [point.relative_address offset 0 (by omega)] at read
      change state.mem.get? ((address base.toInt offset).signExtend 52).toNat = _
      simpa only [Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] using read
    have byte1 : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x81#8) := by
      have read := code 1 0x81 (by rfl)
      rw [point.relative_address offset 1 (by omega)] at read
      exact read
    have byte2 : state.mem.get? (origin.modrmAddress.signExtend 52).toNat = some (modRM 7 pointRegister) := by
      have read := code 2 (modRM 7 pointRegister).toNat (by rfl)
      rw [point.relative_address offset 2 (by omega)] at read
      change state.mem.get? ((address base.toInt (offset + 2)).signExtend 52).toNat = _
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using read
    have data : ∀ i < 4, state.mem.get? ((address origin.next.toInt i).signExtend 52).toNat =
        some (immediate.bits.extractLsb' (8 * i) 8) := by
      intro i inside
      have present : (X86CmpImmediate64.code pointRegister immediate)[3 + i]? =
          some ((immediate.bits.extractLsb' (8 * i) 8).toNat) := by interval_cases i <;> rfl
      have loaded := code (3 + i) _ present
      rw [point.relative_address offset (3 + i) (by omega)] at loaded
      change state.mem.get? ((address (address base.toInt (offset + 3)).toInt i).signExtend 52).toNat = _
      rw [point.relative_address _ _ (by omega), Nat.add_assoc]
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using loaded
    have advances : origin.next.toInt + 4 = branchAt.toInt := by
      change (address base.toInt (offset + 3)).toInt + 4 = (address base.toInt gate.branchOffset).toInt
      rw [branchOffset, point.location _ (by omega), point.location _ (by omega)]
      omega
    obtain ⟨after, ran, rip, frame, flags, read⟩ := X86PreparedCompare.fused_immediate_branch_flags
      (X86FrameStore.linkedHandlers other) extra vector state origin pointRegister immediate condition value
      point.flags branchAt advances known point.knownFlags point.quiet byte0 byte1 byte2 data
      (branchSite point gate checked)
    have next : after.regs.get? .rip = some ((address base.toInt (gate.pick value)).signExtend 64) := by
      rw [← branch_selects point gate checked value]
      exact rip
    exact ⟨after, ran, frame.mono (by decide), ⟨point.advance frame (by decide) next flags read⟩⟩
  | wide literal =>
    let gate : Gate := ⟨offset, missed, condition, .wide literal⟩
    have compareOffset : gate.compareOffset = offset + 6 := by
      simp [gate, Gate.compareOffset, KeyEncoding.materialize, X86Immediate32.code_length]
    have branchOffset : gate.branchOffset = offset + 9 := by
      rw [Gate.branchOffset, compareOffset]
      rfl
    have fits : offset + 9 + 6 < image.size := by
      have := checked.1
      rwa [Gate.fallthrough, branchOffset] at this
    let immediate : X86Immediate32.Inputs state literalRegister literal :=
      { toBasis := point.basis (show offset + 3 ≤ image.size from by omega)
        quiet := point.quiet
        upper := by
          change (address base.toInt offset).toInt + 6 < (2^47 : Int)
          rw [point.location _ (by omega)]
          have := point.upper
          omega
        loaded := point.bytes offset (by omega) _ checked.2.2.2.1 }
    obtain ⟨middle, moved, moveFrame, literalRead, rip⟩ :=
      X86Immediate32.executes (handlers other extra) vector state literalRegister literal immediate
    have atCompare : At image middle base gate.compareOffset := by
      apply point.advance moveFrame (X86Immediate32.writes_data _) _ point.flags
        ((moveFrame.registers .rflags (by decide)).trans point.knownFlags)
      rw [compareOffset, ← point.relative_address offset 6 (by omega)]
      exact rip
    have code := atCompare.bytes gate.compareOffset (by rw [compareOffset]; omega)
      gate.encoding.compare checked.2.2.2.2.1
    let window := decode_register_compare atCompare (gate.compare_inside image checked) code
    have atBranch : window.next = address base.toInt gate.branchOffset := by
      change address base.toInt (gate.compareOffset + 3) = _
      rw [compareOffset, branchOffset]
    let placedBranch := branchSite atCompare gate checked
    let nextSite : BranchSite middle condition window.next :=
      { target := placedBranch.target
        displacement := placedBranch.displacement
        upper := by rw [atBranch]; exact placedBranch.upper
        jump := by rw [atBranch]; exact placedBranch.jump
        bytes := by rw [atBranch]; exact placedBranch.bytes }
    obtain ⟨after, ran, next, frame, flags, read⟩ := X86PreparedCompare.fused_register_branch_flags
      (X86FrameStore.linkedHandlers other) extra vector middle literalRegister pointRegister window condition
      value (literal.zeroExtend 64) atCompare.flags ((moveFrame.lookup _ (by decide)).trans known) literalRead
      atCompare.knownFlags atCompare.quiet nextSite
    have target : nextSite.target = address base.toInt gate.missed := rfl
    have nextRIP : after.regs.get? .rip = some ((address base.toInt (gate.pick value)).signExtend 64) := by
      rw [← branch_selects atCompare gate checked value]
      change after.regs.get? .rip = some
        ((if condition.evaluate value (literal.zeroExtend 64) then
            address (address base.toInt gate.branchOffset).toInt 6
          else address base.toInt gate.missed).signExtend 64)
      simpa only [atBranch, target] using next
    refine ⟨after, X86FuelPrefix.fetches_then 1 2 state middle after moved ran, ?_,
      ⟨atCompare.advance frame (by decide) nextRIP flags read⟩⟩
    exact (moveFrame.trans frame).mono (by decide)

end Mettapedia.Machines.TIsa.X86DispatchGate
