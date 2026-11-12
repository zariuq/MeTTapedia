import Mettapedia.Machines.TIsa.SailRange
import Mettapedia.Machines.TIsa.X86Execution
import Mathlib.Tactic.IntervalCases

/-!
# Word and signed-displacement reads in the original Sail model

The original bytewise rb loop is related to a checked finite fold. Every
iteration retains its canonical-address check, app-view selection and memi
read. Little-endian assembly gives exact 64-bit and 32-bit results with state
preservation. The effective-address layer retains segment and alignment
checks; missing bytes and unaligned checked reads have explicit errors.

The signed displacement theorem uses the original rime_size implementation.
Controls cover changed and missing high bytes, alignment and sign extension.
Instruction fetch, effective-address decoding and full native load templates
remain separate composition obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace Mettapedia.Machines.TIsa.X86ReadWords

open _root_.X86Registers X86RegisterRefinement

def byteStep [MemoryPrimitives] (count : Nat) (addr : Word) (access : String)
    (offset : Int) (current : BitVec (8 * count)) : SailM (BitVec (8 * count)) := do
  if !(← Functions.canonical_address_p (addr.toInt + offset)) then
    Functions.x86_model_error "rb: non-canonical address"
  else pure ()
  let linear := Sail.BitVec.addInt (Functions.sail_mask_signed 48 addr) offset
  let physical ← (do
    if ← _root_.X86Registers.readReg .app_view then
      pure (Functions.sail_mask_signed 52 linear)
    else Functions.ia32e_la_to_pa linear access : SailM (BitVec 52))
  let byte ← Functions.memi physical
  pure (Sail.BitVec.updateSubrange current (Int.toNat (8 * offset + 7)) (Int.toNat (8 * offset))
    (byte.setWidth (Int.toNat (8 * offset + 7) - Int.toNat (8 * offset) + 1)))

theorem rb_fold [MemoryPrimitives] (count : Nat) (addr : Word) (access : String) :
    Functions.rb count addr access =
      (List.range count).foldlM (fun current (offset : Nat) =>
        byteStep count addr access (offset : Int) current) (0#(8 * count)) := by
  rw [← SailRange.forIn_foldlM]
  simp only [Functions.rb, byteStep, bind_assoc, pure_bind, bind_pure,
    SailRange.ite_bind, SailRange.ascending]
  rfl

local instance : MemoryPrimitives := X86Memory.ordinary

theorem add_offset (base : BitVec 48) (offset : Nat) :
    Sail.BitVec.addInt (Functions.sail_mask_signed 48 (base.signExtend 64)) (offset : Int) =
      X86Execution.address base.toInt offset := by
  rw [X86FetchMemory.narrow_pointer]
  unfold Sail.BitVec.addInt X86Execution.address
  rw [BitVec.ofInt_add, BitVec.ofInt_toInt]

theorem update_at_nat (count offset : Nat) (current : BitVec (8 * count)) (byte : BitVec 8) :
    Sail.BitVec.updateSubrange current (Int.toNat (8 * (offset : Int) + 7)) (Int.toNat (8 * (offset : Int)))
      (byte.setWidth (Int.toNat (8 * (offset : Int) + 7) - Int.toNat (8 * (offset : Int)) + 1)) =
      Sail.BitVec.updateSubrange' current (8 * offset) 8 byte := by
  have low : Int.toNat (8 * (offset : Int)) = 8 * offset := by omega
  have width : Int.toNat (8 * (offset : Int) + 7) - Int.toNat (8 * (offset : Int)) + 1 = 8 := by omega
  unfold Sail.BitVec.updateSubrange
  rw [width, low, BitVec.setWidth_eq]

theorem byteStep_app (count offset : Nat) (within : offset < count)
    (state : State) (base : BitVec 48)
    (current : BitVec (8 * count)) (access : String)
    (upper : base.toInt + count ≤ (2 ^ 47 : Int))
    (application : state.regs.get? .app_view = some true) :
    (byteStep count (base.signExtend 64) access (offset : Int) current).run state =
      (do let byte ← Functions.memi ((X86Execution.address base.toInt offset).signExtend 52)
          pure (Sail.BitVec.updateSubrange' current (8 * offset) 8 byte)).run state := by
  have lower : -(2 ^ 47 : Int) ≤ base.toInt := by simpa using BitVec.le_toInt base
  have lastSafe : base.toInt + (count - 1 : Nat) < (2 ^ 47 : Int) := by omega
  have canonical := X86Move.canonical48 state (X86Execution.address base.toInt offset)
  rw [X86Execution.address_toInt _ lower lastSafe _ (by omega)] at canonical
  unfold byteStep
  rw [BitVec.toInt_signExtend_of_le (by decide : 48 ≤ 64), run_bind, canonical]
  dsimp only
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  rw [add_offset, run_bind, run_bind, readRegister_exact, application]
  dsimp only
  rw [X86FetchMemory.widen_physical, if_pos rfl, run_pure]
  dsimp only
  simp only [update_at_nat]

theorem byteStep_exact (count offset : Nat) (within : offset < count)
    (state : State) (base : BitVec 48) (pointer : Word) (byte : BitVec 8)
    (current : BitVec (8 * count)) (access : String)
    (upper : base.toInt + count ≤ (2 ^ 47 : Int))
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (present : state.mem.get? ((X86Execution.address base.toInt offset).signExtend 52).toNat = some byte) :
    (byteStep count (base.signExtend 64) access (offset : Int) current).run state =
      .ok (Sail.BitVec.updateSubrange' current (8 * offset) 8 byte) state := by
  rw [byteStep_app count offset within state base current access upper application]
  rw [run_bind, X86FetchMemory.memi_exact state pointer _ byte rip present]
  rfl

theorem byteStep_missing (count offset : Nat) (within : offset < count)
    (state : State) (base : BitVec 48) (current : BitVec (8 * count)) (access : String)
    (upper : base.toInt + count ≤ (2 ^ 47 : Int))
    (application : state.regs.get? .app_view = some true)
    (missing : state.mem.get? ((X86Execution.address base.toInt offset).signExtend 52).toNat = none) :
    (byteStep count (base.signExtend 64) access (offset : Int) current).run state =
      .error (.OutOfMemoryRange ((X86Execution.address base.toInt offset).signExtend 52).toNat) state := by
  rw [byteStep_app count offset within state base current access upper application]
  rw [run_bind, X86FetchMemory.memi_missing state _ missing]

theorem foldlM_readonly {α β : Type} (items : List α) (body : β → α → SailM β)
    (step : β → α → β) (state : State)
    (known : ∀ item ∈ items, ∀ value, (body value item).run state = .ok (step value item) state)
    (initial : β) :
    (items.foldlM body initial).run state = .ok (items.foldl step initial) state := by
  induction items generalizing initial with
  | nil => rfl
  | cons head tail ih =>
    rw [List.foldlM_cons, run_bind, known head (by simp) initial]
    dsimp only
    exact ih (fun item member value => known item (by simp [member]) value) (step initial head)

def assembled (value : Word) : Word :=
  (List.range 8).foldl (fun current index =>
    Sail.BitVec.updateSubrange' current (8 * index) 8 (value.extractLsb' (8 * index) 8)) (0#64)

theorem assembled_exact (value : Word) : assembled value = value := by
  apply BitVec.eq_of_getLsbD_eq
  intro index bound
  interval_cases index <;>
    simp [assembled, List.range_succ, Sail.BitVec.updateSubrange']

theorem rb_word_exact (state : State) (base : BitVec 48) (pointer value : Word) (access : String)
    (upper : base.toInt + 8 ≤ (2 ^ 47 : Int))
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (present : ∀ index < 8,
      state.mem.get? ((X86Execution.address base.toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8)) :
    (Functions.rb 8 (base.signExtend 64) access).run state = .ok value state := by
  rw [rb_fold]
  have folded := foldlM_readonly (List.range 8)
    (fun current (offset : Nat) => byteStep 8 (base.signExtend 64) access (offset : Int) current)
    (fun current offset => Sail.BitVec.updateSubrange' current (8 * offset) 8 (value.extractLsb' (8 * offset) 8))
    state (fun offset member current => byteStep_exact 8 offset (List.mem_range.mp member)
      state base pointer _ current access upper application rip (present offset (List.mem_range.mp member))) (0#64)
  rw [folded]
  change (EStateM.Result.ok (assembled value) state : EStateM.Result (Sail.Error exception) State Word) = _
  rw [assembled_exact]

def assembled32 (value : BitVec 32) : BitVec 32 :=
  (List.range 4).foldl (fun current index =>
    Sail.BitVec.updateSubrange' current (8 * index) 8 (value.extractLsb' (8 * index) 8)) (0#32)

theorem assembled32_exact (value : BitVec 32) : assembled32 value = value := by
  apply BitVec.eq_of_getLsbD_eq
  intro index bound
  interval_cases index <;>
    simp [assembled32, List.range_succ, Sail.BitVec.updateSubrange']

theorem rb_dword_exact (state : State) (base : BitVec 48) (pointer : Word) (value : BitVec 32) (access : String)
    (upper : base.toInt + 4 ≤ (2 ^ 47 : Int))
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (present : ∀ index < 4,
      state.mem.get? ((X86Execution.address base.toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8)) :
    (Functions.rb 4 (base.signExtend 64) access).run state = .ok value state := by
  rw [rb_fold]
  have folded := foldlM_readonly (List.range 4)
    (fun current (offset : Nat) => byteStep 4 (base.signExtend 64) access (offset : Int) current)
    (fun current offset => Sail.BitVec.updateSubrange' current (8 * offset) 8 (value.extractLsb' (8 * offset) 8))
    state (fun offset member current => byteStep_exact 4 offset (List.mem_range.mp member)
      state base pointer _ current access upper application rip (present offset (List.mem_range.mp member))) (0#32)
  rw [folded]
  change (EStateM.Result.ok (assembled32 value) state :
    EStateM.Result (Sail.Error exception) State (BitVec 32)) = _
  rw [assembled32_exact]

theorem rb_word_missing_last (state : State) (base : BitVec 48) (pointer value : Word) (access : String)
    (upper : base.toInt + 8 ≤ (2 ^ 47 : Int))
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (present : ∀ index < 7,
      state.mem.get? ((X86Execution.address base.toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8))
    (missing : state.mem.get? ((X86Execution.address base.toInt 7).signExtend 52).toNat = none) :
    (Functions.rb 8 (base.signExtend 64) access).run state =
      .error (.OutOfMemoryRange ((X86Execution.address base.toInt 7).signExtend 52).toNat) state := by
  rw [rb_fold, List.range_succ, List.foldlM_append, run_bind]
  have prefixRead := foldlM_readonly (List.range 7)
    (fun current (offset : Nat) => byteStep 8 (base.signExtend 64) access (offset : Int) current)
    (fun current offset => Sail.BitVec.updateSubrange' current (8 * offset) 8 (value.extractLsb' (8 * offset) 8))
    state (fun offset member current => byteStep_exact 8 offset (by have := List.mem_range.mp member; omega)
      state base pointer _ current access upper application rip (present offset (List.mem_range.mp member))) (0#64)
  rw [prefixRead]
  dsimp only
  simp only [List.foldlM_cons, List.foldlM_nil, bind_pure]
  exact byteStep_missing 8 7 (by decide) state base _ access upper application missing

theorem data_linear_address (state : State) (base : BitVec 48) (count : Nat) :
    (Functions.ea_to_la .Mode_64bit (base.signExtend 64) 3 count).run state =
      .ok (base.signExtend 64) state := by
  unfold Functions.ea_to_la
  simp only [Functions.in_64bit_mode, ite_true]
  change (do
    let linear ← (pure (base.signExtend 64) : SailM Word)
    if !(← Functions.canonical_address_p linear.toInt) then
      Functions.x86_model_error ":NON-CANONICAL-ADDRESS"
    else pure ()
    pure linear : SailM Word).run state = _
  rw [run_bind, run_pure]
  dsimp only
  rw [run_bind]
  have canonical : (Functions.canonical_address_p (base.signExtend 64).toInt).run state =
      .ok true state := by
    simpa only [BitVec.toInt_signExtend_of_le (by decide : 48 ≤ 64)] using X86Move.canonical48 state base
  rw [canonical]
  rfl

theorem truncate48 (base : BitVec 48) : Sail.BitVec.truncate (base.signExtend 64) 48 = base := by
  unfold Sail.BitVec.truncate
  apply BitVec.eq_of_getLsbD_eq
  intro index bound
  have wide : index < 64 := by omega
  simp [bound, wide, BitVec.getElem_signExtend]

theorem word_alignment (base : BitVec 48) (pointer : Bool) :
    Functions.address_aligned_p base 8 pointer =
      (pure ((base &&& (7#48)) == (0#48)) : SailM Bool) := by
  unfold Functions.address_aligned_p
  simp only [show ((8 : Nat) == 4) = false from rfl, Bool.and_false,
    Bool.false_eq_true, ite_false]
  have range : Functions.check_range 0 65 7 = (pure 7 : SailM Int) := rfl
  change (do let mask ← Functions.check_range 0 65 7
             pure ((base &&& Functions.bits_of_int mask 48) == (0#48))) = _
  rw [range, pure_bind]
  rfl

theorem word_access_check (base : BitVec 48) (baseRegister : Option Nat) (access : String)
    (checkAlignment pointer : Bool)
    (safe : checkAlignment = false ∨ base &&& (7#48) = (0#48)) :
    Functions.check_linear_memory_access .Mode_64bit 8 8 (base.signExtend 64)
      baseRegister 3 access checkAlignment pointer = (pure () : SailM Unit) := by
  unfold Functions.check_linear_memory_access
  rw [truncate48, word_alignment]
  simp only [pure_bind]
  rcases safe with disabled | aligned
  · subst checkAlignment
    rfl
  · simp only [aligned, beq_self_eq_true, Bool.or_true, Bool.not_true, Bool.false_eq_true, ite_false]

theorem load_word_uses_rb (state : State) (base : BitVec 48) (baseRegister : Option Nat)
    (attributes : Vector (BitVec 16) 6) (access : String) (checkAlignment pointer : Bool)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (safe : checkAlignment = false ∨ base &&& (7#48) = (0#48)) :
    (Functions.load_bytes_from_ea .Mode_64bit 8 8 (base.signExtend 64) baseRegister 3 access
      checkAlignment pointer).run state = (Functions.rb 8 (base.signExtend 64) access).run state := by
  unfold Functions.load_bytes_from_ea
  rw [run_bind, readRegister_exact, segments]
  dsimp only
  change (do
    let linear ← Functions.ea_to_la .Mode_64bit (base.signExtend 64) 3 8
    Functions.check_linear_memory_access .Mode_64bit 8 8 linear baseRegister 3 access checkAlignment pointer
    Functions.rb 8 linear access : SailM Word).run state = _
  rw [run_bind, data_linear_address]
  dsimp only
  rw [word_access_check base baseRegister access checkAlignment pointer safe]
  rfl

theorem load_word_exact (state : State) (base : BitVec 48) (baseRegister : Option Nat)
    (attributes : Vector (BitVec 16) 6) (pointer value : Word) (access : String)
    (checkAlignment memoryPointer : Bool)
    (upper : base.toInt + 8 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (safe : checkAlignment = false ∨ base &&& (7#48) = (0#48))
    (present : ∀ index < 8,
      state.mem.get? ((X86Execution.address base.toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8)) :
    (Functions.load_bytes_from_ea .Mode_64bit 8 8 (base.signExtend 64) baseRegister 3 access
      checkAlignment memoryPointer).run state = .ok value state := by
  rw [load_word_uses_rb state base baseRegister attributes access checkAlignment memoryPointer segments safe]
  exact rb_word_exact state base pointer value access upper application rip present

theorem load_word_unaligned (state : State) (base : BitVec 48) (baseRegister : Option Nat)
    (attributes : Vector (BitVec 16) 6) (access : String) (memoryPointer : Bool)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (unaligned : base &&& (7#48) ≠ (0#48)) :
    (Functions.load_bytes_from_ea .Mode_64bit 8 8 (base.signExtend 64) baseRegister 3 access
      true memoryPointer).run state = .error (.User (.Emsg "Fault: :UNALIGNED-LINEAR-ADDRESS")) state := by
  unfold Functions.load_bytes_from_ea
  rw [run_bind, readRegister_exact, segments]
  dsimp only
  change (do
    let linear ← Functions.ea_to_la .Mode_64bit (base.signExtend 64) 3 8
    Functions.check_linear_memory_access .Mode_64bit 8 8 linear baseRegister 3 access true memoryPointer
    Functions.rb 8 linear access : SailM Word).run state = _
  rw [run_bind, data_linear_address]
  dsimp only
  unfold Functions.check_linear_memory_access
  rw [truncate48, word_alignment]
  have unequal : ((base &&& (7#48)) == (0#48)) = false := by simpa only [beq_eq_false_iff_ne] using unaligned
  simp only [pure_bind, unequal, Bool.not_true, Bool.false_or, Bool.not_false, ite_true]
  rfl

theorem code_linear_dword (state : State) (base : BitVec 48) :
    (Functions.ea_to_la .Mode_64bit (base.signExtend 64) 1 4).run state =
      .ok (base.signExtend 64) state :=
  X86EffectiveFetch.code_linear_address state base

theorem code_dword_access (address : Word) :
    Functions.check_linear_memory_access .Mode_64bit 8 4 address none 1 ":X" false false =
      (pure () : SailM Unit) := by
  unfold Functions.check_linear_memory_access Functions.address_aligned_p
  rfl

theorem code_dword_uses_rb (state : State) (base : BitVec 48)
    (attributes : Vector (BitVec 16) 6)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes) :
    (Functions.load_bytes_from_ea .Mode_64bit 8 4 (base.signExtend 64) none 1 ":X" false false).run state =
      (Functions.rb 4 (base.signExtend 64) ":X").run state := by
  unfold Functions.load_bytes_from_ea
  rw [run_bind, readRegister_exact, segments]
  dsimp only
  change (do
    let linear ← Functions.ea_to_la .Mode_64bit (base.signExtend 64) 1 4
    Functions.check_linear_memory_access .Mode_64bit 8 4 linear none 1 ":X" false false
    Functions.rb 4 linear ":X" : SailM (BitVec 32)).run state = _
  rw [run_bind, code_linear_dword]
  dsimp only
  rw [code_dword_access]
  rfl

theorem signed_displacement_exact (state : State) (base : BitVec 48)
    (attributes : Vector (BitVec 16) 6) (pointer : Word) (value : BitVec 32)
    (upper : base.toInt + 4 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (present : ∀ index < 4,
      state.mem.get? ((X86Execution.address base.toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8)) :
    (Functions.rime_size .Mode_64bit 8 4 (base.signExtend 64) none 1 ":X" false false).run state =
      .ok (value.signExtend 64) state := by
  unfold Functions.rime_size
  rw [run_bind, code_dword_uses_rb state base attributes segments,
    rb_dword_exact state base pointer value ":X" upper application rip present]
  rfl

namespace Controls

private def attributes : Vector (BitVec 16) 6 := Vector.replicate 6 (0#16)

private def mapped (value : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .app_view true
  let registers := registers.insert .rip (0x2000#64)
  let registers := registers.insert .seg_hidden_attrs attributes
  let memory := (∅ : Std.ExtHashMap Nat (BitVec 8)).insert 4096 (value.extractLsb' 0 8)
  let memory := memory.insert 4097 (value.extractLsb' 8 8)
  let memory := memory.insert 4098 (value.extractLsb' 16 8)
  let memory := memory.insert 4099 (value.extractLsb' 24 8)
  let memory := memory.insert 4100 (value.extractLsb' 32 8)
  let memory := memory.insert 4101 (value.extractLsb' 40 8)
  let memory := memory.insert 4102 (value.extractLsb' 48 8)
  let memory := memory.insert 4103 (value.extractLsb' 56 8)
  ⟨registers, (), memory, (), 0, #[]⟩

private theorem byte_present (value : Word) (index : Nat) (within : index < 8) :
    (mapped value).mem.get? ((X86Execution.address (0x1000#48).toInt index).signExtend 52).toNat =
      some (value.extractLsb' (8 * index) 8) := by
  interval_cases index <;> simp [mapped, X86Execution.address, Std.ExtHashMap.getElem_insert]

theorem mapped_word_read (value : Word) :
    (Functions.load_bytes_from_ea .Mode_64bit 8 8 (0x1000#64) none 3 ":R" true false).run (mapped value) =
      .ok value (mapped value) := by
  apply load_word_exact (mapped value) (0x1000#48) none attributes (0x2000#64) value ":R" true false
  · decide
  · simp [mapped]
  · simp [mapped, Std.ExtDHashMap.get?_insert]
  · simp [mapped, Std.ExtDHashMap.get?_insert]
  · exact Or.inr (by decide)
  · exact byte_present value

theorem changed_high_byte_refuses_original_word :
    (Functions.load_bytes_from_ea .Mode_64bit 8 8 (0x1000#64) none 3 ":R" true false).run
      (mapped (0x1123456789abcdef#64)) ≠
      .ok (0x0123456789abcdef#64) (mapped (0x1123456789abcdef#64)) := by
  rw [mapped_word_read]
  intro wrong
  exact (by decide : (0x1123456789abcdef#64) ≠ (0x0123456789abcdef#64)) (EStateM.Result.ok.inj wrong).1

private def truncated (value : Word) : State := { mapped value with mem := (mapped value).mem.erase 4103 }

theorem missing_high_byte_refused :
    (Functions.rb 8 (0x1000#64) ":R").run (truncated (0x0123456789abcdef#64)) =
      .error (.OutOfMemoryRange 4103) (truncated (0x0123456789abcdef#64)) := by
  apply rb_word_missing_last _ (0x1000#48) (0x2000#64) (0x0123456789abcdef#64) ":R"
  · decide
  · simp [truncated, mapped, Std.ExtDHashMap.get?_insert]
  · simp [truncated, mapped, Std.ExtDHashMap.get?_insert]
  · intro index within
    interval_cases index <;> simp [truncated, mapped, X86Execution.address,
      Std.ExtHashMap.getElem_insert]
  · simp [truncated, X86Execution.address]

theorem unaligned_word_refused :
    (Functions.load_bytes_from_ea .Mode_64bit 8 8 (0x1001#64) none 3 ":R" true false).run
      (mapped (0x0123456789abcdef#64)) = .error (.User (.Emsg "Fault: :UNALIGNED-LINEAR-ADDRESS"))
        (mapped (0x0123456789abcdef#64)) :=
  load_word_unaligned _ (0x1001#48) none attributes ":R" false (by simp [mapped]) (by decide)

theorem negative_displacement_sign_extends :
    (Functions.rime_size .Mode_64bit 8 4 (0x1000#64) none 1 ":X" false false).run
      (mapped (0x00000000fffffff0#64)) =
      .ok (0xfffffffffffffff0#64) (mapped (0x00000000fffffff0#64)) := by
  apply signed_displacement_exact _ (0x1000#48) attributes (0x2000#64) (0xfffffff0#32)
  · decide
  · simp [mapped]
  · simp [mapped, Std.ExtDHashMap.get?_insert]
  · simp [mapped, Std.ExtDHashMap.get?_insert]
  · intro index within
    interval_cases index <;> simp [mapped, X86Execution.address, Std.ExtHashMap.getElem_insert]

theorem zero_extended_negative_displacement_refused :
    (Functions.rime_size .Mode_64bit 8 4 (0x1000#64) none 1 ":X" false false).run
      (mapped (0x00000000fffffff0#64)) ≠
      .ok (0x00000000fffffff0#64) (mapped (0x00000000fffffff0#64)) := by
  rw [negative_displacement_sign_extends]
  intro wrong
  exact (by decide : (0xfffffffffffffff0#64) ≠ (0x00000000fffffff0#64)) (EStateM.Result.ok.inj wrong).1

end Controls
end Mettapedia.Machines.TIsa.X86ReadWords

#print axioms Mettapedia.Machines.TIsa.X86ReadWords.rb_fold
#print axioms Mettapedia.Machines.TIsa.X86ReadWords.byteStep_exact
#print axioms Mettapedia.Machines.TIsa.X86ReadWords.rb_word_exact
#print axioms Mettapedia.Machines.TIsa.X86ReadWords.rb_dword_exact
#print axioms Mettapedia.Machines.TIsa.X86ReadWords.rb_word_missing_last
#print axioms Mettapedia.Machines.TIsa.X86ReadWords.load_word_exact
#print axioms Mettapedia.Machines.TIsa.X86ReadWords.signed_displacement_exact
#print axioms Mettapedia.Machines.TIsa.X86ReadWords.Controls.changed_high_byte_refuses_original_word
#print axioms Mettapedia.Machines.TIsa.X86ReadWords.Controls.missing_high_byte_refused
#print axioms Mettapedia.Machines.TIsa.X86ReadWords.Controls.zero_extended_negative_displacement_refused
