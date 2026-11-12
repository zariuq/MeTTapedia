import Mettapedia.Machines.TIsa.X86ReadWords
import Mettapedia.Machines.TIsa.X86StateFrame

/-!
# Bytewise writes in the original Sail memory path

The actual inclusive wb loop is related to a finite stateful fold, retaining
canonical checks, app-view selection, ordinary byte writes and diagnostic
RIP reads. The result has an exact byte footprint and preserves registers
and the remaining state. Eight-byte readback and store-helper alignment
checks are proved from those implementations. Native instruction handlers,
capability ownership and address-model linkage remain separate obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace Mettapedia.Machines.TIsa.X86WriteWords

open _root_.X86Registers X86RegisterRefinement
open Sail.ConcurrencyInterfaceV1

def putByte (state : State) (address : Nat) (value : BitVec 8) : State :=
  { state with mem := state.mem.insert address value }

theorem writeByte_exact (state : State) (address : Nat) (value : BitVec 8) :
    (PreSail.writeByte address value : SailM PUnit).run state = .ok () (putByte state address value) := by rfl

local instance : MemoryPrimitives := X86Memory.ordinary

theorem write_one (state : State) (address : BitVec 64) (value : BitVec 8) :
    (X86Memory.ordinary.writeValue .Write_plain 64 address 1 value).run state =
      .ok true (putByte state address.toNat value) := by
  change (PreSail.writeBytes (n := 1) address.toNat value : SailM Bool).run state = _
  have action : (PreSail.writeBytes (n := 1) address.toNat value : SailM Bool) = (do
    let _ ← PreSail.writeByte address.toNat (value.extractLsb' 0 8)
    pure true) := rfl
  rw [action, BitVec.extractLsb'_eq_self, run_bind, writeByte_exact]
  rfl

theorem log_memory_write_exact (state : State) (pointer : Word) (address : BitVec 52)
    (value : BitVec 8) (known : state.regs.get? .rip = some pointer) :
    (Functions.log_memory_write address 1 value).run state = .ok () state := by
  unfold Functions.log_memory_write Functions.read_rip
  rw [run_bind, run_bind, readRegister_exact, known]
  rfl

theorem bang_memi_exact (state : State) (pointer : Word) (address : BitVec 52) (value : BitVec 8)
    (rip : state.regs.get? .rip = some pointer) :
    (Functions.bang_memi address value).run state = .ok () (putByte state address.toNat value) := by
  unfold Functions.bang_memi
  rw [run_bind]
  change (do
    let _ ← (pure () : SailM Unit)
    let _ ← X86Memory.ordinary.writeValue .Write_plain 64 (Functions.sail_mask 64 address) 1 value
    Functions.log_memory_write address 1 value : SailM Unit).run state = _
  rw [run_bind, write_one, X86FetchMemory.mask52_toNat]
  dsimp only
  exact log_memory_write_exact _ pointer address value rip

theorem discard_unit (action : SailM Unit) : (do let _ ← action; pure ()) = action := by
  have next : (fun _ : Unit => (pure () : SailM Unit)) = pure := by funext value; cases value; rfl
  change (action >>= fun _ => pure ()) = action
  rw [next, bind_pure]

def byteStep [MemoryPrimitives] (count : Nat) (address : Word) (access : String)
    (value : BitVec (8 * count)) (offset : Int) (_ : Unit) : SailM Unit := do
  if !(← Functions.canonical_address_p (address.toInt + offset)) then
    let _ : Unit := if offset != 0 then
      Functions.observe_mem_write (Functions.sail_mask_signed 48 address) (offset - 1) else ()
    Functions.x86_model_error "wb: non-canonical address"
  else pure ()
  let linear := Sail.BitVec.addInt (Functions.sail_mask_signed 48 address) offset
  let physical ← (do
    if ← _root_.X86Registers.readReg .app_view then
      pure (Functions.sail_mask_signed 52 linear)
    else Functions.ia32e_la_to_pa linear access : SailM (BitVec 52))
  Functions.bang_memi physical
    ((Sail.BitVec.extractLsb value (Int.toNat (8 * offset + 7)) (Int.toNat (8 * offset))).setWidth 8)

theorem wb_fold [MemoryPrimitives] (count : Nat) (address : Word) (access : String)
    (value : BitVec (8 * count)) :
    Functions.wb count address access value =
      (List.range count).foldlM (fun initial (offset : Nat) =>
        byteStep count address access value (offset : Int) initial) () := by
  rw [← SailRange.forIn_foldlM]
  simp only [Functions.wb, byteStep, bind_assoc, pure_bind, SailRange.ite_bind, SailRange.ascending]
  exact discard_unit _

theorem extract_at_nat (count offset : Nat) (value : BitVec (8 * count)) :
    (Sail.BitVec.extractLsb value (Int.toNat (8 * (offset : Int) + 7))
      (Int.toNat (8 * (offset : Int)))).setWidth 8 = value.extractLsb' (8 * offset) 8 := by
  have low : Int.toNat (8 * (offset : Int)) = 8 * offset := by omega
  have width : Int.toNat (8 * (offset : Int) + 7) - Int.toNat (8 * (offset : Int)) + 1 = 8 := by omega
  unfold Sail.BitVec.extractLsb BitVec.extractLsb
  rw [width, low, BitVec.setWidth_eq]

theorem byteStep_exact (count offset : Nat) (within : offset < count)
    (state : State) (base : BitVec 48) (pointer : Word) (value : BitVec (8 * count)) (access : String)
    (upper : base.toInt + count ≤ (2 ^ 47 : Int))
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer) :
    (byteStep count (base.signExtend 64) access value (offset : Int) ()).run state =
      .ok () (putByte state ((X86Execution.address base.toInt offset).signExtend 52).toNat
        (value.extractLsb' (8 * offset) 8)) := by
  have lower : -(2 ^ 47 : Int) ≤ base.toInt := by simpa using BitVec.le_toInt base
  have lastSafe : base.toInt + (count - 1 : Nat) < (2 ^ 47 : Int) := by omega
  have canonical := X86Move.canonical48 state (X86Execution.address base.toInt offset)
  rw [X86Execution.address_toInt _ lower lastSafe _ (by omega)] at canonical
  unfold byteStep
  rw [BitVec.toInt_signExtend_of_le (by decide : 48 ≤ 64), run_bind, canonical]
  dsimp only
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  rw [X86ReadWords.add_offset, run_bind, run_bind, readRegister_exact, application]
  dsimp only
  rw [X86FetchMemory.widen_physical, if_pos rfl, run_pure]
  dsimp only
  rw [extract_at_nat]
  exact bang_memi_exact state pointer _ _ rip

theorem foldlM_statewise {α : Type} (items : List α) (body : α → SailM Unit)
    (step : State → α → State) (invariant : State → Prop)
    (fires : ∀ state, invariant state → ∀ item ∈ items,
      (body item).run state = .ok () (step state item))
    (preserves : ∀ state, invariant state → ∀ item ∈ items, invariant (step state item))
    (state : State) (valid : invariant state) :
    (items.foldlM (fun _ item => body item) ()).run state = .ok () (items.foldl step state) := by
  induction items generalizing state with
  | nil => rfl
  | cons head tail ih =>
    rw [List.foldlM_cons, run_bind, fires state valid head (by simp)]
    dsimp only
    exact ih
      (fun current currentValid item member => fires current currentValid item (by simp [member]))
      (fun current currentValid item member => preserves current currentValid item (by simp [member]))
      (step state head) (preserves state valid head (by simp))

def physicalAddress (base : BitVec 48) (offset : Nat) : Nat :=
  ((X86Execution.address base.toInt offset).signExtend 52).toNat

def storeBytes (count : Nat) (state : State) (base : BitVec 48) (value : BitVec (8 * count)) : State :=
  (List.range count).foldl (fun current offset => putByte current (physicalAddress base offset)
    (value.extractLsb' (8 * offset) 8)) state

theorem putByte_frame (state : State) (address : Nat) (value : BitVec 8) :
    X86StateFrame.Frame ∅ {address} state (putByte state address value) where
  registers _ _ := rfl
  memory other outside := by
    have different : address ≠ other := by
      intro same
      exact outside (Finset.mem_singleton.mpr same.symm)
    change (state.mem.insert address value)[other]? = state.mem[other]?
    simp only [Std.ExtHashMap.getElem?_insert, beq_eq_false_iff_ne.mpr different,
      Bool.false_eq_true, ite_false]
  choices := rfl
  tags := rfl
  cycles := rfl
  output := rfl

def written (base : BitVec 48) (offsets : List Nat) : Finset Nat :=
  (offsets.map (physicalAddress base)).toFinset

def storeList (count : Nat) (state : State) (base : BitVec 48) (value : BitVec (8 * count))
    (offsets : List Nat) : State :=
  offsets.foldl (fun current offset => putByte current (physicalAddress base offset)
    (value.extractLsb' (8 * offset) 8)) state

theorem storeList_frame (count : Nat) (offsets : List Nat) (state : State)
    (base : BitVec 48) (value : BitVec (8 * count)) :
    X86StateFrame.Frame ∅ (written base offsets) state (storeList count state base value offsets) := by
  induction offsets generalizing state with
  | nil => exact X86StateFrame.Frame.refl ∅ ∅ state
  | cons offset rest ih =>
    have first := putByte_frame state (physicalAddress base offset) (value.extractLsb' (8 * offset) 8)
    have second := ih (putByte state (physicalAddress base offset) (value.extractLsb' (8 * offset) 8))
    simpa only [storeList, List.foldl_cons, written, List.map_cons, List.toFinset_cons,
      Finset.empty_union, Finset.singleton_union] using first.trans second

theorem storeBytes_frame (count : Nat) (state : State) (base : BitVec 48) (value : BitVec (8 * count)) :
    X86StateFrame.Frame ∅ (written base (List.range count)) state (storeBytes count state base value) :=
  storeList_frame count (List.range count) state base value

theorem physicalAddress_injective (count : Nat) (base : BitVec 48)
    (upper : base.toInt + count ≤ (2 ^ 47 : Int))
    (left right : Nat) (leftWithin : left < count) (rightWithin : right < count)
    (same : physicalAddress base left = physicalAddress base right) : left = right := by
  have lower : -(2 ^ 47 : Int) ≤ base.toInt := by simpa using BitVec.le_toInt base
  have lastSafe : base.toInt + (count - 1 : Nat) < (2 ^ 47 : Int) := by omega
  have equalBits : (X86Execution.address base.toInt left).signExtend 52 =
      (X86Execution.address base.toInt right).signExtend 52 := BitVec.eq_of_toNat_eq same
  have equalIntegers := congrArg BitVec.toInt equalBits
  simp only [BitVec.toInt_signExtend_of_le (by decide : 48 ≤ 52)] at equalIntegers
  rw [X86Execution.address_toInt _ lower lastSafe left (by omega),
    X86Execution.address_toInt _ lower lastSafe right (by omega)] at equalIntegers
  omega

theorem store_word_byte (state : State) (base : BitVec 48) (value : Word)
    (upper : base.toInt + 8 ≤ (2 ^ 47 : Int)) (offset : Nat) (within : offset < 8) :
    (storeBytes 8 state base value).mem.get? (physicalAddress base offset) =
      some (value.extractLsb' (8 * offset) 8) := by
  have sameKey (left right : Nat) (leftWithin : left < 8) (rightWithin : right < 8) :
      physicalAddress base left = physicalAddress base right ↔ left = right :=
    ⟨physicalAddress_injective 8 base upper left right leftWithin rightWithin, by rintro rfl; rfl⟩
  interval_cases offset <;>
    simp [storeBytes, List.range_succ, putByte, Std.ExtHashMap.getElem_insert, sameKey]

theorem wb_exact (count : Nat) (state : State) (base : BitVec 48) (pointer : Word)
    (value : BitVec (8 * count)) (access : String)
    (upper : base.toInt + count ≤ (2 ^ 47 : Int))
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer) :
    (Functions.wb count (base.signExtend 64) access value).run state =
      .ok () (storeBytes count state base value) := by
  rw [wb_fold]
  change ((List.range count).foldlM (fun _ (offset : Nat) =>
    byteStep count (base.signExtend 64) access value (offset : Int) ()) ()).run state = _
  apply foldlM_statewise (List.range count) _ _ (fun current => current.regs = state.regs)
  · intro current unchanged offset member
    apply byteStep_exact count offset (List.mem_range.mp member) current base pointer value access upper
    · rw [unchanged]; exact application
    · rw [unchanged]; exact rip
  · intro current unchanged offset member
    exact unchanged
  · rfl

theorem store_word_uses_wb (state : State) (base : BitVec 48) (baseRegister : Option Nat)
    (attributes : Vector (BitVec 16) 6) (value : Word) (alignment memoryPointer : Bool)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (safe : alignment = false ∨ base &&& (7#48) = (0#48)) :
    (Functions.store_bytes_to_ea .Mode_64bit 8 8 (base.signExtend 64) baseRegister 3 value
      alignment memoryPointer).run state =
        (Functions.wb 8 (base.signExtend 64) ":W" value).run state := by
  unfold Functions.store_bytes_to_ea
  rw [run_bind, readRegister_exact, segments]
  dsimp only
  simp only [Functions.in_64bit_mode, Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false]
  simp only [pure_bind]
  rw [run_bind, X86ReadWords.data_linear_address]
  dsimp only
  rw [X86ReadWords.word_access_check base baseRegister ":W" alignment memoryPointer safe]
  rfl

theorem store_word_exact (state : State) (base : BitVec 48) (baseRegister : Option Nat)
    (attributes : Vector (BitVec 16) 6) (pointer value : Word) (alignment memoryPointer : Bool)
    (upper : base.toInt + 8 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (safe : alignment = false ∨ base &&& (7#48) = (0#48)) :
    (Functions.store_bytes_to_ea .Mode_64bit 8 8 (base.signExtend 64) baseRegister 3 value
      alignment memoryPointer).run state = .ok () (storeBytes 8 state base value) := by
  rw [store_word_uses_wb state base baseRegister attributes value alignment memoryPointer segments safe]
  exact wb_exact 8 state base pointer value ":W" upper application rip

theorem read_after_store (state : State) (base : BitVec 48) (pointer value : Word) (access : String)
    (upper : base.toInt + 8 ≤ (2 ^ 47 : Int))
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer) :
    (Functions.rb 8 (base.signExtend 64) access).run (storeBytes 8 state base value) =
      .ok value (storeBytes 8 state base value) := by
  have unchanged := (storeBytes_frame 8 state base value).registers_equal
  apply X86ReadWords.rb_word_exact (storeBytes 8 state base value) base pointer value access upper
  · rw [unchanged]; exact application
  · rw [unchanged]; exact rip
  · exact store_word_byte state base value upper

theorem store_word_unaligned (state : State) (base : BitVec 48) (baseRegister : Option Nat)
    (attributes : Vector (BitVec 16) 6) (value : Word) (memoryPointer : Bool)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (unaligned : base &&& (7#48) ≠ (0#48)) :
    (Functions.store_bytes_to_ea .Mode_64bit 8 8 (base.signExtend 64) baseRegister 3 value true memoryPointer).run state =
      .error (.User (.Emsg "Fault: :UNALIGNED-LINEAR-ADDRESS")) state := by
  unfold Functions.store_bytes_to_ea
  rw [run_bind, readRegister_exact, segments]
  dsimp only
  simp only [Functions.in_64bit_mode, Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false, pure_bind]
  rw [run_bind, X86ReadWords.data_linear_address]
  dsimp only
  unfold Functions.check_linear_memory_access
  rw [X86ReadWords.truncate48, X86ReadWords.word_alignment]
  have unequal : ((base &&& (7#48)) == (0#48)) = false := by simpa only [beq_eq_false_iff_ne] using unaligned
  simp only [pure_bind, unequal, Bool.not_true, Bool.false_or, Bool.not_false, ite_true]
  rfl

namespace Controls

private def attributes : Vector (BitVec 16) 6 := Vector.replicate 6 (0#16)
private def value : Word := 0x123456789abcdef0#64
private def base : BitVec 48 := 0x1000#48

private def before : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .app_view true
  let registers := registers.insert .rip (0x2000#64)
  let registers := registers.insert .seg_hidden_attrs attributes
  let memory := (∅ : Std.ExtHashMap Nat (BitVec 8)).insert 4104 (42#8)
  let memory := memory.insert 8192 (0x90#8)
  let memory := memory.insert 8193 (0xc3#8)
  let memory := (List.range 8).foldl (fun memory index => memory.insert (4096 + index) (0xaa#8)) memory
  ⟨registers, (), memory, (), 0, #[]⟩

private def after : State := storeBytes 8 before base value

theorem word_store_executes :
    (Functions.store_bytes_to_ea .Mode_64bit 8 8 (0x1000#64) none 3 value true false).run before = .ok () after := by
  exact store_word_exact before base none attributes (0x2000#64) value true false (by decide)
    (by simp [before]) (by simp [before, Std.ExtDHashMap.get?_insert])
    (by simp [before, Std.ExtDHashMap.get?_insert]) (Or.inr (by decide))

theorem round_trip :
    (do Functions.store_bytes_to_ea .Mode_64bit 8 8 (0x1000#64) none 3 value true false
        Functions.rb 8 (0x1000#64) ":R").run before = .ok value after := by
  rw [run_bind, word_store_executes]
  exact read_after_store before base (0x2000#64) value ":R" (by decide)
    (by simp [before, Std.ExtDHashMap.get?_insert]) (by simp [before, Std.ExtDHashMap.get?_insert])

theorem wrong_readback_refused :
    (do Functions.store_bytes_to_ea .Mode_64bit 8 8 (0x1000#64) none 3 value true false
        Functions.rb 8 (0x1000#64) ":R").run before ≠ .ok (0#64) after := by
  rw [round_trip]
  intro wrong
  exact (by decide : value ≠ (0#64)) (EStateM.Result.ok.inj wrong).1

theorem suffix_preserved : after.mem.get? 4104 = some (42#8) := by
  have frame := storeBytes_frame 8 before base value
  change (storeBytes 8 before base value).mem.get? 4104 = some (42#8)
  rw [frame.memory 4104 (by decide)]
  simp [before, List.range_succ, Std.ExtHashMap.getElem_insert]

theorem code_preserved : X86Execution.codeLoaded after 8192 [144, 195] := by
  have frame := storeBytes_frame 8 before base value
  apply frame.codeLoaded 8192 [144, 195]
  · intro index byte present
    have within : index < 2 := (List.getElem?_eq_some_iff.mp present).choose
    interval_cases index <;> simp_all [before, List.range_succ, X86Execution.address,
      Std.ExtHashMap.getElem_insert]
  · intro index byte present
    have within : index < 2 := (List.getElem?_eq_some_iff.mp present).choose
    interval_cases index <;> decide

theorem omitted_write_footprint_refused : ¬X86StateFrame.Frame ∅ ∅ before after := by
  intro frame
  have unchanged := frame.memory 4096 (by simp)
  have stored := store_word_byte before base value (by decide) 0 (by decide)
  change after.mem.get? 4096 = some (0xf0#8) at stored
  have previous : before.mem.get? 4096 = some (0xaa#8) := by
    simp [before, List.range_succ, Std.ExtHashMap.getElem_insert]
  rw [stored, previous] at unchanged
  cases unchanged

theorem unaligned_store_refused :
    (Functions.store_bytes_to_ea .Mode_64bit 8 8 (0x1001#64) none 3 value true false).run before =
      .error (.User (.Emsg "Fault: :UNALIGNED-LINEAR-ADDRESS")) before :=
  store_word_unaligned before (0x1001#48) none attributes value false (by simp [before]) (by decide)

end Controls
end Mettapedia.Machines.TIsa.X86WriteWords

#print axioms Mettapedia.Machines.TIsa.X86WriteWords.byteStep_exact
#print axioms Mettapedia.Machines.TIsa.X86WriteWords.wb_exact
#print axioms Mettapedia.Machines.TIsa.X86WriteWords.store_word_exact
#print axioms Mettapedia.Machines.TIsa.X86WriteWords.Controls.round_trip
#print axioms Mettapedia.Machines.TIsa.X86WriteWords.Controls.omitted_write_footprint_refused
#print axioms Mettapedia.Machines.TIsa.X86WriteWords.Controls.unaligned_store_refused
