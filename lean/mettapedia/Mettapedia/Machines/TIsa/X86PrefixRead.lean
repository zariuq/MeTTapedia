import Mettapedia.Machines.TIsa.X86EffectiveFetch

/-!
# Reading a REX prefix and MOV opcode in the pinned Sail scanner

These lemmas connect initialized code bytes to the actual recursive scanner.
The REX classification covers both word widths and every physical register
pair. Pointer advancement requires the signed canonical-address bounds.
The concrete controls check the returned REX byte and a truncated code image.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86PrefixRead

open _root_.X86Registers X86RegisterRefinement X86Prefix X86EffectiveFetch

local instance : MemoryPrimitives := X86Memory.ordinary

theorem code_address_size : Functions.select_address_size .Mode_64bit (some (0#52)) =
    (pure 8 : SailM Int) := rfl

theorem add_pointer_checked (state : State) (address delta next : BitVec 48)
    (sum : address.toInt + delta.toInt = next.toInt) :
    (Functions.add_to_iptr .Mode_64bit address delta).run state = .ok next state := by
  have canonical : (Functions.canonical_address_p (next.signExtend 49).toInt).run state =
      .ok true state := by
    simpa only [BitVec.toInt_signExtend_of_le (by decide : 48 ≤ 49)] using
      X86Move.canonical48 state next
  unfold Functions.add_to_iptr
  simp only [Functions.in_64bit_mode, ite_true]
  rw [sum, X86Move.bits_of_int49, run_bind, canonical]
  change (pure (Sail.BitVec.truncate (next.signExtend 49) 48) : SailM (BitVec 48)).run state = _
  rw [X86Move.truncate_pointer49]
  rfl

theorem add_pointer_small (state : State) (address : Int) (offset : Nat)
    (lower : -(2 ^ 47 : Int) ≤ address) (upper : address + offset < (2 ^ 47 : Int))
    (small : offset < 2 ^ 47) :
    (Functions.add_to_iptr .Mode_64bit (BitVec.ofInt 48 address) (BitVec.ofNat 48 offset)).run state =
      .ok (BitVec.ofInt 48 (address + offset)) state := by
  apply add_pointer_checked
  have start : (BitVec.ofInt 48 address).toInt = address :=
    BitVec.toInt_ofInt_eq_self (by decide) lower (by omega)
  have finish : (BitVec.ofInt 48 (address + offset)).toInt = address + offset :=
    BitVec.toInt_ofInt_eq_self (by decide) (by omega) upper
  have delta : (BitVec.ofNat 48 offset).toInt = (offset : Int) := by
    have same : BitVec.ofNat 48 offset = BitVec.ofInt 48 (offset : Int) := by simp
    rw [same]
    apply BitVec.toInt_ofInt_eq_self (by decide)
    · omega
    · exact_mod_cast small
  rw [start, delta, finish]

theorem opcode_stops_scan (state : State) (address : BitVec 48) (pointer : Word)
    (attributes : Vector (BitVec 16) 6) (rex : BitVec 8) (count : Nat)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (present : state.mem.get? (address.signExtend 52).toNat = some (0x89#8)) :
    (Functions.get_prefixes .Mode_64bit address (0#52) rex (count + 1)).run state =
      .ok (Functions._update_prefixes_num (Functions._update_prefixes_nxt (0#52) (0x89#8))
        (Functions.bits_of_int (15 - ((count + 1 : Nat) : Int)) 4), rex) state := by
  rw [unfold_original]
  unfold Functions.get_prefixes_body
  rw [code_address_size]
  change (do
    let byte ← Functions.rme08 .Mode_64bit 8 (address.signExtend 64) none 1 ":X"
    _ : SailM (BitVec 52 × BitVec 8)).run state = _
  rw [run_bind, effective_read_exact state address pointer attributes (0x89#8)
    segments application rip present]
  rfl

theorem rex_group (wide : Bool) (source destination : Fin 16) :
    Functions.get_one_byte_prefix_array_code (X86RegisterEncoding.rex wide source destination) = 0 := by
  revert wide source destination
  decide

theorem rex_nibble (wide : Bool) (source destination : Fin 16) :
    Functions.bits_of_int
      (Functions.ash_int (Sail.BitVec.toNatInt (X86RegisterEncoding.rex wide source destination)) (-4)) 4 =
        (0x4#4) := by
  revert wide source destination
  decide

theorem check_range_ok (lower upper value : Int) (above : lower ≤ value) (below : value ≤ upper) :
    Functions.check_range lower upper value = (pure value : SailM Int) := by
  unfold Functions.check_range
  have accepted : ((lower ≤b value) && (value ≤b upper)) = true := by simp [above, below]
  rw [accepted]
  rfl

theorem rex_advances_scan (state : State) (address next : BitVec 48) (pointer : Word)
    (attributes : Vector (BitVec 16) 6) (wide : Bool) (source destination : Fin 16)
    (before : BitVec 8) (remaining : Nat)
    (sum : address.toInt + 1 = next.toInt)
    (positive : 0 < remaining) (bounded : remaining < 15)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (present : state.mem.get? (address.signExtend 52).toNat =
      some (X86RegisterEncoding.rex wide source destination)) :
    (Functions.get_prefixes .Mode_64bit address (0#52) before (remaining + 1)).run state =
      (Functions.get_prefixes .Mode_64bit next (0#52)
        (X86RegisterEncoding.rex wide source destination) remaining).run state := by
  rw [unfold_original]
  unfold Functions.get_prefixes_body
  rw [code_address_size]
  change (do
    let byte ← Functions.rme08 .Mode_64bit 8 (address.signExtend 64) none 1 ":X"
    _ : SailM (BitVec 52 × BitVec 8)).run state = _
  rw [run_bind, effective_read_exact state address pointer attributes
    (X86RegisterEncoding.rex wide source destination) segments application rip present]
  dsimp only
  simp only [Functions.is_ext_prefix_byte, Bool.false_eq_true, ite_false, rex_group, rex_nibble,
    Functions.in_64bit_mode, Bool.true_and, beq_self_eq_true, ite_true]
  rw [run_bind, add_pointer_checked state address (1#48) next (by simpa using sum)]
  dsimp only
  have previous : ((remaining + 1 : Nat) : Int) - 1 = remaining := by omega
  rw [previous, check_range_ok 0 15 (remaining : Int) (by omega) (by omega)]
  rfl

theorem rex_then_opcode (state : State) (address next : BitVec 48) (pointer : Word)
    (attributes : Vector (BitVec 16) 6) (wide : Bool) (source destination : Fin 16)
    (before : BitVec 8) (sum : address.toInt + 1 = next.toInt)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (prefixByte : state.mem.get? (address.signExtend 52).toNat =
      some (X86RegisterEncoding.rex wide source destination))
    (opcodeByte : state.mem.get? (next.signExtend 52).toNat = some (0x89#8)) :
    (Functions.get_prefixes .Mode_64bit address (0#52) before 15).run state =
      .ok (Functions._update_prefixes_num (Functions._update_prefixes_nxt (0#52) (0x89#8))
        (1#4), X86RegisterEncoding.rex wide source destination) state := by
  rw [rex_advances_scan state address next pointer attributes wide source destination before 14 sum
    (by decide) (by decide) segments application rip prefixByte]
  exact opcode_stops_scan state next pointer attributes
    (X86RegisterEncoding.rex wide source destination) 13 segments application rip opcodeByte

theorem scan_missing_opcode (state : State) (address : BitVec 48)
    (attributes : Vector (BitVec 16) 6) (rex : BitVec 8) (count : Nat)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (missing : state.mem.get? (address.signExtend 52).toNat = none) :
    (Functions.get_prefixes .Mode_64bit address (0#52) rex (count + 1)).run state =
      .error (.OutOfMemoryRange (address.signExtend 52).toNat) state := by
  rw [unfold_original]
  unfold Functions.get_prefixes_body
  rw [code_address_size]
  change (do
    let byte ← Functions.rme08 .Mode_64bit 8 (address.signExtend 64) none 1 ":X"
    _ : SailM (BitVec 52 × BitVec 8)).run state = _
  rw [run_bind, effective_read_missing state address attributes segments application missing]

namespace Controls

private def attributes : Vector (BitVec 16) 6 := Vector.replicate 6 (0#16)
private def mapped : State :=
  ⟨(((∅ : Std.ExtDHashMap Register RegisterType).insert .app_view true).insert .rip (0x1000#64)).insert
      .seg_hidden_attrs attributes,
    (), ((∅ : Std.ExtHashMap Nat (BitVec 8)).insert 4096 (0x48#8)).insert 4097 (0x89#8), (), 0, #[]⟩

private def packetPrefix : BitVec 52 := Functions._update_prefixes_num
  (Functions._update_prefixes_nxt (0#52) (0x89#8)) (1#4)

theorem read_packet : (Functions.get_prefixes .Mode_64bit (0x1000#48) (0#52) (0#8) 15).run mapped =
    .ok (packetPrefix, 0x48#8) mapped := by
  apply rex_then_opcode mapped (0x1000#48) (0x1001#48) (0x1000#64) attributes true 0 1 (0#8)
  · decide
  · simp [mapped]
  · simp [mapped, Std.ExtDHashMap.get?_insert]
  · simp [mapped, Std.ExtDHashMap.get?_insert]
  · simp [mapped, Std.ExtHashMap.getElem_insert, X86RegisterEncoding.rex]
  · simp [mapped]

theorem wrong_rex_refused :
    (Functions.get_prefixes .Mode_64bit (0x1000#48) (0#52) (0#8) 15).run mapped ≠
      .ok (packetPrefix, 0x49#8) mapped := by
  rw [read_packet]
  intro wrong
  have bytes := congrArg Prod.snd (EStateM.Result.ok.inj wrong).1
  exact (by decide : (0x48#8) ≠ (0x49#8)) bytes

private def truncated : State :=
  { mapped with mem := (∅ : Std.ExtHashMap Nat (BitVec 8)).insert 4096 (0x48#8) }

theorem missing_opcode :
    (Functions.get_prefixes .Mode_64bit (0x1000#48) (0#52) (0#8) 15).run truncated =
      .error (.OutOfMemoryRange 4097) truncated := by
  rw [rex_advances_scan truncated (0x1000#48) (0x1001#48) (0x1000#64) attributes true 0 1 (0#8) 14
    (by decide) (by decide) (by decide) (by simp [truncated, mapped])
    (by simp [truncated, mapped, Std.ExtDHashMap.get?_insert])
    (by simp [truncated, mapped, Std.ExtDHashMap.get?_insert])
    (by simp [truncated, X86RegisterEncoding.rex])]
  apply scan_missing_opcode truncated (0x1001#48) attributes (0x48#8) 13
  · simp [truncated, mapped]
  · simp [truncated, mapped, Std.ExtDHashMap.get?_insert]
  · simp [truncated]

end Controls


end Mettapedia.Machines.TIsa.X86PrefixRead
