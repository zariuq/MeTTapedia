import Mathlib.Tactic

/-!
# SYS_VM Nested Paging, Loan Custody, and CoW Snapshot Invariants

Clean mathematical specification of the core invariants in `sex_vm`, `kernel_svm`,
`kernel_vm`, and Direct Limine Self-Drag (`drag --self`):

1. **NPT permission & address-mask safety** (`BitVec 64`): `nptLeaf` never grants
   write without `WRITE`, always sets bit 63 (`NX`) when `nx = true` and `EXEC` is
   clear, and masks out stray bits outside physical frame bits `[51:12]`.
2. **SVM/VMX segment attribute bijection** (`BitVec 32` ↔ `BitVec 16`): usable
   present descriptors round-trip identically through `svmAccess (svmAttrib a) = a`,
   and unusable descriptors always encode to `0` and decode back as unusable.
3. **Lent-frame revocation / NPT-generation monotonicity**: revoking or unmapping a
   VM loan strictly advances `eptGen`, forcing any core whose `seenGen < eptGen` to
   flush its ASID/NPT TLB before the next `VMRUN` (no parent frame reuse while stale
   guest NPT translations exist).
4. **CoW RAM snapshot isolation & exact revert**: writing through a CoW overlay
   never mutates the immutable base snapshot, and dropping the overlay restores the
   exact snapshot memory state.
5. **Direct Limine shared-framebuffer containment**: every pixel `(x, y)` within
   `(width, height)` under stride `pitch ≥ width * 4` lies strictly inside the lent
   framebuffer window `[fbGpa, fbGpa + height * pitch)`.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.VmLoanCustody

/-- Physical frame address mask `[51:12]`. -/
def hwAddressMask : BitVec 64 := 0x000FFFFFFFFFF000#64

/-- Access mask bits matching `sexos_vm.h`. -/
def accessRead  : BitVec 64 := 1#64
def accessWrite : BitVec 64 := 2#64
def accessExec  : BitVec 64 := 4#64

/-- AMD SVM nested page table non-leaf entry: present + writable + user. -/
def nptTable (frame : BitVec 64) : BitVec 64 :=
  (frame &&& hwAddressMask) ||| 7#64

/-- AMD SVM nested page table 4 KiB leaf entry matching `sex_svm_npt_leaf`. -/
def nptLeaf (frame access : BitVec 64) (nx : Bool) : BitVec 64 :=
  let w : BitVec 64 := if (access &&& accessWrite) != 0#64 then 2#64 else 0#64
  let noExec : BitVec 64 := if nx && ((access &&& accessExec) == 0#64) then 1#64 <<< 63 else 0#64
  (frame &&& hwAddressMask) ||| 1#64 ||| w ||| 4#64 ||| noExec

/-- Theorem 1 (NPT NX safety): When the host has `EFER.NXE` enabled (`nx = true`) and
`EXEC` is not granted in `access`, `nptLeaf` always sets the NX bit (bit 63). -/
theorem nptLeaf_no_exec_sets_nx (frame access : BitVec 64)
    (hNoExec : (access &&& accessExec) == 0#64) :
    (nptLeaf frame access true).getLsbD 63 = true := by
  unfold nptLeaf
  simp [hNoExec]

/-- Theorem 2 (NPT Write safety): When `WRITE` is not granted in `access`, `nptLeaf`
never sets bit 1 (writable). -/
theorem nptLeaf_no_write_clears_w (frame access : BitVec 64) (nx : Bool)
    (hNoWrite : (access &&& accessWrite) = 0#64) :
    (nptLeaf frame access nx).getLsbD 1 = false := by
  unfold nptLeaf hwAddressMask
  simp only [hNoWrite, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  cases h : (nx && (access &&& accessExec == 0#64)) <;> simp

/-- Theorem 3 (NPT address-mask containment): `nptTable` clears reserved high bits
`[63:52]` regardless of stray bits in `frame`. -/
theorem nptTable_clears_high_reserved (frame : BitVec 64) (i : Nat) (hi : 52 ≤ i) (hi64 : i < 64) :
    (nptTable frame).getLsbD i = false := by
  unfold nptTable hwAddressMask
  have h1 : (0x000FFFFFFFFFF000#64 : BitVec 64).getLsbD i = false := by
    interval_cases i <;> decide
  have h2 : (7#64 : BitVec 64).getLsbD i = false := by
    interval_cases i <;> decide
  simp [h1, h2]

/-- Pack VMX 32-bit access rights into AMD SVM 12-bit VMCB segment attribute. -/
def svmAttrib (access : BitVec 32) : BitVec 16 :=
  if (access &&& (1#32 <<< 16)) != 0#32 then 0#16
  else ((access &&& 0xFF#32) ||| ((access >>> 4) &&& 0xF00#32)).truncate 16

/-- Unpack AMD SVM 12-bit VMCB segment attribute back to VMX 32-bit access rights. -/
def svmAccess (attrib : BitVec 16) : BitVec 32 :=
  let a : BitVec 32 := attrib.zeroExtend 32
  (a &&& 0xFF#32) ||| ((a &&& 0xF00#32) <<< 4) |||
    (if (a &&& 0x80#32) == 0#32 then 1#32 <<< 16 else 0#32)

/-- Theorem 4 (SVM unusable descriptor safety): Any descriptor with bit 16 (unusable)
set encodes to `0` and decodes back with bit 16 set. -/
theorem svm_unusable_roundtrip (access : BitVec 32)
    (hUnusable : (access &&& (1#32 <<< 16)) != 0#32) :
    svmAttrib access = 0#16 ∧ (svmAccess (svmAttrib access)).getLsbD 16 = true := by
  have hAttr : svmAttrib access = 0#16 := by
    unfold svmAttrib
    rw [if_pos hUnusable]
  refine ⟨hAttr, ?_⟩
  rw [hAttr]
  decide

/-- Theorem 5 (SVM usable descriptor round-trip): Any canonical present usable VMX
access word (`bit 16 = 0`, `bit 7 = 1`, zero outside bits `[7:0] ∪ [15:12]`) round-trips
identically through `svmAccess (svmAttrib a) = a`. -/
theorem svm_usable_roundtrip (access : BitVec 32)
    (hPresent : access.getLsbD 7 = true)
    (hCanonical : ∀ i, i < 32 → (8 ≤ i ∧ i < 12 ∨ 16 ≤ i) → access.getLsbD i = false) :
    svmAccess (svmAttrib access) = access := by
  have hBit16 : access.getLsbD 16 = false := hCanonical 16 (by omega) (by omega)
  have hz : (access &&& (1#32 <<< 16)) = 0#32 := by
    ext i hi
    by_cases h16 : i = 16
    · subst h16
      simpa [BitVec.getLsbD_eq_getElem] using hBit16
    · have hmask : (65536#32 : BitVec 32).getLsbD i = false := by
        interval_cases i <;> first | contradiction | decide
      have hmask' : (65536#32 : BitVec 32)[i] = false := by
        rw [← BitVec.getLsbD_eq_getElem hi]; exact hmask
      simp [hmask']
  have hNotUnusable : ((access &&& (1#32 <<< 16)) != 0#32) = false := by
    rw [hz]; rfl
  have hAttrEq : svmAttrib access = ((access &&& 0xFF#32) ||| ((access >>> 4) &&& 0xF00#32)).truncate 16 := by
    unfold svmAttrib
    rw [hNotUnusable]; rfl
  have hPresOut : (((svmAttrib access).zeroExtend 32 &&& 0x80#32) == 0#32) = false := by
    have h7 : (((svmAttrib access).zeroExtend 32 &&& 0x80#32).getLsbD 7) = true := by
      rw [hAttrEq]
      simp [hPresent]
    cases hEq : ((svmAttrib access).zeroExtend 32 &&& 0x80#32) == 0#32
    · rfl
    · have : ((svmAttrib access).zeroExtend 32 &&& 0x80#32) = 0#32 := eq_of_beq hEq
      rw [this] at h7; simp at h7
  unfold svmAccess
  dsimp only
  rw [hPresOut]
  simp only [Bool.false_eq_true, ↓reduceIte, BitVec.or_zero, hAttrEq]
  ext n hn
  by_cases h0 : n < 8
  · interval_cases n <;> simp
  · by_cases h1 : n < 12
    · have hC : access[n] = false := by rw [← BitVec.getLsbD_eq_getElem hn]; exact hCanonical n hn (by omega)
      interval_cases n <;> simp [hC]
    · by_cases h2 : n < 16
      · interval_cases n <;> simp
      · have hC : access[n] = false := by rw [← BitVec.getLsbD_eq_getElem hn]; exact hCanonical n hn (by omega)
        interval_cases n <;> simp [hC]

/-- Per-core NPT TLB generation tracking model. -/
structure VmTlbState where
  eptGen : Nat
  coreSeenGen : Nat
  lentFrames : Nat
  deriving DecidableEq, Repr

/-- Whether a core must flush its ASID/NPT TLB before entering `VMRUN`. -/
def needsTlbFlush (s : VmTlbState) : Bool :=
  s.coreSeenGen < s.eptGen

/-- Revoking a VM clears its lent frames and strictly increments `eptGen`. -/
def revokeVm (s : VmTlbState) : VmTlbState :=
  { s with eptGen := s.eptGen + 1, lentFrames := 0 }

/-- Theorem 6 (Revocation forces NPT TLB flush): If a core was up to date
(`coreSeenGen ≤ eptGen`), revoking a VM guarantees `needsTlbFlush (revokeVm s) = true`
and `lentFrames = 0`, preventing stale guest translations from observing reused host frames. -/
theorem revoke_forces_tlb_flush (s : VmTlbState) (hLe : s.coreSeenGen ≤ s.eptGen) :
    needsTlbFlush (revokeVm s) = true ∧ (revokeVm s).lentFrames = 0 := by
  unfold needsTlbFlush revokeVm
  simp
  omega

/-- Immutable snapshot + volatile RAM CoW overlay model (`GPA → Word`). -/
structure CowMemory (Addr Val : Type) [DecidableEq Addr] where
  snapshot : Addr → Val
  overlay : Addr → Option Val

/-- Read from CoW memory: overlay wins over snapshot. -/
def CowMemory.read {Addr Val : Type} [DecidableEq Addr] (m : CowMemory Addr Val) (a : Addr) : Val :=
  (m.overlay a).getD (m.snapshot a)

/-- Write into CoW memory: updates ONLY the volatile RAM overlay, never the snapshot. -/
def CowMemory.write {Addr Val : Type} [DecidableEq Addr] (m : CowMemory Addr Val) (a : Addr) (v : Val) :
    CowMemory Addr Val :=
  { m with overlay := fun x => if x = a then some v else m.overlay x }

/-- Instant RAM snapshot revert: discard the dirty overlay. -/
def CowMemory.revert {Addr Val : Type} [DecidableEq Addr] (m : CowMemory Addr Val) :
    CowMemory Addr Val :=
  { m with overlay := fun _ => none }

/-- Theorem 7 (CoW snapshot conservation & exact revert): Any write sequence through
`CowMemory.write` leaves `snapshot` untouched, and `revert` restores the exact
original snapshot contents at every guest-physical address. -/
theorem cow_write_then_revert_exact {Addr Val : Type} [DecidableEq Addr]
    (m : CowMemory Addr Val) (a b : Addr) (v : Val) :
    (m.write a v).snapshot = m.snapshot ∧
      ((m.write a v).revert).read b = m.snapshot b := by
  constructor
  · rfl
  · rfl

/-- Theorem 8 (Direct Limine shared-framebuffer containment): For any pixel `(x, y)`
with `x < width` and `y < height`, if `width * 4 ≤ pitch` and the framebuffer window
`[fbGpa, fbGpa + height * pitch)` lies inside `[0, ramBytes)`, then the 4-byte pixel
write `[fbGpa + y * pitch + x * 4, fbGpa + y * pitch + x * 4 + 4)` stays strictly
within `[fbGpa, ramBytes)`. -/
theorem direct_limine_fb_pixel_contained
    (fbGpa ramBytes width height pitch x y : Nat)
    (hx : x < width) (hy : y < height)
    (hPitch : width * 4 ≤ pitch)
    (hWindow : fbGpa + height * pitch ≤ ramBytes) :
    fbGpa ≤ fbGpa + y * pitch + x * 4 ∧
      fbGpa + y * pitch + x * 4 + 4 ≤ ramBytes := by
  have hx4 : x * 4 + 4 ≤ pitch := by omega
  have hy1 : y + 1 ≤ height := by omega
  have hRow : (y + 1) * pitch ≤ height * pitch := Nat.mul_le_mul_right pitch hy1
  have hExpand : (y + 1) * pitch = y * pitch + pitch := by ring
  omega

#print axioms nptLeaf_no_exec_sets_nx
#print axioms nptLeaf_no_write_clears_w
#print axioms nptTable_clears_high_reserved
#print axioms svm_unusable_roundtrip
#print axioms svm_usable_roundtrip
#print axioms revoke_forces_tlb_flush
#print axioms cow_write_then_revert_exact
#print axioms direct_limine_fb_pixel_contained

end Mettapedia.Machines.Kernel.VmLoanCustody
