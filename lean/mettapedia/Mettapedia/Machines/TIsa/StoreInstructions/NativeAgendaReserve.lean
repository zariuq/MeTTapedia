import Mettapedia.Machines.TIsa.StoreInstructions.NativeSpanPrepare
import Mettapedia.Machines.TIsa.X86PlacedArithmetic

/-!
# Reserving the whole agenda extension before decomposition

The mutable live count and the physical capacity are separate
resident words. The guard compares the number requested with
capacity minus live count. It does not add an untrusted width
to an ordinal, and it does not publish a partially added agenda.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaReserve

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads)
open X86PlacedScalar (Code CompareBranch registerCode)
open NativeAgendaRead (fieldSource)
open NativeWords (Wiring)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def baseCode : List ℕ := registerCode 0x89 5 2
def liveCode : List ℕ := X86DataLoad.code true 9 2 0
def limitCode : List ℕ := X86DataLoad.code true 10 2 16
def freeCode : List ℕ := registerCode (X86Arithmetic.opcode .sub) 9 10

def emit (start exhausted : ℕ) : List ℕ :=
  baseCode ++ (liveCode ++ (limitCode ++
    (freeCode ++ NativeDecisions.compareBytes .lessEqualUnsigned 8 10 (start + 20) exhausted)))

theorem emit_size (start exhausted : ℕ) : (emit start exhausted).length = 29 := rfl

structure Placed (image : NativeImage.View) (start exhausted : ℕ) : Prop where
  extent : start + 29 ≤ image.size
  base : Code image start baseCode
  live : Code image (start + 3) liveCode
  limit : Code image (start + 10) limitCode
  free : Code image (start + 17) freeCode
  check : CompareBranch image (start + 20) exhausted .lessEqualUnsigned 8 10

theorem placed_of_emitted (image : NativeImage.View) (start exhausted : ℕ)
    (space : start + 29 ≤ image.size) (ends : exhausted ≤ image.size) (short : image.size < 2 ^ 31)
    (stored : Code image start (emit start exhausted)) : Placed image start exhausted := by
  obtain ⟨base, tail⟩ := NativeWords.code_append (show Code image start (baseCode ++ _) from stored)
  obtain ⟨live, tail⟩ := NativeWords.code_append tail
  obtain ⟨limit, tail⟩ := NativeWords.code_append tail
  obtain ⟨free, compare⟩ := NativeWords.code_append tail
  exact ⟨space, base, live, limit, free,
    NativeDecisions.compare_placed image _ _ _ _ _ (by omega) ends short compare⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers

abbrev clobbers : Finset Register := {.rdx, .r9, .r10, .rflags, .rip}

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

def liveWire : Wiring := ⟨2, by decide, by decide, MemoryBinding.storeEncoding, 9, by decide, by decide⟩
def limitWire : Wiring := ⟨2, by decide, by decide, MemoryBinding.storeEncoding, 10, by decide, by decide⟩

variable {capacity : ℕ} {layout : NativeAgendaRecords.Layout capacity}
variable {arena : PackedEquations.Arena}

theorem capacity_word (layout : NativeAgendaRecords.Layout capacity) :
    (BitVec.ofNat 64 capacity).toNat = capacity := by
  have limit := layout.words.positive_room (show 0 < 3 * (capacity + 1) by omega)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem free_exact {before : Native} (ready : NativeAgendaRecords.Ready layout arena before) :
    (BitVec.ofNat 64 capacity - BitVec.ofNat 64 arena.size).toNat = capacity - arena.size := by
  have below : BitVec.ofNat 64 arena.size ≤ BitVec.ofNat 64 capacity := by
    rw [BitVec.le_def, ready.count_word, capacity_word layout]
    exact ready.fits
  rw [BitVec.toNat_sub_of_le below, capacity_word layout, ready.count_word]

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start exhausted : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (placed : Placed image start exhausted)
    (ready : NativeAgendaRecords.Ready layout arena before) (pointer : lookup before 5 = some layout.words.pointer)
    (limit : Reads before (layout.metadata.cell 2).address (BitVec.ofNat 64 capacity))
    (requested : Word) (width : lookup before 8 = some requested) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 6).run before = .ok () after ∧
      X86StateFrame.Frame clobbers ∅ before after ∧
      lookup after 9 = some (BitVec.ofNat 64 arena.size) ∧
      lookup after 10 = some (BitVec.ofNat 64 (capacity - arena.size)) ∧
      Nonempty (At image after base
        (if arena.size + requested.toNat ≤ capacity then start + 29 else exhausted)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := placed.extent
  have noHandlerChange : NativeWords.handlers (handlers other extra) = handlers other extra := rfl
  have arithmeticHandler : X86Arithmetic.linkedHandlers (handlers other extra) = handlers other extra := rfl
  have headerBase : layout.metadata.pointer = layout.words.pointer := BitVec.add_zero _
  obtain ⟨a, opened, openFrame, known, ⟨atLive⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector point (by omega) 5 2 layout.words.pointer pointer placed.base
  have first := X86StateFrame.registerOnly openFrame
  obtain ⟨b, liveRead, liveFrame, used, ⟨atLimit⟩⟩ := (fieldSource layout.header 0).fetch
    (handlers other extra) vector liveWire (BitVec.ofNat 64 arena.size) atLive (controls.transport first (by decide))
    (layout.header_pointer.symm ▸ known) (ready.count.preserved first (by simp))
    (show start + 10 ≤ image.size by omega) placed.live
  have throughLive := first.trans liveFrame
  obtain ⟨c, limitRead, limitFrame, cap, ⟨atDiff⟩⟩ := (fieldSource layout.metadata 2).fetch
    (handlers other extra) vector limitWire (BitVec.ofNat 64 capacity) (show At image b base (start + 10) from atLimit)
    (controls.transport throughLive (by decide)) (headerBase.symm ▸ (liveFrame.lookup 2 (by decide)).trans known)
    (limit.preserved throughLive (by simp)) (show start + 17 ≤ image.size by omega) placed.limit
  rw [noHandlerChange] at liveRead limitRead
  obtain ⟨d, subtracted, subFrame, free, ⟨atCheck⟩⟩ := X86PlacedArithmetic.executes
    (handlers other extra) vector (show At image c base (start + 17) from atDiff) (by omega)
    .sub 9 10 _ _ ((limitFrame.lookup 9 (by decide)).trans used) cap placed.free
  rw [arithmeticHandler] at subtracted
  have beforeCheck := ((throughLive.trans limitFrame).trans (X86StateFrame.registerOnly subFrame))
  let available := BitVec.ofNat 64 capacity - BitVec.ofNat 64 arena.size
  have checkedSpace : available.toNat = capacity - arena.size := free_exact ready
  have roomWord : available = BitVec.ofNat 64 (capacity - arena.size) := by
    have repr : BitVec.ofNat 64 available.toNat = available := by simp
    rw [← checkedSpace]
    exact repr.symm
  have knownFree : lookup d 10 = some available := free
  obtain ⟨after, compared, checked, ⟨endpoint⟩⟩ := X86PlacedScalar.compare_branch
    (X86PlacedFrameAddress.nativeBase other) extra vector (show At image d base (start + 20) from atCheck)
    .lessEqualUnsigned 8 10 placed.check requested available ((beforeCheck.lookup 8 (by decide)).trans width) knownFree
  change At image after base (if decide (requested.toNat ≤ available.toNat) then start + 20 + 9
    else exhausted) at endpoint
  rw [checkedSpace] at endpoint
  have within : requested.toNat ≤ capacity - arena.size ↔ arena.size + requested.toNat ≤ capacity := by
    have fit := ready.fits
    omega
  simp only [within, decide_eq_true_eq] at endpoint
  have trace := X86FuelPrefix.fetches_then 2 1 before b c
    (X86FuelPrefix.fetches_then 1 1 before a b opened liveRead) limitRead
  exact ⟨after, X86FuelPrefix.fetches_then 4 2 before d after
    (X86FuelPrefix.fetches_then 3 1 before c d trace subtracted) compared,
    (beforeCheck.trans (X86StateFrame.registerOnly checked)).mono (by decide) (by simp),
    (((limitFrame.trans (X86StateFrame.registerOnly subFrame)).trans
      (X86StateFrame.registerOnly checked)).lookup 9 (by decide)).trans used,
    roomWord ▸ (checked.lookup 10 (by decide)).trans knownFree, ⟨endpoint⟩⟩

namespace Examples

theorem a_full_agenda_still_accepts_an_empty_extension : 40 + (0 : Word).toNat ≤ 40 := by decide +kernel

/-- Adding before testing would wrap this impossible request to zero. -/
theorem a_wrapping_request_does_not_fit :
    (1 : Word) + (BitVec.ofNat 64 (2 ^ 64 - 1)) = 0 ∧
      ¬ (BitVec.ofNat 64 (2 ^ 64 - 1)).toNat ≤ 7 - 1 := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaReserve
