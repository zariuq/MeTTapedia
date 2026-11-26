import Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaDispatch
import Mettapedia.Machines.TIsa.StoreInstructions.NativeChildPair

/-!
# Loading the two spans selected by the solver

The child pool base comes from the solver's immutable metadata.
Both counts come from the selected term records. Unequal counts
refuse before loading the starts or creating child addresses.
Equal counts leave the common width and both span bases ready
for the separately checked child-pair reader.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeSpanPrepare

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads)
open X86PlacedScalar (Code CompareBranch registerCode)
open NativeAgendaRead (fieldSource)
open NativeChildPair (spanPointer)
open X86IndexedAddress (Base addressCode)
open X86PreparedLea (Index)
open NativeWords (Wiring)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def metadataCode : List ℕ := registerCode 0x89 5 10
def poolCode : List ℕ := X86DataLoad.code true 0 10 8
def leftCountCode : List ℕ := X86DataLoad.code true 8 6 24
def rightCountCode : List ℕ := X86DataLoad.code true 9 7 24
def leftStartCode : List ℕ := X86DataLoad.code true 1 6 16
def rightStartCode : List ℕ := X86DataLoad.code true 2 7 16
def poolBase : Base := ⟨0, by decide⟩
def leftIndex : Index := ⟨1, by decide⟩
def rightIndex : Index := ⟨2, by decide⟩
def leftAddressCode : List ℕ := addressCode 6 leftIndex 3 poolBase
def rightAddressCode : List ℕ := addressCode 7 rightIndex 3 poolBase

def emit (start malformed : ℕ) : List ℕ :=
  metadataCode ++ (poolCode ++ (leftCountCode ++ (rightCountCode ++
    (NativeDecisions.compareBytes .equal 8 9 (start + 24) malformed ++
      (leftStartCode ++ (rightStartCode ++ (leftAddressCode ++ rightAddressCode)))))))

theorem emit_size (start malformed : ℕ) : (emit start malformed).length = 55 := rfl

structure Placed (image : NativeImage.View) (start malformed : ℕ) : Prop where
  extent : start + 55 ≤ image.size
  metadata : Code image start metadataCode
  pool : Code image (start + 3) poolCode
  leftCount : Code image (start + 10) leftCountCode
  rightCount : Code image (start + 17) rightCountCode
  width : CompareBranch image (start + 24) malformed .equal 8 9
  leftStart : Code image (start + 33) leftStartCode
  rightStart : Code image (start + 40) rightStartCode
  leftAddress : Code image (start + 47) leftAddressCode
  rightAddress : Code image (start + 51) rightAddressCode

theorem placed_of_emitted (image : NativeImage.View) (start malformed : ℕ)
    (extent : start + 55 ≤ image.size) (ends : malformed ≤ image.size) (short : image.size < 2 ^ 31)
    (bytes : Code image start (emit start malformed)) :
    Placed image start malformed := by
  obtain ⟨metadata, tail⟩ := NativeWords.code_append (show Code image start (metadataCode ++ _) from bytes)
  obtain ⟨pool, tail⟩ := NativeWords.code_append tail
  obtain ⟨leftCount, tail⟩ := NativeWords.code_append tail
  obtain ⟨rightCount, tail⟩ := NativeWords.code_append tail
  change Code image (start + 24) _ at tail
  obtain ⟨width, tail⟩ := NativeWords.code_append tail
  rw [NativeDecisions.compare_size] at tail
  obtain ⟨leftStart, tail⟩ := NativeWords.code_append tail
  obtain ⟨rightStart, tail⟩ := NativeWords.code_append tail
  obtain ⟨leftAddress, rightAddress⟩ := NativeWords.code_append tail
  exact ⟨extent, metadata, pool, leftCount, rightCount,
    NativeDecisions.compare_placed image _ _ _ _ _ (by omega) ends short width,
    leftStart, rightStart, leftAddress, rightAddress⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers

abbrev clobbers : Finset Register := {.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .rflags, .rip}

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

def poolWire : Wiring := ⟨10, by decide, by decide, MemoryBinding.storeEncoding, 0, by decide, by decide⟩
def leftCountWire : Wiring := ⟨6, by decide, by decide, MemoryBinding.storeEncoding, 8, by decide, by decide⟩
def rightCountWire : Wiring := ⟨7, by decide, by decide, MemoryBinding.storeEncoding, 9, by decide, by decide⟩
def leftStartWire : Wiring := ⟨6, by decide, by decide, MemoryBinding.storeEncoding, 1, by decide, by decide⟩
def rightStartWire : Wiring := ⟨7, by decide, by decide, MemoryBinding.storeEncoding, 2, by decide, by decide⟩

variable {agendaCapacity nodeCapacity edgeCapacity : ℕ}
variable {agendaLayout : NativeAgendaRecords.Layout agendaCapacity}
variable {termLayout : NativeTermArena.Layout nodeCapacity edgeCapacity} {arena : PackedTerms.Arena}

structure Inputs (agendaLayout : NativeAgendaRecords.Layout agendaCapacity)
    (termLayout : NativeTermArena.Layout nodeCapacity edgeCapacity) (arena : PackedTerms.Arena)
    (left right : Fin arena.nodes.size) (before : Native) : Prop where
  ready : NativeTermArena.Ready termLayout arena before
  agendaBase : lookup before 5 = some agendaLayout.words.pointer
  childBase : Reads before (agendaLayout.metadata.cell 1).address termLayout.edges.pointer
  left : lookup before 6 = some (ready.bank left).pointer
  right : lookup before 7 = some (ready.bank right).pointer

theorem Inputs.from_dispatch {before after : Native} {left right : Word}
    (ready : NativeTermArena.Ready termLayout arena before)
    (selected : NativeAgendaDispatch.Selected ready left right after)
    (frame : X86StateFrame.Frame NativeAgendaDispatch.clobbers ∅ before after)
    (agendaBase : lookup before 5 = some agendaLayout.words.pointer)
    (childBase : Reads before (agendaLayout.metadata.cell 1).address termLayout.edges.pointer)
    (l : left.toNat < arena.nodes.size) (r : right.toNat < arena.nodes.size) :
    Inputs agendaLayout termLayout arena ⟨left.toNat, l⟩ ⟨right.toNat, r⟩ after := by
  have kept := ready.preserved frame
  obtain ⟨atL, atR, _⟩ := selected l r
  refine ⟨kept, (frame.lookup 5 (by decide)).trans agendaBase, childBase.preserved frame (by simp), ?_, ?_⟩
  · rw [kept.bank_word left l]
    simpa only [ready.bank_word] using atL
  · rw [kept.bank_word right r]
    simpa only [ready.bank_word] using atR

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start malformed : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (placed : Placed image start malformed)
    (left right : Fin arena.nodes.size) (input : Inputs agendaLayout termLayout arena left right before) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame clobbers ∅ before after ∧
      if arena.nodes[left].childrenCount = arena.nodes[right].childrenCount then
        steps = 10 ∧ lookup after 8 = some arena.nodes[left].childrenCount ∧
          lookup after 6 = some (spanPointer termLayout arena.nodes[left]) ∧
          lookup after 7 = some (spanPointer termLayout arena.nodes[right]) ∧
          Nonempty (At image after base (start + 55))
      else steps = 6 ∧ Nonempty (At image after base malformed) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have room := placed.extent
  have noHandlerChange : NativeWords.handlers (handlers other extra) = handlers other extra := rfl
  let l := termLayout.record ⟨left.val, left.isLt.trans_le input.ready.nodesFit⟩
  let r := termLayout.record ⟨right.val, right.isLt.trans_le input.ready.nodesFit⟩
  have metadataBase : agendaLayout.metadata.pointer = agendaLayout.words.pointer := BitVec.add_zero _
  obtain ⟨a, baseMoved, baseFrame, metaRead, ⟨atPool⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector point (by omega) 5 10 agendaLayout.words.pointer input.agendaBase placed.metadata
  have first := X86StateFrame.registerOnly baseFrame
  obtain ⟨b, poolLoaded, poolFrame, pool, ⟨atLeftCount⟩⟩ := (fieldSource agendaLayout.metadata 1).fetch
    (handlers other extra) vector poolWire termLayout.edges.pointer atPool (controls.transport first (by decide))
    (metadataBase.symm ▸ metaRead) (input.childBase.preserved first (by simp))
    (show start + 10 ≤ image.size by omega) placed.pool
  rw [noHandlerChange] at poolLoaded
  have prelude := first.trans poolFrame
  obtain ⟨c, leftLoaded, leftFrame, leftCount, ⟨atRightCount⟩⟩ := (fieldSource l 3).fetch
    (handlers other extra) vector leftCountWire arena.nodes[left].childrenCount
    (show At image b base (start + 10) from atLeftCount) (controls.transport prelude (by decide))
    ((prelude.lookup 6 (by decide)).trans input.left) ((input.ready.node left 3).preserved prelude (by simp))
    (show start + 17 ≤ image.size by omega) placed.leftCount
  rw [noHandlerChange] at leftLoaded
  have throughLeft := prelude.trans leftFrame
  obtain ⟨d, rightLoaded, rightFrame, rightCount, ⟨atCompare⟩⟩ := (fieldSource r 3).fetch
    (handlers other extra) vector rightCountWire arena.nodes[right].childrenCount
    (show At image c base (start + 17) from atRightCount) (controls.transport throughLeft (by decide))
    ((throughLeft.lookup 7 (by decide)).trans input.right) ((input.ready.node right 3).preserved throughLeft (by simp))
    (show start + 24 ≤ image.size by omega) placed.rightCount
  rw [noHandlerChange] at rightLoaded
  have loaded := throughLeft.trans rightFrame
  obtain ⟨e, compared, compareFrame, ⟨atEqual⟩⟩ := X86PlacedScalar.compare_branch (X86PlacedFrameAddress.nativeBase other)
    extra vector (show At image d base (start + 24) from atCompare) .equal 8 9 placed.width _ _
    ((rightFrame.lookup 8 (by decide)).trans leftCount) rightCount
  have gather := X86FuelPrefix.fetches_then 2 1 before b c
    (X86FuelPrefix.fetches_then 1 1 before a b baseMoved poolLoaded) leftLoaded
  have counts := X86FuelPrefix.fetches_then 3 1 before c d gather rightLoaded
  have decidePath := X86FuelPrefix.fetches_then 4 2 before d e counts compared
  have decided := loaded.trans (X86StateFrame.registerOnly compareFrame)
  simp only [Comparison.evaluate, beq_iff_eq] at atEqual
  by_cases equal : arena.nodes[left].childrenCount = arena.nodes[right].childrenCount
  · simp only [if_pos equal] at atEqual
    obtain ⟨f, startL, startLFrame, startOfL, ⟨atStartR⟩⟩ := (fieldSource l 2).fetch
      (handlers other extra) vector leftStartWire arena.nodes[left].childrenAt
      (show At image e base (start + 33) from atEqual) (controls.transport decided (by decide))
      ((decided.lookup 6 (by decide)).trans input.left) ((input.ready.node left 2).preserved decided (by simp))
      (show start + 40 ≤ image.size by omega) placed.leftStart
    rw [noHandlerChange] at startL
    have withLeft := decided.trans startLFrame
    obtain ⟨g, startR, startRFrame, startOfR, ⟨atAddrL⟩⟩ := (fieldSource r 2).fetch
      (handlers other extra) vector rightStartWire arena.nodes[right].childrenAt
      (show At image f base (start + 40) from atStartR) (controls.transport withLeft (by decide))
      ((withLeft.lookup 7 (by decide)).trans input.right) ((input.ready.node right 2).preserved withLeft (by simp))
      (show start + 47 ≤ image.size by omega) placed.rightStart
    rw [noHandlerChange] at startR
    have withSpans := withLeft.trans startRFrame
    have poolRest := (((((leftFrame.trans rightFrame).trans (X86StateFrame.registerOnly compareFrame)).trans
      startLFrame).trans startRFrame).lookup 0 (by decide)).trans pool
    obtain ⟨h, placedL, placeLFrame, pointerL, ⟨atAddrR⟩⟩ := X86IndexedAddress.forms_address other extra vector
      (show At image g base (start + 47) from atAddrL) (by omega) 6 leftIndex 3 poolBase placed.leftAddress
      termLayout.edges.pointer arena.nodes[left].childrenAt poolRest ((startRFrame.lookup 1 (by decide)).trans startOfL)
    obtain ⟨after, placedR, placeRFrame, pointerR, endpoint⟩ := X86IndexedAddress.forms_address other extra vector
      (show At image h base (start + 51) from atAddrR) (by omega) 7 rightIndex 3 poolBase placed.rightAddress
      termLayout.edges.pointer arena.nodes[right].childrenAt ((placeLFrame.lookup 0 (by decide)).trans poolRest)
      ((placeLFrame.lookup 2 (by decide)).trans startOfR)
    have placement := X86StateFrame.registerOnly (placeLFrame.trans placeRFrame)
    have work := X86FuelPrefix.fetches_then 7 1 before f g
      (X86FuelPrefix.fetches_then 6 1 before e f decidePath startL) startR
    refine ⟨after, 10, X86FuelPrefix.fetches_then 9 1 before h after
      (X86FuelPrefix.fetches_then 8 1 before g h work placedL) placedR,
      (withSpans.trans placement).mono (by decide) (by simp), ?_⟩
    rw [if_pos equal]
    exact ⟨rfl, (((((rightFrame.trans (X86StateFrame.registerOnly compareFrame)).trans startLFrame).trans
      startRFrame).trans placement).lookup 8 (by decide)).trans leftCount,
      (placeRFrame.lookup 6 (by decide)).trans pointerL, pointerR, endpoint⟩
  · refine ⟨e, 6, decidePath, decided.mono (by decide) (by simp), ?_⟩
    rw [if_neg equal]
    exact ⟨rfl, ⟨by simpa only [if_neg equal] using atEqual⟩⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeSpanPrepare
