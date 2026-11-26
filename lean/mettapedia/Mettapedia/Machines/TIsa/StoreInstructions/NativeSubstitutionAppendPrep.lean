import Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionCopyEntry
import Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionSelect

/-!
# Preparing a changed node from its original record

Copying borrows RBX for the edge destination. This block reloads
the term base and staged ordinals, selects the original record
again, and reads its symbol and arity. The pending root, source
cursor, variable and replacement never need to spill.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionAppendPrep

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls)
open X86PlacedScalar (Code registerCode)
open NativeArenaGeometry (Region)
open NativeSubstitutionFrame (Table Ready load values)
open NativeSubstitutionReserve (frameBase)
open NativeTermAppend (remapRegisters)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def openCode : List ℕ := registerCode 0x89 4 0
def frameCode : List ℕ :=
  X86DataLoad.code true 3 0 16 ++ (X86DataLoad.code true 2 0 24 ++ X86DataLoad.code true 13 0 32)
def readsCode : List ℕ := X86DataLoad.code true 10 6 8 ++ X86DataLoad.code true 14 6 24
def widthCode : List ℕ := registerCode 0x89 14 6
def tagCode : List ℕ := X86Immediate32.code 14 2

def emit : List ℕ :=
  openCode ++ (frameCode ++ (NativeSubstitutionSelect.emit ++ (readsCode ++ (widthCode ++ tagCode))))

theorem emit_size : emit.length = 58 := by
  simp only [emit, List.length_append, NativeSubstitutionSelect.emit_size,
    show openCode.length = 3 from rfl, show frameCode.length = 21 from rfl, show readsCode.length = 14 from rfl,
    show widthCode.length = 3 from rfl, show tagCode.length = 6 from rfl]

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers : Finset Register := {.rax, .rbx, .rdx, .r13, .rsi, .r10, .r14, .rip}
private abbrev frameClobbers : Finset Register := {key 3, .rip} ∪ ({key 2, .rip} ∪ ({key 13, .rip} ∪ ∅))
private abbrev recordClobbers : Finset Register := {key 10, .rip} ∪ ({key 14, .rip} ∪ ∅)

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

def frameLoads {nodeCapacity edgeCapacity mapCapacity : ℕ} (layout : NativeTermArena.Layout nodeCapacity edgeCapacity)
    (map : Region mapCapacity) (frame : Table) (target : PackedTerms.Arena) : List (NativeLoads.Load frameBase frame.pointer) :=
  [load frameBase frame 3 (by decide) 2 (values layout map target 2),
    load frameBase frame 2 (by decide) 3 (values layout map target 3),
    load frameBase frame 13 (by decide) 4 (values layout map target 4)]

private theorem resident_frame {nodeCapacity edgeCapacity mapCapacity : ℕ}
    {layout : NativeTermArena.Layout nodeCapacity edgeCapacity} {map : Region mapCapacity}
    {frame : Table} {target : PackedTerms.Arena} {before : Native} (ready : Ready layout map frame target before)
    (move : NativeLoads.Load frameBase frame.pointer) (one : move ∈ frameLoads layout map frame target) :
    X86PlacedMemory.Reads before move.cell.address move.value := by
  simp only [frameLoads, List.mem_cons, List.not_mem_nil, or_false] at one
  rcases one with rfl | rfl | rfl
  · exact ready.word 2
  · exact ready.word 3
  · exact ready.word 4

def recordBase : NativeLoads.Base := ⟨6, by decide, by decide⟩

def symbolRead (record : WordRegion.Region 4) (node : PackedTerms.Node) : NativeLoads.Load recordBase record.pointer :=
  ⟨10, by decide, _, record.cell 1, node.header.symbol⟩
def widthRead (record : WordRegion.Region 4) (node : PackedTerms.Node) : NativeLoads.Load recordBase record.pointer :=
  ⟨14, by decide, _, record.cell 3, node.childrenCount⟩

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (extent : start + 58 ≤ image.size)
    (installed : Code image start emit)
    {nodeCapacity edgeCapacity mapCapacity : ℕ}
    {layout : NativeTermArena.Layout nodeCapacity edgeCapacity} {map : Region mapCapacity}
    {frame : Table} {source target : PackedTerms.Arena} (extension : NativeRemapSnapshot.Extension source target)
    (record : Ready layout map frame target before) (resident : NativeTermArena.Ready layout target before)
    (original : Word) (inside : original.toNat < source.nodes.size) (cursor : lookup before 1 = some original)
    (zero : lookup before 12 = some 0) (children : Array Word)
    (tag : (source.nodes[original.toNat]'inside).header.tag = 2)
    (width : (source.nodes[original.toNat]'inside).childrenCount = BitVec.ofNat 64 children.size) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 11).run before = .ok () after ∧ X86StateFrame.Frame clobbers ∅ before after ∧
      NativeTermAppend.Input remapRegisters layout target
        (PackedTerms.newNode target (source.nodes[original.toNat]'inside).header children) after ∧
      Nonempty (At image after base (start + 58)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨opened, tail⟩ := NativeWords.code_append (show Code image start (openCode ++ _) from installed)
  obtain ⟨frameCodePlaced, tail⟩ := NativeWords.code_append tail
  change Code image (start + 24) _ at tail
  obtain ⟨selectPlaced, tail⟩ := NativeWords.code_append tail
  rw [NativeSubstitutionSelect.emit_size] at tail
  obtain ⟨readsPlaced, tail⟩ := NativeWords.code_append tail
  obtain ⟨widthPlaced, tagPlaced⟩ := NativeWords.code_append tail
  obtain ⟨a, openedFrame, openFrame, pointer, ⟨atFrame⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector point (by omega) 4 0 frame.pointer record.pointer opened
  have initial := X86StateFrame.registerOnly openFrame
  let framePlan := frameLoads layout map frame target
  obtain ⟨b, loaded, loadFrame, frameValues, ⟨atSource⟩⟩ := NativeLoads.fetched other extra vector atFrame
    (controls.transport initial (by decide)) framePlan (show start + 24 ≤ image.size by omega) frameCodePlaced pointer
    (resident_frame (record.preserved initial (by decide))) (by simp [framePlan, frameLoads, load])
  have nodes : lookup b 3 = some layout.nodes.pointer :=
    frameValues (load frameBase frame 3 (by decide) 2 (values layout map target 2)) (by simp [framePlan, frameLoads])
  have nodeCount : lookup b 2 = some (PackedTerms.root target) :=
    frameValues (load frameBase frame 2 (by decide) 3 (values layout map target 3)) (by simp [framePlan, frameLoads])
  have edgeCount : lookup b 13 = some (BitVec.ofNat 64 target.children.size) :=
    frameValues (load frameBase frame 13 (by decide) 4 (values layout map target 4)) (by simp [framePlan, frameLoads])
  have frameEffect : X86StateFrame.Frame frameClobbers ∅ a b := loadFrame
  have beforeSelect := initial.trans frameEffect
  have sourceReady := NativeRemapSnapshot.ready_restrict extension (resident.preserved beforeSelect)
  obtain ⟨c, selected, selectFrame, address, ⟨atRead⟩⟩ := NativeSubstitutionSelect.fetched other extra vector
    (show At image b base (start + 24) from atSource) (by omega) selectPlaced
    sourceReady original inside ((beforeSelect.lookup 1 (by decide)).trans cursor) nodes
    ((beforeSelect.lookup 12 (by decide)).trans zero)
  let i : Fin source.nodes.size := ⟨original.toNat, inside⟩
  let node := source.nodes[i]
  let sourceRecord := layout.record ⟨i.val, i.isLt.trans_le sourceReady.nodesFit⟩
  let fields := [symbolRead sourceRecord node, widthRead sourceRecord node]
  have earlier := beforeSelect.trans selectFrame
  have present (move : NativeLoads.Load recordBase sourceRecord.pointer) (access : move ∈ fields) :
      X86PlacedMemory.Reads c move.cell.address move.value := by
    simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at access
    rcases access with rfl | rfl
    · exact (sourceReady.node i 1).preserved selectFrame (by simp)
    · exact (sourceReady.node i 3).preserved selectFrame (by simp)
  obtain ⟨d, read, readFrame, readValues, ⟨atWidth⟩⟩ := NativeLoads.fetched other extra vector
    (show At image c base (start + 35) from atRead) (controls.transport earlier (by decide)) fields
    (show start + 49 ≤ image.size by omega) readsPlaced address present (by simp [fields, symbolRead, widthRead])
  have recordEffect : X86StateFrame.Frame recordClobbers ∅ c d := readFrame
  have symbol : lookup d 10 = some node.header.symbol := readValues (symbolRead sourceRecord node) (by simp [fields])
  have arity : lookup d 14 = some node.childrenCount := readValues (widthRead sourceRecord node) (by simp [fields])
  obtain ⟨e, moved, widthFrame, count, ⟨atTag⟩⟩ := X86PlacedRegisterMove.executes (handlers other extra) vector
    (show At image d base (start + 49) from atWidth) (by omega) 14 6 node.childrenCount arity widthPlaced
  obtain ⟨after, set, tagFrame, checkedTag, endpoint⟩ := X86PlacedScalar.rex_immediate (X86PlacedFrameAddress.nativeBase other)
    extra vector (show At image e base (start + 52) from atTag) (by omega) 14 2 tagPlaced
  have afterSelect := (((selectFrame.trans recordEffect).trans (X86StateFrame.registerOnly widthFrame)).trans
    (X86StateFrame.registerOnly tagFrame))
  have all : X86StateFrame.Frame clobbers ∅ before after :=
    (beforeSelect.trans afterSelect).mono (by decide) (by simp)
  have fieldValues : ∀ j : Fin 4, lookup after (remapRegisters.field j) =
      some (NativeTermArena.field (PackedTerms.newNode target node.header children) j) := by
    intro j
    fin_cases j
    · change lookup after 14 = some (source.nodes[original.toNat]'inside).header.tag
      rw [tag]
      exact checkedTag
    · exact ((widthFrame.trans tagFrame).lookup 10 (by decide)).trans symbol
    · exact (afterSelect.lookup 13 (by decide)).trans edgeCount
    · change lookup after 6 = some (BitVec.ofNat 64 children.size)
      rw [← width]
      exact (tagFrame.lookup 6 (by decide)).trans count
  have firstFour := X86FuelPrefix.fetches_then 1 3 before a b openedFrame loaded
  have firstSeven := X86FuelPrefix.fetches_then 4 3 before b c firstFour selected
  have firstNine := X86FuelPrefix.fetches_then 7 2 before c d firstSeven read
  have firstTen := X86FuelPrefix.fetches_then 9 1 before d e firstNine moved
  exact ⟨after, X86FuelPrefix.fetches_then 10 1 before e after firstTen set, all,
    ⟨resident.preserved all, (afterSelect.lookup 3 (by decide)).trans nodes,
      (afterSelect.lookup 2 (by decide)).trans nodeCount, (all.lookup 12 (by decide)).trans zero, fieldValues⟩, endpoint⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionAppendPrep
