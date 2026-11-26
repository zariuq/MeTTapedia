import Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionAppendPrep

/-!
# Closing the private changed-node update

After the new record and its edges are initialized, install
its handle in the remap prefix and update the two staged
lengths. No live length or agenda field is written here.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionCommit

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls CodeApart footprint Reads)
open X86PlacedScalar (Code registerCode)
open NativeArenaGeometry (Region)
open NativeBindEntry (tableWire tableCode)
open NativeSubstitutionFrame (Table Ready nodeCount edgeCount mutableBytes)
open NativeSubstLeaf (MapReady mapStore)
open NativeAgendaRead (fieldSource)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def pointerCode : List ℕ := registerCode 0x89 4 10
def reloadCode : List ℕ := X86DataLoad.code true 7 10 0
def rootCode : List ℕ := registerCode 0x89 2 0
def addEdgesCode : List ℕ := registerCode (X86Arithmetic.opcode .add) 6 13
def encoding : X86PlacedMemory.Encoding := .direct 10 (by decide) (by decide)
def storeEdgesCode : List ℕ := encoding.bytes 13 32
def oneCode : List ℕ := X86Immediate32.code 13 1
def addNodeCode : List ℕ := registerCode (X86Arithmetic.opcode .add) 13 2
def storeNodesCode : List ℕ := encoding.bytes 2 24

def emit : List ℕ :=
  pointerCode ++ (reloadCode ++ (rootCode ++ (mapStore ++
    (addEdgesCode ++ (pointerCode ++ (storeEdgesCode ++ (oneCode ++ (addNodeCode ++ storeNodesCode))))))))

theorem emit_size : emit.length = 53 := by
  simp only [emit, List.length_append, show pointerCode.length = 3 from rfl, show reloadCode.length = 7 from rfl,
    show rootCode.length = 3 from rfl, show mapStore.length = 11 from rfl, show addEdgesCode.length = 3 from rfl,
    show storeEdgesCode.length = 7 from rfl, show oneCode.length = 6 from rfl, show addNodeCode.length = 3 from rfl,
    show storeNodesCode.length = 7 from rfl]

structure Placed (image : NativeImage.View) (start : ℕ) : Prop where
  extent : start + 53 ≤ image.size
  pointer : Code image start pointerCode
  reload : Code image (start + 3) reloadCode
  root : Code image (start + 10) rootCode
  map : Code image (start + 13) mapStore
  addEdges : Code image (start + 24) addEdgesCode
  base : Code image (start + 27) pointerCode
  storeEdges : Code image (start + 30) storeEdgesCode
  one : Code image (start + 37) oneCode
  addNode : Code image (start + 43) addNodeCode
  storeNodes : Code image (start + 46) storeNodesCode

theorem placed_of_emitted (image : NativeImage.View) (start : ℕ) (fits : start + 53 ≤ image.size)
    (code : Code image start emit) : Placed image start := by
  obtain ⟨pointer, rest⟩ := NativeWords.code_append (show Code image start (pointerCode ++ _) from code)
  obtain ⟨reload, rest⟩ := NativeWords.code_append rest
  obtain ⟨root, rest⟩ := NativeWords.code_append rest
  obtain ⟨map, rest⟩ := NativeWords.code_append rest
  obtain ⟨addEdges, rest⟩ := NativeWords.code_append rest
  obtain ⟨base, rest⟩ := NativeWords.code_append rest
  obtain ⟨storeEdges, rest⟩ := NativeWords.code_append rest
  obtain ⟨one, rest⟩ := NativeWords.code_append rest
  obtain ⟨addNode, storeNodes⟩ := NativeWords.code_append rest
  exact ⟨fits, pointer, reload, root, map, addEdges, base, storeEdges, one, addNode, storeNodes⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers : Finset Register := {.rax, .r10, .rdi, .r13, .rdx, .rflags, .rip}
private abbrev mapClobbers : Finset Register := {.rax, .r10, .rdi, .rip}
private abbrev lengthClobbers : Finset Register := {.r13, .r10, .rdx, .rflags, .rip}

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

def reloadWire : NativeWords.Wiring := ⟨10, by decide, by decide, encoding, 7, by decide, by decide⟩

variable {nodeCapacity edgeCapacity mapCapacity : ℕ}
variable {layout : NativeTermArena.Layout nodeCapacity edgeCapacity} {table : Region mapCapacity}
variable {frame : Table} {arena : PackedTerms.Arena} {mapping : Array Word}

def slotBytes (table : Region mapCapacity) (slot : Fin mapCapacity) : Finset ℕ :=
  footprint ((table.wordCell slot).cell 0).address

structure Geometry (table : Region mapCapacity) (frame : Table) (image : NativeImage.View) (base : BitVec 48) : Prop where
  mapCode : ∀ slot : Fin mapCapacity, CodeApart image base (slotBytes table slot)
  frameCode : CodeApart image base (mutableBytes frame)
  disjoint : ∀ (slot : Fin mapCapacity) (field : Fin 7), Disjoint (slotBytes table slot) (footprint (frame.cell field).address)

structure Input (layout : NativeTermArena.Layout nodeCapacity edgeCapacity) (table : Region mapCapacity)
    (frame : Table) (arena : PackedTerms.Arena) (mapping : Array Word) (original : Word) (width : ℕ) (before : Native) : Prop where
  staged : Ready layout table frame arena before
  map : MapReady table mapping before
  cursor : lookup before 1 = some original
  root : lookup before 2 = some (PackedTerms.root arena)
  edgeStart : lookup before 13 = some (BitVec.ofNat 64 arena.children.size)
  arity : lookup before 6 = some (BitVec.ofNat 64 width)

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (placed : Placed image start)
    (geometry : Geometry table frame image base) (original : Word) (cursor : original.toNat = mapping.size)
    (room : mapping.size < mapCapacity) (header : UnifierHeaders.Header) (children : Array Word)
    (input : Input layout table frame arena mapping original children.size before) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 11).run before = .ok () after ∧
      X86StateFrame.Frame clobbers (slotBytes table ⟨mapping.size, room⟩ ∪ mutableBytes frame) before after ∧
      Ready layout table frame (PackedTerms.place arena header children) after ∧
      MapReady table (mapping.push (PackedTerms.root arena)) after ∧
      lookup after 7 = some (table.atWord 0) ∧ lookup after 13 = some 1 ∧ Nonempty (At image after base (start + 53)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := placed.extent
  let slot : Fin mapCapacity := ⟨mapping.size, room⟩
  obtain ⟨a, opened, pointerFrame, baseValue, ⟨atReload⟩⟩ := X86PlacedRegisterMove.executes (handlers other extra)
    vector point (by omega) 4 10 frame.pointer input.staged.pointer placed.pointer
  have afterOpen := X86StateFrame.registerOnly pointerFrame
  obtain ⟨b, loaded, reloadFrame, mapBase, ⟨atRoot⟩⟩ := (fieldSource frame 0).fetch (handlers other extra) vector
    reloadWire (table.atWord 0) atReload (controls.transport afterOpen (by decide)) baseValue
    ((input.staged.word 0).preserved afterOpen (by simp)) (show start + 10 ≤ image.size by omega) placed.reload
  have linked : NativeWords.handlers (handlers other extra) = handlers other extra := rfl
  rw [linked] at loaded
  have throughReload := afterOpen.trans reloadFrame
  obtain ⟨c, moved, rootFrame, root, ⟨atMap⟩⟩ := X86PlacedRegisterMove.executes (handlers other extra)
    vector (show At image b base (start + 10) from atRoot) (by omega) 2 0 (PackedTerms.root arena)
    ((throughReload.lookup 2 (by decide)).trans input.root) placed.root
  have beforeMap := throughReload.trans (X86StateFrame.registerOnly rootFrame)
  have fit : 0 + original.toNat < mapCapacity := by rw [Nat.zero_add, cursor]; exact room
  have same : (⟨0 + original.toNat, fit⟩ : Fin mapCapacity) = slot :=
    Fin.ext ((Nat.zero_add _).trans cursor)
  have apartMap : CodeApart image base (footprint ((table.wordCell ⟨0 + original.toNat, fit⟩).cell 0).address) := by
    rw [same]
    exact geometry.mapCode slot
  obtain ⟨d, mapped, mapFrame, written, ⟨atEdges⟩⟩ := NativeIndexedWord.fetched_store other extra vector
    (show At image c base (start + 13) from atMap) (controls.transport beforeMap (by decide)) (by omega)
    NativeChildMarkLoop.markBase NativeOccursLoop.cursorIndex table 0 original (PackedTerms.root arena) fit
    ((rootFrame.lookup 7 (by decide)).trans mapBase) ((beforeMap.lookup 1 (by decide)).trans input.cursor)
    root placed.map apartMap
  rw [same] at mapFrame written
  have throughMap : X86StateFrame.Frame mapClobbers (slotBytes table slot) before d :=
    (beforeMap.trans mapFrame).mono (by decide) (by simp [slotBytes])
  have afterMap := input.map.extend room (PackedTerms.root arena) throughMap written
  have staged := input.staged.kept throughMap (by decide) (fun j => (geometry.disjoint slot j).symm)
  obtain ⟨e, edgesAdded, edgeFrame, edges, ⟨atBase⟩⟩ := X86PlacedArithmetic.executes (handlers other extra)
    vector (show At image d base (start + 24) from atEdges) (by omega) .add 6 13 _ _
    ((throughMap.lookup 6 (by decide)).trans input.arity) ((throughMap.lookup 13 (by decide)).trans input.edgeStart)
    placed.addEdges
  have ordinary : X86Arithmetic.linkedHandlers (handlers other extra) = handlers other extra := rfl
  rw [ordinary] at edgesAdded
  obtain ⟨f, based, baseFrame, baseRead, ⟨atEdgeStore⟩⟩ := X86PlacedRegisterMove.executes (handlers other extra)
    vector (show At image e base (start + 27) from atBase) (by omega) 4 10 frame.pointer
    ((edgeFrame.lookup 4 (by decide)).trans staged.pointer) placed.base
  let new := PackedTerms.place arena header children
  have edgeCountWord : lookup f 13 = some (BitVec.ofNat 64 new.children.size) := by
    change lookup e 13 = some (BitVec.ofNat 64 arena.children.size + BitVec.ofNat 64 children.size) at edges
    change lookup f 13 = some (BitVec.ofNat 64 (arena.children ++ children).size)
    rw [Array.size_append, BitVec.ofNat_add]
    exact (baseFrame.lookup 13 (by decide)).trans edges
  have beforeEdgeStore := X86StateFrame.registerOnly (edgeFrame.trans baseFrame)
  have edgeCode : CodeApart image base (footprint (frame.cell edgeCount).address) :=
    geometry.frameCode.mono Finset.subset_union_right
  obtain ⟨g, edgesStored, edgeStoreFrame, exactEdges, ⟨atOne⟩⟩ := X86PlacedMemory.stores (handlers other extra) vector
    (show At image f base (start + 30) from atEdgeStore)
    (controls.transport (throughMap.trans beforeEdgeStore) (by decide)) encoding 13 32 frame.pointer
    (BitVec.ofNat 64 new.children.size) (frame.cell edgeCount) baseRead edgeCountWord
    (show start + 37 ≤ image.size by omega) placed.storeEdges edgeCode
  obtain ⟨h, setOne, oneFrame, one, ⟨atNode⟩⟩ := X86PlacedScalar.rex_immediate
    (X86PlacedFrameAddress.nativeBase other) extra vector (show At image g base (start + 37) from atOne)
    (by omega) 13 1 placed.one
  have afterEdgeStore := (beforeEdgeStore.trans edgeStoreFrame).trans (X86StateFrame.registerOnly oneFrame)
  obtain ⟨i, nodeAdded, addFrame, nodeWord, ⟨atNodeStore⟩⟩ := X86PlacedArithmetic.executes (handlers other extra)
    vector (show At image h base (start + 43) from atNode) (by omega) .add 13 2 (PackedTerms.root arena) 1 one
    (((throughMap.trans afterEdgeStore).lookup 2 (by decide)).trans input.root) placed.addNode
  rw [ordinary] at nodeAdded
  have nodeCountWord : lookup i 2 = some (BitVec.ofNat 64 new.nodes.size) := by
    change lookup i 2 = some (BitVec.ofNat 64 arena.nodes.size + BitVec.ofNat 64 1) at nodeWord
    change lookup i 2 = some (BitVec.ofNat 64 (arena.nodes.push (PackedTerms.newNode arena header children)).size)
    rw [Array.size_push, BitVec.ofNat_add]
    exact nodeWord
  have framePointer := (((edgeStoreFrame.trans (X86StateFrame.registerOnly oneFrame)).trans
    (X86StateFrame.registerOnly addFrame)).lookup 10 (by decide)).trans baseRead
  have beforeNode := afterEdgeStore.trans (X86StateFrame.registerOnly addFrame)
  have nodeCode : CodeApart image base (footprint (frame.cell nodeCount).address) :=
    geometry.frameCode.mono Finset.subset_union_left
  obtain ⟨after, nodeStored, nodeStoreFrame, exactNodes, endpoint⟩ := X86PlacedMemory.stores (handlers other extra) vector
    (show At image i base (start + 46) from atNodeStore)
    (controls.transport (throughMap.trans beforeNode) (by decide)) encoding 2 24 frame.pointer
    (BitVec.ofNat 64 new.nodes.size) (frame.cell nodeCount) framePointer nodeCountWord
    (show start + 53 ≤ image.size by omega) placed.storeNodes nodeCode
  have proof : X86StateFrame.Frame lengthClobbers (mutableBytes frame) d after :=
    (beforeNode.trans nodeStoreFrame).mono (by decide) (by simp [mutableBytes, Finset.union_comm])
  have afterCounts := staged.lengths_updated proof (by decide) new exactNodes
    (exactEdges.preserved (((X86StateFrame.registerOnly oneFrame).trans (X86StateFrame.registerOnly addFrame)).trans nodeStoreFrame)
      (by simpa using frame.separate_words (by decide : edgeCount ≠ nodeCount)))
  have mapReady := afterMap.kept proof (fun j => Finset.disjoint_union_right.mpr
    ⟨geometry.disjoint j nodeCount, geometry.disjoint j edgeCount⟩)
  have all : X86StateFrame.Frame clobbers (slotBytes table slot ∪ mutableBytes frame) before after :=
    (throughMap.trans proof).mono (by decide) (Finset.Subset.refl _)
  have firstTwo := X86FuelPrefix.fetches_then 1 1 before a b opened loaded
  have firstThree := X86FuelPrefix.fetches_then 2 1 before b c firstTwo moved
  have firstFive := X86FuelPrefix.fetches_then 3 2 before c d firstThree mapped
  have firstSix := X86FuelPrefix.fetches_then 5 1 before d e firstFive edgesAdded
  have firstSeven := X86FuelPrefix.fetches_then 6 1 before e f firstSix based
  have firstEight := X86FuelPrefix.fetches_then 7 1 before f g firstSeven edgesStored
  have firstNine := X86FuelPrefix.fetches_then 8 1 before g h firstEight setOne
  have firstTen := X86FuelPrefix.fetches_then 9 1 before h i firstNine nodeAdded
  exact ⟨after, X86FuelPrefix.fetches_then 10 1 before i after firstTen nodeStored, all, afterCounts, mapReady,
    (proof.lookup 7 (by decide)).trans
      ((((X86StateFrame.registerOnly rootFrame).trans mapFrame).lookup 7 (by decide)).trans mapBase),
    (((X86StateFrame.registerOnly addFrame).trans nodeStoreFrame).lookup 13 (by decide)).trans one, endpoint⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionCommit
