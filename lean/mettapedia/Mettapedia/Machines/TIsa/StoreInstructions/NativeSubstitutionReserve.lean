import Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionFrame

/-!
# Reserving a changed application from the staged counts

The first test checks for one remaining node. The second checks
the actual arity against the edge capacity minus the staged edge
count. The subtraction is exact, and neither failure writes
memory. The old edge count doubles as the new span's ordinal.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionReserve

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls)
open X86PlacedScalar (Code CompareBranch registerCode)
open NativeArenaGeometry (Region)
open NativeSubstitutionFrame (Table Ready values load)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def frameBase : NativeLoads.Base := ⟨0, by decide, by decide⟩
def openCode : List ℕ := registerCode 0x89 4 0
def nodeWords : List ℕ := X86DataLoad.code true 10 0 24 ++ X86DataLoad.code true 14 0 40
def edgeWords : List ℕ := X86DataLoad.code true 10 0 32 ++ X86DataLoad.code true 14 0 48
def freeCode : List ℕ := registerCode (X86Arithmetic.opcode .sub) 10 14

def emit (start exhausted : ℕ) : List ℕ :=
  openCode ++ (nodeWords ++ (NativeDecisions.compareBytes .lessUnsigned 10 14 (start + 17) exhausted ++
    (edgeWords ++ (freeCode ++ NativeDecisions.compareBytes .lessEqualUnsigned 2 14 (start + 43) exhausted))))

theorem emit_size (start exhausted : ℕ) : (emit start exhausted).length = 52 := by
  simp only [emit, List.length_append, NativeDecisions.compare_size,
    show openCode.length = 3 from rfl, show nodeWords.length = 14 from rfl, show edgeWords.length = 14 from rfl,
    show freeCode.length = 3 from rfl]

structure Placed (image : NativeImage.View) (start exhausted : ℕ) : Prop where
  extent : start + 52 ≤ image.size
  opened : Code image start openCode
  nodes : Code image (start + 3) nodeWords
  roomNode : CompareBranch image (start + 17) exhausted .lessUnsigned 10 14
  edges : Code image (start + 26) edgeWords
  free : Code image (start + 40) freeCode
  roomEdge : CompareBranch image (start + 43) exhausted .lessEqualUnsigned 2 14

theorem placed_of_emitted (image : NativeImage.View) (start exhausted : ℕ)
    (fits : start + 52 ≤ image.size) (target : exhausted ≤ image.size) (short : image.size < 2 ^ 31)
    (code : Code image start (emit start exhausted)) : Placed image start exhausted := by
  obtain ⟨opened, rest⟩ := NativeWords.code_append (show Code image start (openCode ++ _) from code)
  obtain ⟨nodes, rest⟩ := NativeWords.code_append rest
  change Code image (start + 17) _ at rest
  obtain ⟨roomNode, rest⟩ := NativeWords.code_append rest
  rw [NativeDecisions.compare_size] at rest
  obtain ⟨edges, rest⟩ := NativeWords.code_append rest
  obtain ⟨free, roomEdge⟩ := NativeWords.code_append rest
  exact ⟨fits, opened, nodes,
    NativeDecisions.compare_placed image _ _ _ _ _ (by omega) target short roomNode, edges, free,
    NativeDecisions.compare_placed image _ _ _ _ _ (by omega) target short roomEdge⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers : Finset Register := {.rax, .r10, .r14, .rflags, .rip}
private abbrev loadClobbers : Finset Register := {key 10, .rip} ∪ ({key 14, .rip} ∪ ∅)

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

theorem word_of_region {length : ℕ} (region : Region length) (n : ℕ) (fits : n ≤ length) :
    (BitVec.ofNat 64 n).toNat = n := by
  by_cases pos : 0 < length
  · have bound := region.positive_room pos
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · rw [show n = 0 by omega]
    rfl

variable {nodeCapacity edgeCapacity mapCapacity : ℕ}
variable {layout : NativeTermArena.Layout nodeCapacity edgeCapacity} {map : Region mapCapacity}
variable {frame : Table} {arena : PackedTerms.Arena}

def loadNodes (layout : NativeTermArena.Layout nodeCapacity edgeCapacity) (map : Region mapCapacity)
    (frame : Table) (arena : PackedTerms.Arena) : List (NativeLoads.Load frameBase frame.pointer) :=
  [load frameBase frame 10 (by decide) 3 (values layout map arena 3),
    load frameBase frame 14 (by decide) 5 (values layout map arena 5)]

def loadEdges (layout : NativeTermArena.Layout nodeCapacity edgeCapacity) (map : Region mapCapacity)
    (frame : Table) (arena : PackedTerms.Arena) : List (NativeLoads.Load frameBase frame.pointer) :=
  [load frameBase frame 10 (by decide) 4 (values layout map arena 4),
    load frameBase frame 14 (by decide) 6 (values layout map arena 6)]

private theorem loadedNodes {before : Native} (s : Ready layout map frame arena before)
    (move : NativeLoads.Load frameBase frame.pointer) (member : move ∈ loadNodes layout map frame arena) :
    X86PlacedMemory.Reads before move.cell.address move.value := by
  simp only [loadNodes, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact s.word 3
  · exact s.word 5

private theorem loadedEdges {before : Native} (s : Ready layout map frame arena before)
    (move : NativeLoads.Load frameBase frame.pointer) (member : move ∈ loadEdges layout map frame arena) :
    X86PlacedMemory.Reads before move.cell.address move.value := by
  simp only [loadEdges, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact s.word 4
  · exact s.word 6

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start exhausted : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (placed : Placed image start exhausted)
    (record : Ready layout map frame arena before) (resident : NativeTermArena.Ready layout arena before)
    (width : Word) (knownWidth : lookup before 2 = some width) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame clobbers ∅ before after ∧
      if arena.nodes.size < nodeCapacity then
        if arena.children.size + width.toNat ≤ edgeCapacity then
          steps = 10 ∧ lookup after 10 = some (BitVec.ofNat 64 arena.children.size) ∧
            Nonempty (At image after base (start + 52))
        else steps = 10 ∧ Nonempty (At image after base exhausted)
      else steps = 5 ∧ Nonempty (At image after base exhausted) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := placed.extent
  obtain ⟨a, first, moveFrame, pointer, ⟨atNodes⟩⟩ := X86PlacedRegisterMove.executes (handlers other extra) vector
    point (by omega) 4 0 frame.pointer record.pointer placed.opened
  have asFrame := X86StateFrame.registerOnly moveFrame
  let nodeLoads := loadNodes layout map frame arena
  obtain ⟨b, second, nodeFrame, nodeValues, ⟨atNodeTest⟩⟩ := NativeLoads.fetched other extra vector atNodes
    (controls.transport asFrame (by decide)) nodeLoads (show start + 17 ≤ image.size by omega) placed.nodes pointer
    (loadedNodes (record.preserved asFrame (by decide))) (by simp [nodeLoads, loadNodes, load])
  have nodeEffect : X86StateFrame.Frame loadClobbers ∅ a b := nodeFrame
  have throughNodes := asFrame.trans nodeEffect
  have nodeCount : lookup b 10 = some (BitVec.ofNat 64 arena.nodes.size) :=
    nodeValues (load frameBase frame 10 (by decide) 3 (values layout map arena 3)) (by simp [nodeLoads, loadNodes])
  have nodeLimit : lookup b 14 = some (BitVec.ofNat 64 nodeCapacity) :=
    nodeValues (load frameBase frame 14 (by decide) 5 (values layout map arena 5)) (by simp [nodeLoads, loadNodes])
  obtain ⟨c, testedNodes, nodeTestFrame, ⟨ready⟩⟩ := X86PlacedScalar.compare_branch (X86PlacedFrameAddress.nativeBase other)
    extra vector (show At image b base (start + 17) from atNodeTest) .lessUnsigned 10 14 placed.roomNode _ _
    nodeCount nodeLimit
  have staged := throughNodes.trans (X86StateFrame.registerOnly nodeTestFrame)
  have firstThree := X86FuelPrefix.fetches_then 1 2 before a b first second
  have firstFive := X86FuelPrefix.fetches_then 3 2 before b c firstThree testedNodes
  change At image c base
    (if decide ((BitVec.ofNat 64 arena.nodes.size).toNat < (BitVec.ofNat 64 nodeCapacity).toNat) then start + 17 + 9
      else exhausted) at ready
  rw [resident.count_word, word_of_region layout.nodes _ (by omega)] at ready
  by_cases nodeRoom : arena.nodes.size < nodeCapacity
  · simp only [nodeRoom, decide_true, if_true] at ready
    let edgeLoads := loadEdges layout map frame arena
    have savedPointer := ((nodeEffect.trans (X86StateFrame.registerOnly nodeTestFrame)).lookup 0 (by decide)).trans pointer
    obtain ⟨d, readEdges, edgeFrame, edgeValues, ⟨atFree⟩⟩ := NativeLoads.fetched other extra vector
      (show At image c base (start + 26) from ready) (controls.transport staged (by decide)) edgeLoads
      (show start + 40 ≤ image.size by omega) placed.edges savedPointer (loadedEdges (record.preserved staged (by decide)))
      (by simp [edgeLoads, loadEdges, load])
    have edgeEffect : X86StateFrame.Frame loadClobbers ∅ c d := edgeFrame
    have live : lookup d 10 = some (BitVec.ofNat 64 arena.children.size) :=
      edgeValues (load frameBase frame 10 (by decide) 4 (values layout map arena 4)) (by simp [edgeLoads, loadEdges])
    have limit : lookup d 14 = some (BitVec.ofNat 64 edgeCapacity) :=
      edgeValues (load frameBase frame 14 (by decide) 6 (values layout map arena 6)) (by simp [edgeLoads, loadEdges])
    let free := BitVec.ofNat 64 edgeCapacity - BitVec.ofNat 64 arena.children.size
    obtain ⟨e, subtracted, freeFrame, rawFree, ⟨atEdgeTest⟩⟩ := X86PlacedArithmetic.executes
      (handlers other extra) vector (show At image d base (start + 40) from atFree) (by omega)
      .sub 10 14 _ _ live limit placed.free
    have ordinary : X86Arithmetic.linkedHandlers (handlers other extra) = handlers other extra := rfl
    rw [ordinary] at subtracted
    have knownFree : lookup e 14 = some free := rawFree
    have freeExact : free.toNat = edgeCapacity - arena.children.size := by
      have ordering : BitVec.ofNat 64 arena.children.size ≤ BitVec.ofNat 64 edgeCapacity := by
        rw [BitVec.le_def, word_of_region layout.edges _ resident.edgesFit, word_of_region layout.edges _ (Nat.le_refl _)]
        exact resident.edgesFit
      rw [show free = BitVec.ofNat 64 edgeCapacity - BitVec.ofNat 64 arena.children.size from rfl,
        BitVec.toNat_sub_of_le ordering, word_of_region layout.edges _ resident.edgesFit,
        word_of_region layout.edges _ (Nat.le_refl _)]
    have throughFree := (staged.trans edgeEffect).trans (X86StateFrame.registerOnly freeFrame)
    obtain ⟨after, tested, finalFrame, ⟨endpoint⟩⟩ := X86PlacedScalar.compare_branch (X86PlacedFrameAddress.nativeBase other)
      extra vector (show At image e base (start + 43) from atEdgeTest) .lessEqualUnsigned 2 14 placed.roomEdge width free
      ((throughFree.lookup 2 (by decide)).trans knownWidth) knownFree
    change At image after base (if decide (width.toNat ≤ free.toNat) then start + 43 + 9 else exhausted) at endpoint
    rw [freeExact] at endpoint
    have equivalent : width.toNat ≤ edgeCapacity - arena.children.size ↔ arena.children.size + width.toNat ≤ edgeCapacity := by
      have residentEdges := resident.edgesFit
      omega
    simp only [equivalent, decide_eq_true_eq] at endpoint
    have firstSeven := X86FuelPrefix.fetches_then 5 2 before c d firstFive readEdges
    have firstEight := X86FuelPrefix.fetches_then 7 1 before d e firstSeven subtracted
    have full := X86FuelPrefix.fetches_then 8 2 before e after firstEight tested
    have frame : X86StateFrame.Frame clobbers ∅ before after :=
      (throughFree.trans (X86StateFrame.registerOnly finalFrame)).mono (by decide) (by simp)
    refine ⟨after, 10, full, frame, ?_⟩
    rw [if_pos nodeRoom]
    by_cases edgeRoom : arena.children.size + width.toNat ≤ edgeCapacity
    · rw [if_pos edgeRoom] at endpoint ⊢
      exact ⟨rfl, ((freeFrame.trans finalFrame).lookup 10 (by decide)).trans live, ⟨endpoint⟩⟩
    · rw [if_neg edgeRoom] at endpoint ⊢
      exact ⟨rfl, ⟨endpoint⟩⟩
  · simp only [nodeRoom, decide_false] at ready
    refine ⟨c, 5, firstFive, staged.mono (by decide) (by simp), ?_⟩
    rw [if_neg nodeRoom]
    exact ⟨rfl, ⟨ready⟩⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionReserve
