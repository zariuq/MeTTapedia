import Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardWorkspace

/-!
# Re-entering the unifier for one guard candidate

Each trial starts with one equation, no bindings, and the
fixed term prefix. Seven stores reset the live cursors and
the one equation; no term, edge, or stale scratch word is copied.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardTrial

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Reads Controls CodeApart footprint Encoding)
open X86PlacedScalar (Code registerCode)
open NativeGuardWorkspace (Frame Geometry Ready values activeLengths)
open NativeArenaGeometry (Region)
open NativeSubstitutionMemory (nodeBytes edgeBytes)
open NativeSolverStep (Resident Writes)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def stackCode : List ℕ := registerCode 0x89 4 6
def loadCode : List ℕ := X86DataLoad.code true 15 6 64 ++ (X86DataLoad.code true 10 6 72 ++
  (X86DataLoad.code true 5 6 80 ++ (X86DataLoad.code true 3 6 16 ++ X86DataLoad.code true 9 6 56)))
def encoding : Encoding := .direct 6 (by decide) (by decide)
def agendaCode : List ℕ := registerCode 0x89 5 6
def seedCode : List ℕ := encoding.bytes 12 24 ++ (encoding.bytes 1 32 ++ (encoding.bytes 2 40 ++ encoding.bytes 13 0))
def trailCode : List ℕ := registerCode 0x89 9 6
def clearCode : List ℕ := encoding.bytes 12 0
def lengthsCode : List ℕ := encoding.bytes 15 24 ++ encoding.bytes 10 32
def rootCode : List ℕ := registerCode 0x89 13 11
def tagCode : List ℕ := X86Immediate32.code 14 2

def emit : List ℕ :=
  stackCode ++ (loadCode ++ (agendaCode ++ (seedCode ++ (trailCode ++ (clearCode ++
    (stackCode ++ (lengthsCode ++ (rootCode ++ tagCode))))))))

theorem emit_size : emit.length = 105 := rfl

structure Placed (image : NativeImage.View) (start : ℕ) : Prop where
  extent : start + 105 ≤ image.size
  stack : Code image start stackCode
  load : Code image (start + 3) loadCode
  agenda : Code image (start + 38) agendaCode
  seed : Code image (start + 41) seedCode
  trail : Code image (start + 69) trailCode
  clear : Code image (start + 72) clearCode
  restack : Code image (start + 79) stackCode
  lengths : Code image (start + 82) lengthsCode
  root : Code image (start + 96) rootCode
  tag : Code image (start + 99) tagCode

theorem placed_of_emitted (image : NativeImage.View) (start : ℕ) (extent : start + 105 ≤ image.size)
    (code : Code image start emit) : Placed image start := by
  obtain ⟨stack, tail⟩ := NativeWords.code_append (show Code image start (stackCode ++ _) from code)
  obtain ⟨loaded, tail⟩ := NativeWords.code_append tail
  obtain ⟨agenda, tail⟩ := NativeWords.code_append tail
  obtain ⟨seed, tail⟩ := NativeWords.code_append tail
  obtain ⟨trail, tail⟩ := NativeWords.code_append tail
  obtain ⟨clear, tail⟩ := NativeWords.code_append tail
  obtain ⟨restack, tail⟩ := NativeWords.code_append tail
  obtain ⟨lengths, tail⟩ := NativeWords.code_append tail
  obtain ⟨root, tag⟩ := NativeWords.code_append tail
  exact ⟨extent, stack, loaded, agenda, seed, trail, clear, restack, lengths, root, tag⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers : Finset Register := {.rbp, .rbx, .rsi, .r9, .r10, .r11, .r14, .r15, .rip}
theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

variable {nc ec mc ac tc : ℕ}
variable {term : NativeTermArena.Layout nc ec} {map : Region mc} {frame : Frame}
variable {agenda : NativeAgendaRecords.Layout ac} {trail : NativeAgendaRecords.Layout tc}
variable {image : NativeImage.View} {base : BitVec 48}

private def stackBase : NativeLoads.Base := ⟨6, by decide, by decide⟩
private def load (frame : Frame) (register : Fin 16) (different : stackBase.register ≠ register)
    (slot : Fin 16) (word : Word) : NativeLoads.Load stackBase frame.pointer :=
  ⟨register, different, _, frame.cell slot, word⟩

private def loads (frame : Frame) (term : NativeTermArena.Layout nc ec) (agenda : NativeAgendaRecords.Layout ac)
    (trail : NativeAgendaRecords.Layout tc) (source : PackedTerms.Arena) :
    List (NativeLoads.Load stackBase frame.pointer) :=
  [load frame 15 (by decide) 8 (BitVec.ofNat 64 source.nodes.size),
    load frame 10 (by decide) 9 (BitVec.ofNat 64 source.children.size),
    load frame 5 (by decide) 10 agenda.words.pointer,
    load frame 3 (by decide) 2 term.nodes.pointer,
    load frame 9 (by decide) 7 trail.words.pointer]

private def wordWrite {n : ℕ} (bank : WordRegion.Region n) (source : Fin 16) (i : Fin n) (value : Word) :
    NativeStores.Write bank.pointer := ⟨source, _, bank.cell i, value⟩

private def agendaBank (layout : NativeAgendaRecords.Layout ac) (room : 0 < ac) : WordRegion.Region 6 :=
  layout.words.slice 0 6 (by decide) (by omega) (by decide)

private theorem agendaBank_pointer (layout : NativeAgendaRecords.Layout ac) (room : 0 < ac) :
    (agendaBank layout room).pointer = layout.words.pointer := BitVec.add_zero _

private theorem seed_header (room : 0 < ac) :
    ((agendaBank agenda room).cell 0).address = (agenda.header.cell 0).address := by
  simp only [agendaBank, NativeAgendaRecords.Layout.header, Region.slice_address]
  rfl

private def seedSlot : Fin 3 → Fin 6 := fun i => ⟨3 + i.val, by have := i.isLt; omega⟩

private theorem seed_cell (room : 0 < ac) (j : Fin 3) :
    ((agendaBank agenda room).cell (seedSlot j)).address = ((agenda.record ⟨0, room⟩).cell j).address := by
  simp only [agendaBank, NativeAgendaRecords.Layout.record, Region.slice_address, Nat.zero_add]
  rfl

private def seedSource (j : Fin 3) : Fin 16 := if j = 0 then 12 else if j = 1 then 1 else 2
private def equation (left right : Word) : PackedEquations.Node := ⟨0, left, right⟩
private def seedField (bank : WordRegion.Region 6) (left right : Word) (j : Fin 3) : NativeStores.Write bank.pointer :=
  wordWrite bank (seedSource j) (seedSlot j) (NativeAgendaRecords.field (equation left right) j)
private def seedWrites (bank : WordRegion.Region 6) (left right : Word) : List (NativeStores.Write bank.pointer) :=
  [seedField bank left right 0, seedField bank left right 1, seedField bank left right 2, wordWrite bank 13 0 1]
private def lengthWrites (frame : Frame) (source : PackedTerms.Arena) : List (NativeStores.Write frame.pointer) :=
  [wordWrite frame 15 3 (BitVec.ofNat 64 source.nodes.size), wordWrite frame 10 4 (BitVec.ofNat 64 source.children.size)]

private theorem separate_writes {n : ℕ} (bank : WordRegion.Region n) (fields : List (Fin n × Fin 16 × Word))
    (distinct : (fields.map Prod.fst).Nodup) :
    NativeStores.Separate (fields.map fun (i, reg, value) => wordWrite bank reg i value) := by
  induction fields with
  | nil => exact .nil
  | cons first rest ih =>
    obtain ⟨i, reg, value⟩ := first
    rw [List.map_cons, List.nodup_cons] at distinct
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih distinct.2⟩
    intro write found
    obtain ⟨⟨j, source, v⟩, present, rfl⟩ := List.mem_map.mp found
    apply bank.separate_words
    intro same
    have picked : j ∈ rest.map Prod.fst := List.mem_map.mpr ⟨(j, source, v), present, rfl⟩
    exact distinct.1 (same.symm ▸ picked)

def seedBytes (agenda : NativeAgendaRecords.Layout ac) (room : 0 < ac) : Finset ℕ :=
  ((footprint ((agenda.record ⟨0, room⟩).cell 0).address ∪
    (footprint ((agenda.record ⟨0, room⟩).cell 1).address ∪ footprint ((agenda.record ⟨0, room⟩).cell 2).address)) ∪
    NativeBindingPublish.header agenda)

def bytes (frame : Frame) (agenda : NativeAgendaRecords.Layout ac) (trail : NativeAgendaRecords.Layout tc) (room : 0 < ac) : Finset ℕ :=
  seedBytes agenda room ∪ NativeBindingPublish.header trail ∪ activeLengths frame

private theorem seed_effect {left right : Word} {room : 0 < ac} :
    NativeStores.written (seedWrites (agendaBank agenda room) left right) = seedBytes agenda room := by
  simp only [NativeStores.written, seedWrites, seedField, wordWrite, seedBytes, seed_cell, seed_header,
    NativeBindingPublish.header, Finset.union_empty, Finset.union_assoc]

private theorem seed_scope (room : 0 < ac) : Writes term map frame.solver agenda trail (seedBytes agenda room) := by
  apply Writes.union
  · apply Writes.pending (lo := 0) (hi := 1)
    intro b present
    simp only [Finset.mem_union] at present
    rcases present with a | a | a
    · exact ⟨⟨0, room⟩, 0, Nat.le_refl _, Nat.zero_lt_one, a⟩
    · exact ⟨⟨0, room⟩, 1, Nat.le_refl _, Nat.zero_lt_one, a⟩
    · exact ⟨⟨0, room⟩, 2, Nat.le_refl _, Nat.zero_lt_one, a⟩
  · exact .header

private theorem trail_scope : Writes term map frame.solver agenda trail (NativeBindingPublish.header trail) := by
  -- The trial touches just the trail header, independently of any agenda write.
  exact .trailHeader

private theorem termNode_apart (space : Geometry term map frame agenda trail image base) (room : 0 < ac) (i : Fin nc) (j : Fin 4) :
    Disjoint (nodeBytes term i j) (bytes frame agenda trail room) := by
  have field (col : Fin 3) : Disjoint (nodeBytes term i j) (footprint ((agenda.record ⟨0, room⟩).cell col).address) :=
    (agenda.words.separate_arenas term.nodes space.solver.substitute.agendaNode 3 3 (4 * i.val) 4
      (by decide) (by decide) (by omega) (by have := i.isLt; omega) (by decide) (by decide) col j).symm
  have saved (k : Fin 16) : Disjoint (nodeBytes term i j) (footprint (frame.cell k).address) := by
    rw [← frame.as_slice]
    exact (frame.region.separate_arenas term.nodes space.frameNode 0 16 (4 * i.val) 4
      (by decide) (by decide) (by decide) (by have := i.isLt; omega) (by decide) (by decide) k j).symm
  have header := Finset.disjoint_union_right.mp (space.solver.publishGeometry.node i j)
  simp only [bytes, seedBytes, activeLengths, Finset.disjoint_union_right]
  exact ⟨⟨⟨⟨field 0, field 1, field 2⟩, header.2⟩, header.1⟩, saved 3, saved 4⟩

private theorem termEdge_apart (space : Geometry term map frame agenda trail image base) (room : 0 < ac) (i : Fin ec) :
    Disjoint (edgeBytes term i) (bytes frame agenda trail room) := by
  have field (col : Fin 3) : Disjoint (edgeBytes term i) (footprint ((agenda.record ⟨0, room⟩).cell col).address) :=
    (agenda.words.separate_arenas term.edges space.solver.substitute.agendaEdge 3 3 i.val 1
      (by decide) (by decide) (by omega) i.isLt (by decide) (by decide) col 0).symm
  have saved (k : Fin 16) : Disjoint (edgeBytes term i) (footprint (frame.cell k).address) := by
    rw [← frame.as_slice]
    exact (frame.region.separate_arenas term.edges space.frameEdge 0 16 i.val 1
      (by decide) (by decide) (by decide) i.isLt (by decide) (by decide) k 0).symm
  have header := Finset.disjoint_union_right.mp (space.solver.publishGeometry.edge i)
  simp only [bytes, seedBytes, activeLengths, Finset.disjoint_union_right]
  exact ⟨⟨⟨⟨field 0, field 1, field 2⟩, header.2⟩, header.1⟩, saved 3, saved 4⟩

set_option maxHeartbeats 1500000 in
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {start : ℕ} {before : Native} (point : At image before base start) (controls : Controls before)
    (placed : Placed image start) (space : Geometry term map frame agenda trail image base)
    (source : PackedTerms.Arena) (input : Ready term map frame agenda trail source before)
    (left right : Word) (leftWord : lookup before 1 = some left) (rightWord : lookup before 2 = some right)
    (room : 0 < ac) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 18).run before = .ok () after ∧
      X86StateFrame.Frame clobbers (bytes frame agenda trail room) before after ∧
      Writes term map frame.solver agenda trail (bytes frame agenda trail room) ∧
      ∃ seed : Resident term map frame.solver agenda trail ⟨source, [(left, right)], []⟩ after,
        seed.equations.size = 1 ∧ seed.bindings.size = 0 ∧ Nonempty (At image after base (start + 105)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := placed.extent
  obtain ⟨a, opened, opening, stackKnown, ⟨atLoads⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector point (by omega) 4 6 frame.pointer input.stack placed.stack
  have openingFrame := X86StateFrame.registerOnly opening
  let reads := loads frame term agenda trail source
  have stored (item : NativeLoads.Load stackBase frame.pointer) (fetched : item ∈ reads) : Reads a item.cell.address item.value := by
    simp only [reads, loads, List.mem_cons, List.not_mem_nil, or_false] at fetched
    rcases fetched with rfl | rfl | rfl | rfl | rfl
    · exact (input.saved 8 (by decide) (by decide)).preserved openingFrame (by simp)
    · exact (input.saved 9 (by decide) (by decide)).preserved openingFrame (by simp)
    · exact (input.saved 10 (by decide) (by decide)).preserved openingFrame (by simp)
    · exact (input.saved 2 (by decide) (by decide)).preserved openingFrame (by simp)
    · exact (input.saved 7 (by decide) (by decide)).preserved openingFrame (by simp)
  obtain ⟨b, fetched, readFrame, values, ⟨atAgenda⟩⟩ := NativeLoads.fetched other extra vector
    atLoads (controls.transport openingFrame (by decide)) reads (by change start + 3 + 35 ≤ image.size; omega)
    placed.load stackKnown stored (by simp [reads, loads, load])
  have readRegs : NativeLoads.clobbers reads = ({.r15, .r10, .rbp, .rbx, .r9, .rip} : Finset Register) := by
    have registerSets : NativeLoads.clobbers reads =
        ({key 15, .rip} ∪ ({key 10, .rip} ∪ ({key 5, .rip} ∪ ({key 3, .rip} ∪ ({key 9, .rip} ∪ ∅))))) := rfl
    rw [registerSets]
    decide
  rw [readRegs] at readFrame
  have agendaKnown := values (load frame 5 (by decide) 10 agenda.words.pointer) (by simp [reads, loads])
  have termKnown := values (load frame 3 (by decide) 2 term.nodes.pointer) (by simp [reads, loads])
  have trailKnown := values (load frame 9 (by decide) 7 trail.words.pointer) (by simp [reads, loads])
  have nodes := values (load frame 15 (by decide) 8 (BitVec.ofNat 64 source.nodes.size)) (by simp [reads, loads])
  have edges := values (load frame 10 (by decide) 9 (BitVec.ofNat 64 source.children.size)) (by simp [reads, loads])
  have first := openingFrame.trans readFrame
  obtain ⟨c, ready, agendaMove, address, ⟨atSeed⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector (show At image b base (start + 38) from atAgenda) (by omega)
    5 6 agenda.words.pointer agendaKnown placed.agenda
  have startStores := first.trans (X86StateFrame.registerOnly agendaMove)
  let bank := agendaBank agenda room
  let seed := seedWrites bank left right
  have operand (w : NativeStores.Write bank.pointer) (found : w ∈ seed) : lookup c w.source = some w.value := by
    simp only [seed, seedWrites, List.mem_cons, List.not_mem_nil, or_false] at found
    rcases found with rfl | rfl | rfl | rfl
    · exact (startStores.lookup 12 (by decide)).trans input.zero
    · exact (startStores.lookup 1 (by decide)).trans leftWord
    · exact (startStores.lookup 2 (by decide)).trans rightWord
    · exact (startStores.lookup 13 (by decide)).trans input.one
  have seedApart : CodeApart image base (NativeStores.written seed) := by
    rw [seed_effect]
    intro i byte defined hit
    simp only [seedBytes, Finset.mem_union] at hit
    rcases hit with ((a | a | a) | a)
    · exact space.solver.agendaCode ⟨0, room⟩ 0 i byte defined a
    · exact space.solver.agendaCode ⟨0, room⟩ 1 i byte defined a
    · exact space.solver.agendaCode ⟨0, room⟩ 2 i byte defined a
    · exact space.solver.agendaHeader i byte defined a
  have separated : NativeStores.Separate seed := separate_writes bank [(3, 12, 0), (4, 1, left), (5, 2, right), (0, 13, 1)]
    (by change ([3, 4, 5, 0] : List (Fin 6)).Nodup; decide)
  obtain ⟨d, seeded, seededFrame, setFields, ⟨atTrail⟩⟩ := NativeStores.fetched (handlers other extra)
    vector encoding seed atSeed (controls.transport startStores (by decide))
    (NativeStores.checked_of_emitted encoding image _ _ (by change start + 41 + 28 ≤ image.size; omega) placed.seed)
    ((agendaBank_pointer agenda room).symm ▸ address) operand separated seedApart
  rw [seed_effect] at seededFrame
  have throughSeed := startStores.trans seededFrame
  obtain ⟨e, trailMoved, trailMove, toTrail, ⟨atClear⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector (show At image d base (start + 69) from atTrail) (by omega)
    9 6 trail.words.pointer (((X86StateFrame.registerOnly agendaMove).trans seededFrame).lookup 9 (by decide) |>.trans trailKnown) placed.trail
  have beforeClear := throughSeed.trans (X86StateFrame.registerOnly trailMove)
  obtain ⟨f, cleared, clearFrame, empty, ⟨atStack⟩⟩ := X86PlacedMemory.stores (handlers other extra)
    vector (show At image e base (start + 72) from atClear) (controls.transport beforeClear (by decide))
    encoding 12 0 trail.header.pointer 0 (trail.header.cell 0) (trail.header_pointer.symm ▸ toTrail)
    ((beforeClear.lookup 12 (by decide)).trans input.zero) (show start + 79 ≤ image.size by omega)
    placed.clear space.solver.trailHeader
  have throughClear := beforeClear.trans clearFrame
  obtain ⟨g, restacked, restack, stackAgain, ⟨atLengths⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector (show At image f base (start + 79) from atStack) (by omega)
    4 6 frame.pointer ((throughClear.lookup 4 (by decide)).trans input.stack) placed.restack
  have keepAfterLoad :=
    ((((X86StateFrame.registerOnly agendaMove).trans seededFrame).trans (X86StateFrame.registerOnly trailMove)).trans clearFrame).trans
      (X86StateFrame.registerOnly restack)
  have beforeLengths := throughClear.trans (X86StateFrame.registerOnly restack)
  let lengths := lengthWrites frame source
  have apartLengths : CodeApart image base (NativeStores.written lengths) := by
    have effect : NativeStores.written lengths = activeLengths frame := by simp [lengths, lengthWrites, wordWrite, NativeStores.written, activeLengths]
    rw [effect, NativeGuardWorkspace.activeLengths_eq]
    exact space.solver.substitute.lengthCode
  obtain ⟨h, sized, lengthFrame, sizes, ⟨atRoot⟩⟩ := NativeStores.fetched (handlers other extra)
    vector encoding lengths atLengths (controls.transport beforeLengths (by decide))
    (NativeStores.checked_of_emitted encoding image _ _ (by change start + 82 + 14 ≤ image.size; omega) placed.lengths) stackAgain
    (by intro item member; simp only [lengths, lengthWrites, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact (keepAfterLoad.lookup 15 (by decide)).trans nodes
        · exact (keepAfterLoad.lookup 10 (by decide)).trans edges)
    (separate_writes frame [(3, 15, BitVec.ofNat 64 source.nodes.size), (4, 10, BitVec.ofNat 64 source.children.size)]
      (by change ([3, 4] : List (Fin 16)).Nodup; decide))
    apartLengths
  have lengthEffect : NativeStores.written lengths = activeLengths frame := by
    simp [lengths, lengthWrites, wordWrite, NativeStores.written, activeLengths]
  rw [lengthEffect] at lengthFrame
  have throughLengths := beforeLengths.trans lengthFrame
  obtain ⟨k, rooted, rooting, root, ⟨atTag⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector (show At image h base (start + 96) from atRoot) (by omega)
    13 11 1 ((throughLengths.lookup 13 (by decide)).trans input.one) placed.root
  obtain ⟨after, tagged, tagging, tag, endpoint⟩ := X86PlacedScalar.rex_immediate (X86PlacedFrameAddress.nativeBase other)
    extra vector atTag extent 14 2 placed.tag
  have last := X86StateFrame.registerOnly (rooting.trans tagging)
  have all : X86StateFrame.Frame clobbers (bytes frame agenda trail room) before after :=
    (throughLengths.trans last).mono (by decide) (by
      simp only [bytes, NativeBindingPublish.header, Finset.empty_union, Finset.union_empty]
      exact Finset.Subset.refl _)
  have writes : Writes term map frame.solver agenda trail (bytes frame agenda trail room) :=
    .union (.union (seed_scope room) trail_scope)
      (.graph (by rw [NativeGuardWorkspace.activeLengths_eq]; exact NativeSubstitutionMemory.Includes.lengths term map frame.solver.substitution))
  have graph := input.sourceReady.kept all (termNode_apart space room) (termEdge_apart space room)
  have kept := input.afterTrial space all writes graph (by decide) (by decide) ((all.lookup 13 (by decide)).trans input.one)
  have nodeCount := sizes (wordWrite frame 15 3 (BitVec.ofNat 64 source.nodes.size)) List.mem_cons_self
  have edgeCount := sizes (wordWrite frame 10 4 (BitVec.ofNat 64 source.children.size)) (by simp [lengths, lengthWrites])
  have state : NativeSubstitutionFrame.Ready term map frame.solver.substitution source after := by
    refine ⟨frame.solver.substitution_pointer.symm ▸ (frame.solver_pointer.symm ▸ kept.stack), ?_⟩
    intro i
    rw [frame.staged_cell]
    fin_cases i
    · exact kept.saved 0 (by decide) (by decide)
    · exact kept.saved 1 (by decide) (by decide)
    · exact kept.saved 2 (by decide) (by decide)
    · exact nodeCount.preserved last (by simp)
    · exact edgeCount.preserved last (by simp)
    · exact kept.saved 5 (by decide) (by decide)
    · exact kept.saved 6 (by decide) (by decide)
  have later := (((X86StateFrame.registerOnly trailMove).trans clearFrame).trans (X86StateFrame.registerOnly restack)).trans
    (lengthFrame.trans last)
  have acrossSeed {held : Finset ℕ} (head : Disjoint held (NativeBindingPublish.header trail))
      (stack : Disjoint held (activeLengths frame)) : Disjoint held
        ((∅ ∪ footprint (trail.header.cell 0).address ∪ ∅) ∪ (activeLengths frame ∪ ∅)) := by
    simpa only [Finset.empty_union, Finset.union_empty, NativeBindingPublish.header] using
      Finset.disjoint_union_right.mpr ⟨head, stack⟩
  have frameApart (j : Fin 3) : Disjoint (footprint ((agenda.record ⟨0, room⟩).cell j).address) (activeLengths frame) :=
    Finset.disjoint_union_right.mpr ⟨(Geometry.frame_record space.frameAgenda 3 ⟨0, room⟩ j).symm,
      (Geometry.frame_record space.frameAgenda 4 ⟨0, room⟩ j).symm⟩
  have headerApart : Disjoint (NativeBindingPublish.header agenda) (activeLengths frame) :=
    Finset.disjoint_union_right.mpr ⟨(Geometry.frame_header space.frameAgenda 3).symm, (Geometry.frame_header space.frameAgenda 4).symm⟩
  have agendaReady : NativeAgendaRecords.Ready agenda #[equation left right] after := by
    have countSet := setFields (wordWrite bank 13 0 1) (by simp [seed, seedWrites])
    change Reads d ((agendaBank agenda room).cell 0).address 1 at countSet
    rw [seed_header] at countSet
    refine ⟨show 1 ≤ ac by omega, countSet.preserved later (acrossSeed (NativeBindingMemory.header_apart space.solver.trailAgenda.symm)
      headerApart), ?_⟩
    intro i j
    have isZero : i.val = 0 := by have small := i.isLt; change i.val < 1 at small; omega
    have indexOf : (⟨i.val, i.isLt.trans_le (show (#[equation left right] : PackedEquations.Arena).size ≤ ac from room)⟩ : Fin ac) =
        ⟨0, room⟩ := Fin.ext isZero
    have known := setFields (seedField bank left right j) (by fin_cases j <;> simp [seed, seedWrites])
    change Reads d ((agendaBank agenda room).cell (seedSlot j)).address (NativeAgendaRecords.field (equation left right) j) at known
    rw [seed_cell] at known
    rw [indexOf]
    have eqNode : (#[equation left right] : PackedEquations.Arena)[i] = equation left right := by
      have first : i = 0 := Fin.ext isZero
      subst i
      rfl
    rw [eqNode]
    exact known.preserved later (acrossSeed (NativeBindingMemory.record_header_apart space.solver.trailAgenda.symm _ j) (frameApart j))
  have emptyTrail : NativeAgendaRecords.Ready trail #[] after := by
    refine ⟨Nat.zero_le _, empty.preserved (((X86StateFrame.registerOnly restack).trans lengthFrame).trans last) ?_, fun i => Fin.elim0 i⟩
    simp only [Finset.empty_union, Finset.union_empty, activeLengths, Finset.disjoint_union_right]
    exact ⟨(Geometry.frame_header space.frameTrail 3).symm, (Geometry.frame_header space.frameTrail 4).symm⟩
  have afterRegisters := keepAfterLoad.trans (lengthFrame.trans last)
  have context : NativeAgendaDispatch.Context agenda term #[equation left right] source 1 after :=
    ⟨agendaReady, graph, (afterRegisters.lookup 5 (by decide)).trans agendaKnown, (afterRegisters.lookup 3 (by decide)).trans termKnown,
      (tagging.lookup 11 (by decide)).trans root, (afterRegisters.lookup 15 (by decide)).trans nodes, kept.zero, kept.one, tag⟩
  have trailPtr := kept.saved 7 (by decide) (by decide)
  have live : NativeBindingStep.Live term map frame.solver agenda trail source #[equation left right] 1 #[] after :=
    ⟨context, state, emptyTrail, kept.pool, kept.agendaLimit, kept.trailLimit, by rw [frame.solver_cell]; exact trailPtr⟩
  let seedState : Resident term map frame.solver agenda trail ⟨source, [(left, right)], []⟩ after :=
    ⟨#[equation left right], #[], 1, live, by rfl, rfl⟩
  have throughLoad := X86FuelPrefix.fetches_then 1 5 before a b opened fetched
  have throughSeedRun := X86FuelPrefix.fetches_then 7 4 before c d
    (X86FuelPrefix.fetches_then 6 1 before b c throughLoad ready) seeded
  have throughClearRun := X86FuelPrefix.fetches_then 12 1 before e f
    (X86FuelPrefix.fetches_then 11 1 before d e throughSeedRun trailMoved) cleared
  have stagedRun := X86FuelPrefix.fetches_then 14 2 before g h
    (X86FuelPrefix.fetches_then 13 1 before f g throughClearRun restacked) sized
  exact ⟨after, X86FuelPrefix.fetches_then 17 1 before k after
    (X86FuelPrefix.fetches_then 16 1 before h k stagedRun rooted) tagged, all, writes, seedState, rfl, rfl, endpoint⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardTrial
