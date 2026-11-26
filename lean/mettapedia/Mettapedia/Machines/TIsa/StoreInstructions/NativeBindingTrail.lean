import Mettapedia.Machines.TIsa.StoreInstructions.NativeTrailReserve
import Mettapedia.Machines.TIsa.StoreInstructions.NativeRegisterCopies
import Mettapedia.Machines.TIsa.StoreInstructions.NativePendingFill

/-!
# Staging the newest binding before reusing its registers

The solver uses the same three-word packed record for an
equation and for a trail entry. This operation leaves both
live lengths alone. Restoring the ordinary agenda cursor
makes it possible to remap that agenda using the same registers
for the next phase.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeBindingTrail

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads CodeApart footprint)
open X86PlacedScalar (Code)
open NativeTrailReserve (Descriptor)
open NativeAgendaRecords (Ready Records)
open NativeAgendaLoop (Within)
open PackedEquations (Arena Node readWords)
open PackedWorklist (Words)
open NativeRegisterCopies (Copy Values)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def prepare : List Copy := [⟨5, 7⟩, ⟨11, 3⟩, ⟨2, 5⟩, ⟨14, 11⟩, ⟨9, 10⟩, ⟨8, 9⟩]
def restore : List Copy := [⟨7, 5⟩, ⟨3, 11⟩, ⟨4, 6⟩]
def mapCode : List ℕ := X86DataLoad.code true 7 6 0
def mapWire : NativeWords.Wiring := ⟨6, by decide, by decide, MemoryBinding.storeEncoding, 7, by decide, by decide⟩

def emit (start exhausted : ℕ) : List ℕ :=
  NativeTrailReserve.emit start exhausted ++ (NativeRegisterCopies.emit prepare ++
    (NativeAgendaInsert.emit ++ (NativeRegisterCopies.emit restore ++ mapCode)))

theorem emit_size (start exhausted : ℕ) : (emit start exhausted).length = 108 := by
  simp only [emit, List.length_append, NativeTrailReserve.emit_size, NativeRegisterCopies.emit_size, NativeAgendaInsert.emit_size,
    show prepare.length = 6 from rfl, show restore.length = 3 from rfl, show mapCode.length = 7 from rfl]

structure Placed (image : NativeImage.View) (start exhausted : ℕ) : Prop where
  extent : start + 108 ≤ image.size
  reserve : NativeTrailReserve.Placed image start exhausted
  prepare : Code image (start + 33) (NativeRegisterCopies.emit prepare)
  insert : NativeAgendaInsert.Placed image (start + 51)
  restore : Code image (start + 92) (NativeRegisterCopies.emit restore)
  map : Code image (start + 101) mapCode

theorem placed_of_emitted (image : NativeImage.View) (start exhausted : ℕ)
    (extent : start + 108 ≤ image.size) (lack : exhausted ≤ image.size) (short : image.size < 2 ^ 31)
    (code : Code image start (emit start exhausted)) : Placed image start exhausted := by
  obtain ⟨reserve, rest⟩ := NativeWords.code_append (show Code image start (NativeTrailReserve.emit start exhausted ++ _) from code)
  rw [NativeTrailReserve.emit_size] at rest
  obtain ⟨before, rest⟩ := NativeWords.code_append rest
  rw [NativeRegisterCopies.emit_size] at rest
  obtain ⟨record, rest⟩ := NativeWords.code_append rest
  rw [NativeAgendaInsert.emit_size] at rest
  obtain ⟨after, map⟩ := NativeWords.code_append rest
  rw [NativeRegisterCopies.emit_size] at map
  exact ⟨extent, NativeTrailReserve.placed_of_emitted image _ exhausted (by omega) lack short reserve, before,
    NativeAgendaInsert.placed_of_emitted image _ (by omega) record, after, map⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers : Finset Register :=
  {.rax, .rbx, .rdx, .rsi, .rdi, .rbp, .r9, .r10, .r11, .r14, .rflags, .rip}
theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

variable {capacity : ℕ} {layout : NativeAgendaRecords.Layout capacity} {arena : Arena} {frame : Descriptor}
variable {image : NativeImage.View} {base : BitVec 48}

def root (arena : Arena) : Word := BitVec.ofNat 64 arena.size
def binding (arena : Arena) (name replacement : Word) : Node := ⟨root arena, name, replacement⟩

structure Geometry (layout : NativeAgendaRecords.Layout capacity) (frame : Descriptor)
    (image : NativeImage.View) (base : BitVec 48) : Prop where
  code : ∀ i j, CodeApart image base (footprint ((layout.record i).cell j).address)
  descriptor : NativeBindingSelection.Separated layout.words frame.region

theorem Geometry.frame_apart (space : Geometry layout frame image base) (i : Fin 8) (record : Fin capacity) (j : Fin 3) :
    Disjoint (footprint (frame.cell i).address) (footprint ((layout.record record).cell j).address) := by
  have slot : ((frame.region.slice 0 8 (by decide) (by decide) (by decide)).cell i).address = (frame.cell i).address := by
    rw [NativeArenaGeometry.Region.slice_address, Nat.zero_add]
    rfl
  rw [← slot]
  exact (layout.words.separate_arenas frame.region space.descriptor (3 * (record.val + 1)) 3 0 8 (by decide) (by decide)
    (by have bound := record.isLt; omega) (by decide) (by decide) (by decide) j i).symm

structure Input (layout : NativeAgendaRecords.Layout capacity) (frame : Descriptor) (arena : Arena)
    (ordinary cursor map name value : Word) (native : Native) : Prop where
  trail : Ready layout arena native
  pointer : Reads native (frame.cell 7).address layout.words.pointer
  limit : Reads native (layout.metadata.cell 2).address (BitVec.ofNat 64 capacity)
  stack : lookup native 4 = some frame.pointer
  map : Reads native (frame.cell 0).address map
  ordinary : lookup native 5 = some ordinary
  cursor : lookup native 11 = some cursor
  name : lookup native 8 = some name
  replacement : lookup native 9 = some value
  one : lookup native 13 = some 1

private def put (v : Values) (i : Fin 16) (word : Word) : Values := Function.update v i (some word)

private def prepIn (agenda oldCursor trail oldCount name value : Word) : Values :=
  put (put (put (put (put (put (fun _ => none) 5 agenda) 11 oldCursor) 2 trail) 14 oldCount) 9 value) 8 name

private def prepOut (agenda oldCursor trail oldCount name value : Word) : Values :=
  put (put (put (put (put (put (prepIn agenda oldCursor trail oldCount name value) 7 agenda) 3 oldCursor)
    5 trail) 11 oldCount) 10 value) 9 name

private theorem prep_exact (a c t n l r : Word) :
    NativeRegisterCopies.interpret prepare (prepIn a c t n l r) = some (prepOut a c t n l r) := rfl

private def regainIn (agenda cursor stack : Word) : Values := put (put (put (fun _ => none) 7 agenda) 3 cursor) 4 stack
private def regainOut (agenda cursor stack : Word) : Values :=
  put (put (put (regainIn agenda cursor stack) 5 agenda) 11 cursor) 6 stack

private theorem regain_exact (a c s : Word) : NativeRegisterCopies.interpret restore (regainIn a c s) =
    some (regainOut a c s) := rfl

/-- Stage an exact trail append, preserving the previous live
length. Capacity failure branches without any trail store. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start exhausted : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (placed : Placed image start exhausted)
    (space : Geometry layout frame image base) (ordinary cursor map name value : Word)
    (input : Input layout frame arena ordinary cursor map name value before)
    (trail : Words) (history : readWords arena (root arena) = some trail) :
    let node := binding arena name value
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps bytes, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame clobbers bytes before after ∧
      if arena.size < capacity then
        steps = 25 ∧ Within layout arena.size (arena.size + 1) bytes ∧ Ready layout arena after ∧
        Records layout (arena.push node) after ∧ readWords (arena.push node) (root (arena.push node)) = some ((name, value) :: trail) ∧
        lookup after 5 = some ordinary ∧ lookup after 11 = some cursor ∧ lookup after 7 = some map ∧
        Nonempty (At image after base (start + 108))
      else steps = 6 ∧ bytes = ∅ ∧ Nonempty (At image after base exhausted) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let node := binding arena name value
  have extent := placed.extent
  obtain ⟨a, ranReserve, reserveFrame, trailBase, oldLen, ⟨decision⟩⟩ :=
    NativeTrailReserve.fetched other extra vector point controls placed.reserve frame input.stack input.trail input.pointer input.limit
  by_cases room : arena.size < capacity
  · rw [if_pos room] at decision
    let val := prepIn ordinary cursor layout.words.pointer (root arena) name value
    let expected := prepOut ordinary cursor layout.words.pointer (root arena) name value
    have five := (NativeRegisterCopies.Ready.empty a).set 5 ordinary ((reserveFrame.lookup 5 (by decide)).trans input.ordinary)
    have eleven := five.set 11 cursor ((reserveFrame.lookup 11 (by decide)).trans input.cursor)
    have two := eleven.set 2 layout.words.pointer trailBase
    have fourteen := two.set 14 (root arena) oldLen
    have nine := fourteen.set 9 value ((reserveFrame.lookup 9 (by decide)).trans input.replacement)
    have roles : NativeRegisterCopies.Ready val a := nine.set 8 name ((reserveFrame.lookup 8 (by decide)).trans input.name)
    obtain ⟨b, prepared, shuffling, reg, ⟨atInsert⟩⟩ := NativeRegisterCopies.fetched other extra vector
      decision prepare (by change start + 33 + 18 ≤ image.size; omega) placed.prepare val expected roles (prep_exact _ _ _ _ _ _)
    have prior := reserveFrame.trans shuffling
    have entry : NativeAgendaInsert.Inputs layout arena node b :=
      ⟨(input.trail.preserved (prior.mono (Finset.Subset.refl _) (by simp))).records,
        reg 5 layout.words.pointer rfl, (shuffling.lookup 14 (by decide)).trans oldLen,
        (prior.lookup 13 (by decide)).trans input.one, reg 11 (root arena) rfl, reg 9 name rfl, reg 10 value rfl⟩
    let bytes := NativeAgendaInsert.footprintOf layout arena room node
    have confined : Within layout arena.size (arena.size + 1) bytes := by
      intro byte changed
      obtain ⟨j, hit⟩ := NativeAgendaInsert.footprint_member _ _ _ _ changed
      exact ⟨⟨arena.size, room⟩, j, Nat.le_refl _, Nat.lt_succ_self _, hit⟩
    have codeApart : CodeApart image base bytes := by
      intro i value present changed
      obtain ⟨idx, col, _, _, there⟩ := confined _ changed
      exact space.code idx col i value present there
    obtain ⟨c, inserted, insertion, packed, _, _, exactTrail, ⟨atRestore⟩⟩ := NativeAgendaInsert.fetched
      other extra vector (show At image b base (start + 51) from atInsert) (controls.transport prior (by decide))
      placed.insert node entry room trail history (by change (root arena).toNat ≤ arena.size; rw [root, input.trail.count_word])
      codeApart
    have throughInsert : X86StateFrame.Frame clobbers bytes before c :=
      (prior.trans insertion).mono (by decide) (by simp only [Finset.empty_union, bytes]; exact Finset.Subset.refl _)
    let startRestore := regainIn ordinary cursor frame.pointer
    let endRestore := regainOut ordinary cursor frame.pointer
    have seven := (NativeRegisterCopies.Ready.empty c).set 7 ordinary ((insertion.lookup 7 (by decide)).trans (reg 7 ordinary rfl))
    have three := seven.set 3 cursor ((insertion.lookup 3 (by decide)).trans (reg 3 cursor rfl))
    have relevant : NativeRegisterCopies.Ready startRestore c :=
      three.set 4 frame.pointer ((throughInsert.lookup 4 (by decide)).trans input.stack)
    obtain ⟨d, regained, regain, kept, ⟨atMap⟩⟩ := NativeRegisterCopies.fetched other extra vector
      atRestore restore (by change start + 92 + 9 ≤ image.size; omega) placed.restore startRestore endRestore relevant (regain_exact _ _ _)
    have beforeLoad := throughInsert.trans regain
    obtain ⟨after, reread, loaded, mapKnown, endpoint⟩ := (NativeAgendaRead.fieldSource frame 0).fetch
      (handlers other extra) vector mapWire map (show At image d base (start + 101) from atMap)
      (controls.transport beforeLoad (by decide)) (kept 6 frame.pointer rfl)
      (input.map.preserved beforeLoad (by
        simp only [Finset.union_empty]
        exact NativePendingFill.Within.separate confined _ (fun i j _ _ => space.frame_apart 0 i j)))
      extent placed.map
    have linked : NativeWords.handlers (handlers other extra) = handlers other extra := rfl
    rw [linked] at reread
    have final : X86StateFrame.Frame clobbers bytes before after :=
      (beforeLoad.trans loaded).mono (by decide) (by simp)
    have tailFrame := (regain.trans loaded).mono (Finset.Subset.refl _) (by simp : (∅ ∪ ∅ : Finset ℕ) ⊆ ∅)
    have old : Ready layout arena after :=
      ⟨input.trail.fits, input.trail.count.preserved final (NativeAgendaLoop.Within.preserves_count confined),
        fun i j => (input.trail.node i j).preserved final
          (NativePendingFill.Within.separate confined _ (fun k col lower _ =>
            layout.records_apart _ k (i.isLt.trans_le lower) j col))⟩
    have staged : Records layout (arena.push node) after :=
      ⟨packed.fits, fun i j => (packed.node i j).preserved tailFrame (by simp)⟩
    have lastRoot : root (arena.push node) = PackedEquations.next arena := by rw [root, Array.size_push]; rfl
    have executed := X86FuelPrefix.fetches_then 24 1 before d after
      (X86FuelPrefix.fetches_then 21 3 before c d
        (X86FuelPrefix.fetches_then 12 9 before b c
          (X86FuelPrefix.fetches_then 6 6 before a b ranReserve prepared) inserted) regained) reread
    refine ⟨after, 25, bytes, executed, final, ?_⟩
    rw [if_pos room]
    exact ⟨rfl, confined, old, staged, lastRoot.symm ▸ exactTrail,
      (loaded.lookup 5 (by decide)).trans (kept 5 ordinary rfl),
      (loaded.lookup 11 (by decide)).trans (kept 11 cursor rfl), mapKnown, endpoint⟩
  · rw [if_neg room] at decision
    refine ⟨a, 6, ∅, ranReserve, reserveFrame.mono (by decide) (Finset.Subset.refl _), ?_⟩
    rw [if_neg room]
    exact ⟨rfl, rfl, ⟨decision⟩⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeBindingTrail
