import Mettapedia.Machines.TIsa.StoreInstructions.NativeLiveRootLoop
import Mettapedia.Machines.TIsa.StoreInstructions.NativeTrailReserve

/-!
# Entering the live-root pass after a binding

The ordinary solver descriptor is the first eight words.
The root pointer and length follow the sixteen-word guard
prefix, so a later observer can borrow a different window
without rebuilding that directory. The completed map is
already in the registers left by the graph traversal.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeLiveRootEntry

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads)
open X86PlacedScalar (Code registerCode)
open NativeArenaGeometry (Region)
open NativeSubstLeaf (MapReady)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev Descriptor := WordRegion.Region 18

def Descriptor.region (d : Descriptor) : Region 18 := ⟨d.pointer, d.aligned, d.area⟩

def Descriptor.solver (d : Descriptor) : NativeTrailReserve.Descriptor :=
  d.region.slice 0 8 (by decide) (by decide) (by decide)

theorem Descriptor.solver_pointer (d : Descriptor) : d.solver.pointer = d.pointer := BitVec.add_zero _

theorem Descriptor.cell_of_solver (d : Descriptor) (i : Fin 8) :
    (d.solver.cell i).address = (d.cell ⟨i.val, i.isLt.trans (by decide)⟩).address := by
  rw [Descriptor.solver, Region.slice_address, Nat.zero_add]
  rfl

def stackCode : List ℕ := registerCode 0x89 4 2
def limitCode : List ℕ := X86DataLoad.code true 14 2 136
def baseCode : List ℕ := X86DataLoad.code true 6 2 128
def cursorCode : List ℕ := registerCode 0x89 12 1

def emit : List ℕ := stackCode ++ (limitCode ++ (baseCode ++ cursorCode))

theorem emit_size : emit.length = 20 := rfl

structure Placed (image : NativeImage.View) (start : ℕ) : Prop where
  extent : start + 20 ≤ image.size
  stack : Code image start stackCode
  limit : Code image (start + 3) limitCode
  roots : Code image (start + 10) baseCode
  cursor : Code image (start + 17) cursorCode

theorem placed_of_emitted (image : NativeImage.View) (start : ℕ) (extent : start + 20 ≤ image.size)
    (code : Code image start emit) : Placed image start := by
  obtain ⟨stack, rest⟩ := NativeWords.code_append (show Code image start (stackCode ++ _) from code)
  obtain ⟨limit, rest⟩ := NativeWords.code_append rest
  obtain ⟨roots, cursor⟩ := NativeWords.code_append rest
  exact ⟨extent, stack, limit, roots, cursor⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers

abbrev clobbers : Finset Register := {.rcx, .rdx, .rsi, .r14, .rip}

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

private def limitWire : NativeWords.Wiring := ⟨2, by decide, by decide, MemoryBinding.storeEncoding, 14, by decide, by decide⟩
private def baseWire : NativeWords.Wiring :=
  ⟨2, by decide, by decide, .direct 7 (by decide) (by decide), 6, by decide, by decide⟩

variable {rc mc : ℕ} {roots : Region rc} {map : Region mc}
variable {old translated : Array Word} {image : NativeImage.View} {base : BitVec 48}

structure Metadata (d : Descriptor) (roots : Region rc) (count : ℕ) (native : Native) : Prop where
  pointer : Reads native (d.cell 16).address (roots.atWord 0)
  length : Reads native (d.cell 17).address (BitVec.ofNat 64 count)

structure Held (d : Descriptor) (roots : Region rc) (words : Array Word) (native : Native) : Prop where
  descriptor : Metadata d roots words.size native
  words : MapReady roots words native

theorem Metadata.kept {d : Descriptor} {count : ℕ} {R : Finset Register} {bytes : Finset ℕ} {before after : Native}
    (read : Metadata d roots count before) (run : X86StateFrame.Frame R bytes before after)
    (pointer : Disjoint (X86PlacedMemory.footprint (d.cell 16).address) bytes)
    (length : Disjoint (X86PlacedMemory.footprint (d.cell 17).address) bytes) :
    Metadata d roots count after :=
  ⟨read.pointer.preserved run pointer, read.length.preserved run length⟩

/-- Four fetched instructions open the physical vector.
No root, graph entry, or equation is touched by this setup. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {start : ℕ} {before : Native} (point : At image before base start) (controls : Controls before)
    (code : Placed image start) (d : Descriptor)
    (held : Held d roots old before) (mapped : MapReady map translated before)
    (stack : lookup before 4 = some d.pointer) (mapBase : lookup before 7 = some (map.atWord 0))
    (mapLimit : lookup before 15 = some (BitVec.ofNat 64 translated.size))
    (zero : lookup before 12 = some 0) (one : lookup before 13 = some 1) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 4).run before = .ok () after ∧ X86StateFrame.Frame clobbers ∅ before after ∧
      NativeLiveRootLoop.Ready roots map old translated 0 old.size after ∧ Nonempty (At image after base (start + 20)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := code.extent
  obtain ⟨a, opened, move, address, ⟨atLimit⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector point (by omega) 4 2 d.pointer stack code.stack
  have startFrame := X86StateFrame.registerOnly move
  obtain ⟨b, limited, limitFrame, last, ⟨atRoots⟩⟩ := (NativeAgendaRead.fieldSource d 17).fetch
    (handlers other extra) vector limitWire (BitVec.ofNat 64 old.size) atLimit
    (controls.transport startFrame (by decide)) address (held.descriptor.length.preserved startFrame (by simp))
    (show start + 10 ≤ image.size by omega) code.limit
  have two := startFrame.trans limitFrame
  obtain ⟨c, selected, rootFrame, rootBase, ⟨atCursor⟩⟩ := (NativeAgendaRead.fieldSource d 16).fetch
    (handlers other extra) vector baseWire (roots.atWord 0) (show At image b base (start + 10) from atRoots)
    (controls.transport two (by decide)) ((limitFrame.lookup 2 (by decide)).trans address)
    (held.descriptor.pointer.preserved two (by simp)) (show start + 17 ≤ image.size by omega) code.roots
  have three := two.trans rootFrame
  obtain ⟨after, cleared, cursorFrame, cursor, done⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector (show At image c base (start + 17) from atCursor) (by omega)
    12 1 0 ((three.lookup 12 (by decide)).trans zero) code.cursor
  have fourth := X86StateFrame.registerOnly cursorFrame
  have all : X86StateFrame.Frame clobbers ∅ before after := (three.trans fourth).mono (by decide) (by simp)
  have linked : NativeWords.handlers (handlers other extra) = handlers other extra := rfl
  rw [linked] at limited selected
  have ran := X86FuelPrefix.fetches_then 3 1 before c after
    (X86FuelPrefix.fetches_then 2 1 before b c (X86FuelPrefix.fetches_then 1 1 before a b opened limited) selected) cleared
  exact ⟨after, ran, all,
    ⟨⟨held.words.preserved all, mapped.preserved all, (fourth.lookup 6 (by decide)).trans rootBase,
      (all.lookup 7 (by decide)).trans mapBase, cursor, (all.lookup 15 (by decide)).trans mapLimit⟩,
      ((rootFrame.trans fourth).lookup 14 (by decide)).trans last, (all.lookup 13 (by decide)).trans one⟩, done⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeLiveRootEntry
