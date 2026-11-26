import Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardReuse
import Mettapedia.Machines.TIsa.StoreInstructions.NativeRootedSolverStep

/-!
# Selecting an all-solutions observer

The first observer captures the checkpoint. A later
observer on the same snapshot changes only the pattern.
Both leave the same stable scan interface.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeObserverSelect

open _root_.X86Registers X86Execution X86RegisterRefinement
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls CodeApart footprint)
open X86PlacedScalar (Code)
open NativeArenaGeometry (Region)
open NativeBindingSelection (Separated)
open NativeBindingRootMemory (Covered External)
open NativeLiveRootEntry (Descriptor Held)
open NativeGuardWorkspace (Frame)
open NativeGuardInstall (guardFrame slotBytes slots_cover descriptorBytes)
open NativeGuardState (Geometry Stable counters)
open NativeRootSlices (View)
open NativeSolverStep (Writes)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

inductive Mode where
  | first | reuse
  deriving DecidableEq

def Mode.size : Mode → ℕ | .first => 104 | .reuse => 38
def Mode.cost : Mode → ℕ | .first => 15 | .reuse => 6
def Mode.writes (mode : Mode) (frame : Frame) : Finset ℕ :=
  match mode with | .first => descriptorBytes frame | .reuse => slotBytes frame 11

def emit (mode : Mode) (pattern offset count : ℕ) : List ℕ :=
  match mode with
  | .first => NativeGuardInstall.emit pattern offset count
  | .reuse => NativeGuardInstall.emitNeedle pattern

theorem emit_size (mode : Mode) (pattern offset count : ℕ) : (emit mode pattern offset count).length = mode.size := by
  cases mode <;> rfl

def Placed (image : NativeImage.View) (start pattern offset count : ℕ) : Mode → Prop
  | .first => NativeGuardInstall.Placed image start pattern offset count
  | .reuse => NativeGuardInstall.NeedlePlaced image start pattern

theorem placed_of_emitted (image : NativeImage.View) (mode : Mode) (start pattern offset count : ℕ)
    (extent : start + mode.size ≤ image.size) (code : Code image start (emit mode pattern offset count)) :
    Placed image start pattern offset count mode := by
  cases mode
  · exact NativeGuardInstall.placed_of_emitted image _ _ _ _ extent code
  · exact NativeGuardInstall.needle_placed image _ _ extent code

variable {nc ec mc ac tc rc : ℕ}
variable {term : NativeTermArena.Layout nc ec} {map : Region mc}
variable {agenda : NativeAgendaRecords.Layout ac} {trail : NativeAgendaRecords.Layout tc}
variable {r : Region rc} {words : Array Word} {capacity : words.size ≤ rc} {image : NativeImage.View} {base : BitVec 48}

inductive Ready (term : NativeTermArena.Layout nc ec) (map : Region mc) (d : Descriptor)
    (agenda : NativeAgendaRecords.Layout ac) (trail : NativeAgendaRecords.Layout tc)
    (r : Region rc) (words : Array Word) (capacity : words.size ≤ rc)
    (graph : PackedTerms.Arena) (view : View words) (native : Native) : Mode → Prop
  | first : NativeGuardInstall.Input term map (guardFrame d) agenda trail d r graph words native →
      Ready term map d agenda trail r words capacity graph view native .first
  | reuse (old : Word) : Held d r words native →
      Stable term map (guardFrame d) agenda trail (view.region r capacity) graph old view.occurrences native →
      Ready term map d agenda trail r words capacity graph view native .reuse

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers := NativeGuardInstall.clobbers
theorem clobbers_data : clobbers ⊆ dataRegisters := NativeGuardInstall.clobbers_data

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {start : ℕ} {before : Native} (mode : Mode) (d : Descriptor) (view : View words)
    (code : Placed image start view.pattern.val view.offset view.count mode)
    (point : At image before base start) (controls : Controls before) (graph : PackedTerms.Arena)
    (input : Ready term map d agenda trail r words capacity graph view before mode)
    (space : Geometry term map (guardFrame d) agenda trail (view.region r capacity) image base)
    (apart : Separated r (guardFrame d).region) (safe : CodeApart image base (mode.writes (guardFrame d))) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches mode.cost).run before = .ok () after ∧
      X86StateFrame.Frame clobbers (mode.writes (guardFrame d)) before after ∧
      Stable term map (guardFrame d) agenda trail (view.region r capacity) graph view.needle view.occurrences after ∧
      Held d r words after ∧ Nonempty (At image after base (start + mode.size)) := by
  cases input with
  | first input => exact NativeGuardInstall.fetched other extra vector view code point controls graph input space apart safe
  | reuse old input ready => exact NativeGuardReuse.fetched other extra vector view code point controls rfl input graph old space ready apart safe

private theorem far_slot (d : Descriptor) (i : Fin 18) (outside : 16 ≤ i.val) (j : Fin 16) :
    Disjoint (footprint (d.cell i).address) (slotBytes (guardFrame d) j) := by
  rw [slotBytes, NativeGuardInstall.guard_field]
  refine d.separate_words ?_
  intro same
  have v : i.val = j.val := congrArg Fin.val same
  have range := j.isLt
  omega

/-- The held root directory survives an observer's workspace
and scan writes, plus an optional private collection mask
in another separated bank. -/
theorem keep_roots {d : Descriptor} {before after : Native} {regs : Finset Register} {work marks : Finset ℕ}
    (space : NativeBindingRootMemory.Geometry r d term map agenda trail image base)
    (apart : Separated r (guardFrame d).region) (held : Held d r words before)
    (effects : Writes term map (guardFrame d).solver agenda trail work)
    (avoidRoot : ∀ i : Fin rc, Disjoint (footprint ((r.wordCell i).cell 0).address) marks)
    (avoidDesc : ∀ i : Fin 18, 16 ≤ i.val → Disjoint (footprint (d.cell i).address) marks)
    (run : X86StateFrame.Frame regs ((work ∪ marks) ∪ counters (guardFrame d)) before after) :
    Held d r words after := by
  have same : d.solver = (guardFrame d).solver := NativeGuardInstall.root_solver d
  have touched : Writes term map d.solver agenda trail work := same.symm ▸ effects
  have field (i : Fin 18) (far : 16 ≤ i.val) : Disjoint (footprint (d.cell i).address) ((work ∪ marks) ∪ counters (guardFrame d)) := by
    have nodes : i ≠ 3 := fun same => by rw [same] at far; exact (by decide : ¬16 ≤ (3 : Fin 18).val) far
    have edges : i ≠ 4 := fun same => by rw [same] at far; exact (by decide : ¬16 ≤ (4 : Fin 18).val) far
    exact Finset.disjoint_union_right.mpr ⟨Finset.disjoint_union_right.mpr ⟨
        NativeRootedSolverStep.keep_writes space.descriptor (Covered.field d i)
          (NativeBindingRootMemory.descriptor_lengths d i nodes edges) touched, avoidDesc i far⟩,
      Finset.disjoint_union_right.mpr ⟨far_slot d i far 14, far_slot d i far 15⟩⟩
  have root (i : Fin rc) :
      Disjoint (footprint ((r.wordCell i).cell 0).address) ((work ∪ marks) ∪ counters (guardFrame d)) :=
    Finset.disjoint_union_right.mpr ⟨Finset.disjoint_union_right.mpr ⟨
      NativeRootedSolverStep.keep_writes space.rootSpace (Covered.word r i)
        (NativeBindingRootMemory.root_lengths d space.rootFrame i) touched, avoidRoot i⟩,
      Covered.separate apart (Covered.word r i) ((slots_cover (guardFrame d) 14).union (slots_cover (guardFrame d) 15))⟩
  exact ⟨held.descriptor.kept run (field 16 (by decide)) (field 17 (by decide)), held.words.kept run root⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeObserverSelect
