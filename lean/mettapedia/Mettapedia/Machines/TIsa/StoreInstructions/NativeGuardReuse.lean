import Mettapedia.Machines.TIsa.StoreInstructions.RootedObserverLayout

/-!
# Reusing a snapshot checkpoint for a different observer

Changing only the pattern changes one descriptor word.
The root window and saved graph lengths survive probes.
In particular a later test does not capture a trial's
larger active term lengths as if it were the original graph.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardReuse

open _root_.X86Registers X86Execution X86RegisterRefinement
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls CodeApart)
open NativeArenaGeometry (Region)
open NativeBindingSelection (Separated)
open NativeBindingRootMemory (Covered)
open NativeLiveRootEntry (Descriptor Held)
open NativeGuardWorkspace (Frame)
open NativeGuardInstall (guardFrame slotBytes slots_cover)
open NativeGuardState (Geometry Stable)
open NativeRootSlices (View)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers := NativeGuardInstall.clobbers

variable {nc ec mc ac tc rc : ℕ}
variable {term : NativeTermArena.Layout nc ec} {map : Region mc} {frame : Frame}
variable {agenda : NativeAgendaRecords.Layout ac} {trail : NativeAgendaRecords.Layout tc}
variable {d : Descriptor} {rootRegion : Region rc} {all : Array Word}
variable {image : NativeImage.View} {base : BitVec 48}

private theorem needle_away (frame : Frame) (i : Fin 11) :
    Disjoint (slotBytes frame ⟨i.val, i.isLt.trans (by decide)⟩) (slotBytes frame 11) := by
  apply frame.separate_words
  intro same
  have impossible : i.val = 11 := congrArg Fin.val same
  omega

/-- Reuse the earlier checkpoint and occurrence window,
fetching only the new pattern. No trial length is read. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {start : ℕ} {before : Native} (view : View all) (code : NativeGuardInstall.NeedlePlaced image start view.pattern.val)
    (point : At image before base start) (controls : Controls before) (sameFrame : frame = guardFrame d)
    (held : Held d rootRegion all before) (graph : PackedTerms.Arena) (oldNeedle : Word)
    (space : Geometry term map frame agenda trail (view.region rootRegion held.words.fits) image base)
    (ready : Stable term map frame agenda trail (view.region rootRegion held.words.fits) graph oldNeedle view.occurrences before)
    (rootApart : Separated rootRegion frame.region) (safe : CodeApart image base (slotBytes frame 11)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 6).run before = .ok () after ∧
      X86StateFrame.Frame clobbers (slotBytes frame 11) before after ∧
      Stable term map frame agenda trail (view.region rootRegion held.words.fits) graph view.needle view.occurrences after ∧
      Held d rootRegion all after ∧ Nonempty (At image after base (start + 38)) := by
  obtain ⟨after, ran, framed, _, _, needle, endpoint⟩ :=
    NativeGuardInstall.fetched_needle other extra vector view code point controls sameFrame held ready.scratch.stack safe
  have field := slots_cover frame 11
  have workspace := space.workspace
  have savedGraph := ready.scratch.sourceReady.kept framed
    (fun i j => Covered.separate workspace.frameNode.symm (Covered.node term i j) field)
    (fun i => Covered.separate workspace.frameEdge.symm (Covered.edge term i) field)
  have directory := ready.directory
  have atRoot (i : Fin rc) := Covered.separate rootApart (Covered.word rootRegion i) field
  have atWindow (i : Fin view.count) :=
    Covered.separate rootApart (NativeRootSlices.window_covered rootRegion view.offset view.count (view.fits.trans held.words.fits) i) field
  have scratch : NativeGuardWorkspace.Ready term map frame agenda trail graph after :=
    ⟨savedGraph, (framed.lookup 4 (by decide)).trans ready.scratch.stack,
      fun i n e => (ready.scratch.saved i n e).preserved framed (needle_away frame i),
      ready.scratch.pool.preserved framed (Covered.separate workspace.frameAgenda.symm (Covered.metadata agenda 1) field),
      ready.scratch.agendaLimit.preserved framed (Covered.separate workspace.frameAgenda.symm (Covered.metadata agenda 2) field),
      ready.scratch.trailLimit.preserved framed (Covered.separate workspace.frameTrail.symm (Covered.metadata trail 2) field),
      (framed.lookup 12 (by decide)).trans ready.scratch.zero, (framed.lookup 13 (by decide)).trans ready.scratch.one⟩
  have remainder : NativeGuardOperands.Directory (view.region rootRegion held.words.fits) frame view.needle view.occurrences after :=
    ⟨needle, directory.pointer.preserved framed (frame.separate_words (by decide)),
      directory.count.preserved framed (frame.separate_words (by decide)), directory.occurrences.kept framed atWindow⟩
  have metadata (i : Fin 18) (afterCore : 16 ≤ i.val) :=
    (NativeGuardInstall.root_metadata_apart d frame sameFrame i afterCore).mono_right
      (show slotBytes frame 11 ⊆ NativeGuardInstall.descriptorBytes frame from
        Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left)
  exact ⟨after, ran, framed, ⟨scratch, remainder⟩,
    ⟨held.descriptor.kept framed (metadata 16 (by decide)) (metadata 17 (by decide)), held.words.kept framed atRoot⟩, endpoint⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardReuse
