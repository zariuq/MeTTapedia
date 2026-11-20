import Mettapedia.Machines.TIsa.X86BlockCompiler

/-!
# Combining native component libraries with a shared source interface

The combined library retains each component's source action, bytes and count.
Its footprint is the union of the actual component footprints. Matching source
representations and readiness predicates are required explicitly.

Local execution certificates compose without re-proving their instructions.
Every fetched prefix retains the combined frame, and the existing block
compiler then supplies layout, source/WP and native sequencing theorems for
mixed programs. This construction introduces no additional runtime semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86LibrarySum
open _root_.X86Registers X86RegisterRefinement X86Execution
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
local instance : MemoryPrimitives := X86Memory.ordinary

universe u v s
variable {Left : Type u} {Right : Type v} {Source : Type s}

def combine (left : X86BlockCompiler.Spec Left Source) (right : X86BlockCompiler.Spec Right Source) :
    X86BlockCompiler.Spec (Sum Left Right) Source where
  action := Sum.elim left.action right.action
  represents := left.represents
  ready := left.ready
  bytes := Sum.elim left.bytes right.bytes
  count := Sum.elim left.count right.count
  registerWrites := left.registerWrites ∪ right.registerWrites
  byteWrites := left.byteWrites ∪ right.byteWrites

theorem progress (left : X86BlockCompiler.Spec Left Source) (right : X86BlockCompiler.Spec Right Source)
    (leftProgress : ∀ instruction, (left.action instruction).Progress)
    (rightProgress : ∀ instruction, (right.action instruction).Progress)
    (instruction : Sum Left Right) : ((combine left right).action instruction).Progress := by
  cases instruction with
  | inl instruction => exact leftProgress instruction
  | inr instruction => exact rightProgress instruction

theorem correct [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (left : X86BlockCompiler.Spec Left Source) (right : X86BlockCompiler.Spec Right Source)
    (leftCorrect : X86BlockCompiler.Correct left) (rightCorrect : X86BlockCompiler.Correct right)
    (sameRepresentation : right.represents = left.represents) (sameReady : right.ready = left.ready) :
    X86BlockCompiler.Correct (combine left right) where
  dataOnly := Finset.union_subset leftCorrect.dataOnly rightCorrect.dataOnly
  execute instruction source following native origin safe step represented prepared upper loaded outside := by
    cases instruction with
    | inl instruction =>
      obtain ⟨after,run,frame,representedAfter,readyAfter,rip,prefixes⟩ :=
        leftCorrect.execute instruction source following native origin safe step represented prepared upper loaded
          (fun index byte present member => outside index byte present (Finset.mem_union_left _ member))
      refine ⟨after,run,frame.mono Finset.subset_union_left Finset.subset_union_left,
        representedAfter,readyAfter,rip,?_⟩
      intro count within observed observedRun
      exact (prefixes count within observed observedRun).mono Finset.subset_union_left Finset.subset_union_left
    | inr instruction =>
      have representedRight : right.represents source native := by rw [sameRepresentation]; exact represented
      have preparedRight : right.ready native := by rw [sameReady]; exact prepared
      obtain ⟨after,run,frame,representedAfter,readyAfter,rip,prefixes⟩ :=
        rightCorrect.execute instruction source following native origin safe step representedRight preparedRight upper loaded
          (fun index byte present member => outside index byte present (Finset.mem_union_right _ member))
      refine ⟨after,run,frame.mono Finset.subset_union_right Finset.subset_union_right,?_,?_,rip,?_⟩
      · simpa only [combine,sameRepresentation] using representedAfter
      · simpa only [combine,sameReady] using readyAfter
      · intro count within observed observedRun
        exact (prefixes count within observed observedRun).mono Finset.subset_union_right Finset.subset_union_right

#print axioms correct
end Mettapedia.Machines.TIsa.X86LibrarySum
