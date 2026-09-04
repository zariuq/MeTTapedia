import Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface

/-!
# Finite frame for the decorated direct assertion handler

This module contains only the concrete row inventory.  Matching, scheduling,
publication, and source representation are separate proof layers over this
shared finite surface.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionFrame

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.ProcessCalculi.MORK

def decoratedDirectAssertionDataSlice
    (context : DirectAssertionContext) : List Atom :=
  [context.pendingRow, context.lookupRow, context.heapRow, context.machineRow,
   context.headerRow, context.rejoinCaptureRow,
   decoratedDirectAssertionBridgeCaptureRow]

/-- Every row in the finite assertion data slice exposes exactly its outer
constructor head, without unfolding its payload in downstream proofs. -/
theorem decoratedDirectAssertionDataSlice_head_cases
    (context : DirectAssertionContext) {row : Atom}
    (member : row ∈ decoratedDirectAssertionDataSlice context) :
    compressedDynamicRowHead? row = some "mm-compressed-step-pending" ∨
      compressedDynamicRowHead? row = some "mm-compressed-heap-lookup" ∨
      compressedDynamicRowHead? row = some "mm-compressed-heap-assertion" ∨
      compressedDynamicRowHead? row = some "mm-compressed-machine" ∨
      compressedDynamicRowHead? row = some "mm-assertion-header" ∨
      compressedDynamicRowHead? row =
        some "mm-compressed-owned-runtime-rule" ∨
      compressedDynamicRowHead? row =
        some "mm-internal-compressed-normal-dispatch-bridge" := by
  simp only [decoratedDirectAssertionDataSlice, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

/-- The data slice has one uniform outer-head certificate; downstream physical
proofs need not instantiate their key argument once per row constructor. -/
theorem decoratedDirectAssertionDataSlice_shortNonExecHead
    (context : DirectAssertionContext) {row : Atom}
    (member : row ∈ decoratedDirectAssertionDataSlice context) :
    ∃ head,
      compressedDynamicRowHead? row = some head ∧
        0 < (morkUtf8Bytes head).length ∧
        (morkUtf8Bytes head).length < 64 ∧
        head ≠ "exec" := by
  rcases decoratedDirectAssertionDataSlice_head_cases context member with
    pending | lookup | heap | machine | header | rejoin | bridge
  · exact ⟨"mm-compressed-step-pending", pending,
      by decide, by decide, by decide⟩
  · exact ⟨"mm-compressed-heap-lookup", lookup,
      by decide, by decide, by decide⟩
  · exact ⟨"mm-compressed-heap-assertion", heap,
      by decide, by decide, by decide⟩
  · exact ⟨"mm-compressed-machine", machine,
      by decide, by decide, by decide⟩
  · exact ⟨"mm-assertion-header", header,
      by decide, by decide, by decide⟩
  · exact ⟨"mm-compressed-owned-runtime-rule", rejoin,
      by decide, by decide, by decide⟩
  · exact ⟨"mm-internal-compressed-normal-dispatch-bridge", bridge,
      by decide, by decide, by decide⟩

def decoratedDirectAssertionMatchSlice
    (context : DirectAssertionContext) : List Atom :=
  decoratedDirectAssertionDirective.atom ::
    decoratedDirectAssertionDataSlice context

theorem decoratedDirectAssertionMatchSlice_eq_cons
    (context : DirectAssertionContext) :
    decoratedDirectAssertionMatchSlice context =
      decoratedDirectAssertionDirective.atom ::
        decoratedDirectAssertionDataSlice context := by
  rfl

theorem mem_decoratedDirectAssertionMatchSlice_iff
    (context : DirectAssertionContext) (atom : Atom) :
    atom ∈ decoratedDirectAssertionMatchSlice context ↔
      atom = decoratedDirectAssertionDirective.atom ∨
        atom ∈ decoratedDirectAssertionDataSlice context := by
  rw [decoratedDirectAssertionMatchSlice_eq_cons]
  exact List.mem_cons

def decoratedDirectAssertionSchedulerFrame : List Atom :=
  [compressedProofStepDirective.atom,
   decoratedCursorAssertionDirective.atom,
   compressedHeapLookupFaultDirective.atom,
   compressedHeapLookupAdvanceDirective.atom]

inductive DecoratedAssertionSchedulerAuthority where
  | proofStep
  | cursorAssertion
  | lookupFault
  | lookupAdvance
  deriving DecidableEq

def DecoratedAssertionSchedulerAuthority.all :
    List DecoratedAssertionSchedulerAuthority :=
  [.proofStep, .cursorAssertion, .lookupFault, .lookupAdvance]

def DecoratedAssertionSchedulerAuthority.atom :
    DecoratedAssertionSchedulerAuthority → Atom
  | .proofStep => compressedProofStepDirective.atom
  | .cursorAssertion => decoratedCursorAssertionDirective.atom
  | .lookupFault => compressedHeapLookupFaultDirective.atom
  | .lookupAdvance => compressedHeapLookupAdvanceDirective.atom

def DecoratedAssertionSchedulerAuthority.directive :
    DecoratedAssertionSchedulerAuthority → SourceExecFact
  | .proofStep => compressedProofStepDirective
  | .cursorAssertion => decoratedCursorAssertionDirective
  | .lookupFault => compressedHeapLookupFaultDirective
  | .lookupAdvance => compressedHeapLookupAdvanceDirective

theorem decoratedDirectAssertionSchedulerFrame_eq_atoms :
    decoratedDirectAssertionSchedulerFrame =
      DecoratedAssertionSchedulerAuthority.all.map
        DecoratedAssertionSchedulerAuthority.atom := by
  rfl

def canonicalDecoratedDirectAssertionSpace
    (context : DirectAssertionContext) : List Atom :=
  decoratedDirectAssertionMatchSlice context ++
    decoratedDirectAssertionSchedulerFrame

theorem mem_canonicalDecoratedDirectAssertionSpace_iff
    (context : DirectAssertionContext) (atom : Atom) :
    atom ∈ canonicalDecoratedDirectAssertionSpace context ↔
      atom ∈ decoratedDirectAssertionMatchSlice context ∨
        atom ∈ decoratedDirectAssertionSchedulerFrame := by
  exact List.mem_append

def decoratedDirectAssertionLive (space : List Atom) : List Atom :=
  space.erase decoratedDirectAssertionDirective.atom

def decoratedDirectAssertionLaunchRows
    (context : DirectAssertionContext) : List Atom :=
  context.launchRows ++ [compressedNormalDispatchBridgeRule]

#print axioms mem_decoratedDirectAssertionMatchSlice_iff
#print axioms mem_canonicalDecoratedDirectAssertionSpace_iff
#print axioms decoratedDirectAssertionDataSlice_head_cases
#print axioms decoratedDirectAssertionDataSlice_shortNonExecHead

end Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionFrame
