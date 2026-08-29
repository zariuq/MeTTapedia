import Mettapedia.GSLT.Core.FiniteHeapLookupRealization
import Mettapedia.GSLT.Core.ReservedFiniteCursorLookup
import Mettapedia.Languages.Metamath.MM2CompressedIndexSpine
import Mettapedia.Languages.Metamath.MM2CompressedProofHeapSourceBridge

/-!
# Authored compressed heap lookup as a finite GSLT realization

This module joins the authored heterogeneous Metamath heap to the reusable
finite cursor calculus.  Proof entries and assertion entries remain distinct,
but both retain the same authored heap position.  Missing references reach an
explicit finite frontier.

The output is still a semantic cursor GSLT, not yet the reflective MM2 atom
machine.  That next realization must preserve these exact proof, assertion,
and missing observations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupTransformation

open Mettapedia.GSLT
open Mettapedia.GSLT.FiniteHeapLookupRealization
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.OccurrenceHeapProtocol
open Mettapedia.GSLT.ReservedFiniteCursorLookup
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.MM2CompressedIndexSpine
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapSourceBridge
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceProjection

abbrev SourceHeapEntry := Entry Nat Unit SourceAssertion

/-! ## Exact target cursor inventory

The semantic scan stops at the live heap frontier.  The executable MM2 data
may reserve a larger finite capacity for later `Z` saves, but it must contain
every successor edge strictly below the current frontier.  Failure remains an
explicit comparison with `heap-next`; it is not inferred from the absence of a
reserved successor row.
-/

/-- Every live source heap position has the exact compact successor row in
any finite MM2 reservation large enough to contain the heap. -/
theorem source_live_heap_cursor_has_target_successor
    {source : SourcePrefix} (proofOwner : Atom)
    (heap : List (SourceGSLTCompressedTheorem.HeapEntry source))
    (capacity position : Nat) (heapFits : heap.length ≤ capacity)
    (live : position < heap.length) :
    compressedIndexSuccessorRow (compressedHeapOwner proofOwner)
        (CompressedIndexCode.ofNat position).atom
        (CompressedIndexCode.ofNat (position + 1)).atom ∈
      compressedIndexSuccessorRows (compressedHeapOwner proofOwner)
        capacity := by
  exact compressedIndexSuccessorRow_mem _ capacity position
    (lt_of_lt_of_le live heapFits)

/-- Negative control for the exact live spine: it has no edge beginning at
the source heap frontier. -/
theorem source_heap_frontier_has_no_live_successor
    {source : SourcePrefix} (proofOwner : Atom)
    (heap : List (SourceGSLTCompressedTheorem.HeapEntry source)) :
    compressedIndexSuccessorRow (compressedHeapOwner proofOwner)
        (CompressedIndexCode.ofNat heap.length).atom
        (CompressedIndexCode.ofNat (heap.length + 1)).atom ∉
      compressedIndexSuccessorRows (compressedHeapOwner proofOwner)
        heap.length := by
  exact compressedIndexFrontier_has_no_successor _ heap.length

/-- A larger allocation may deliberately contain an edge beyond the current
heap frontier.  This positive control prevents an absence-of-row argument
from being mistaken for the verifier's missing-reference test. -/
theorem reserved_capacity_may_extend_past_source_frontier
    {source : SourcePrefix} (proofOwner : Atom)
    (heap : List (SourceGSLTCompressedTheorem.HeapEntry source))
    (capacity : Nat) (reserved : heap.length < capacity) :
    compressedIndexSuccessorRow (compressedHeapOwner proofOwner)
        (CompressedIndexCode.ofNat heap.length).atom
        (CompressedIndexCode.ofNat (heap.length + 1)).atom ∈
      compressedIndexSuccessorRows (compressedHeapOwner proofOwner)
        capacity := by
  exact compressedIndexSuccessorRow_mem _ capacity heap.length reserved

/-- The generic path-valued lookup realization specialized to the authored
compressed Metamath heap carrier. -/
noncomputable def sourceHeapLookupRealization :
    OperationalRealization (directGSLT Nat Unit SourceAssertion)
      (FiniteOccurrenceLookup.gslt Nat SourceHeapEntry) :=
  scanRealization

/-- Compose the authored heterogeneous lookup with the reserved indexed
cursor stage.  At a concrete runtime lookup, `reserve` is the unused portion
of the already allocated heap capacity; no proof action is expanded here. -/
noncomputable def sourceHeapReservedCursorRealization (reserve : Nat) :
    OperationalRealization (directGSLT Nat Unit SourceAssertion)
      (ReservedFiniteCursorLookup.gslt Nat SourceHeapEntry) :=
  sourceHeapLookupRealization.comp
    (ReservedFiniteCursorLookup.realization reserve)

/-- OSLF modal transport for one source heap lookup lowered to a finite cursor
path.  The arrow is contravariant because predicates pull back from realized
cursor states to the direct authored lookup meaning. -/
noncomputable def sourceHeapLookupReachabilityNTT :
    Mettapedia.OSLF.Framework.IndexedModalFunctor.ForwardModalPredicateTheory.Hom
      (Mettapedia.OSLF.Framework.IndexedModalFunctor.oslfForwardModalObject
        (FiniteOccurrenceLookup.gslt Nat SourceHeapEntry).closure)
      (Mettapedia.OSLF.Framework.IndexedModalFunctor.oslfForwardModalObject
        (directGSLT Nat Unit SourceAssertion).closure) :=
  sourceHeapLookupRealization.closureOSLFPullback

/-- OSLF of the composed source lookup → finite scan → reserved cursor
route. -/
noncomputable def sourceHeapReservedCursorReachabilityNTT (reserve : Nat) :
    Mettapedia.OSLF.Framework.IndexedModalFunctor.ForwardModalPredicateTheory.Hom
      (Mettapedia.OSLF.Framework.IndexedModalFunctor.oslfForwardModalObject
        (ReservedFiniteCursorLookup.gslt Nat SourceHeapEntry).closure)
      (Mettapedia.OSLF.Framework.IndexedModalFunctor.oslfForwardModalObject
        (directGSLT Nat Unit SourceAssertion).closure) :=
  (sourceHeapReservedCursorRealization reserve).closureOSLFPullback

/-- The generated native-theory arrow factors in reverse stage order, as
required by OSLF predicate pullback. -/
theorem sourceHeapReservedCursorReachabilityNTT_factors (reserve : Nat) :
    sourceHeapReservedCursorReachabilityNTT reserve =
      (ReservedFiniteCursorLookup.realization reserve).closureOSLFPullback.comp
        sourceHeapLookupRealization.closureOSLFPullback := by
  exact OperationalRealization.closureOSLFPullback_comp
    sourceHeapLookupRealization
    (ReservedFiniteCursorLookup.realization reserve)

/-- A proof-valued authored heap entry becomes a finite scan ending at the
same heap position and the same proof-node identity. -/
theorem source_proof_lookup_realizes_finite_scan
    {source : SourcePrefix}
    (heap : List (SourceGSLTCompressedTheorem.HeapEntry source))
    (index nodeId : Nat)
    (found : heap[index]? = some (.proof nodeId)) :
    Nonempty
      (ExecutionPath (FiniteOccurrenceLookup.gslt Nat SourceHeapEntry)
        (scanState
          ⟨sourceHeap heap, Control.lookup index⟩)
        (scanState
          ⟨sourceHeap heap,
            Control.foundOccurrence index ⟨nodeId, ()⟩⟩)) := by
  exact scan_step_has_path
    (Step.occurrence (sourceHeap heap) index ⟨nodeId, ()⟩
      (sourceHeap_get_proof found))

/-- An assertion-valued authored heap entry follows the same finite carrier
but ends in the opaque branch rather than masquerading as a proof node. -/
theorem source_assertion_lookup_realizes_finite_scan
    {source : SourcePrefix}
    (heap : List (SourceGSLTCompressedTheorem.HeapEntry source))
    (index : Nat) (assertion : SourceAssertion)
    (found : heap[index]? = some (.assertion assertion)) :
    Nonempty
      (ExecutionPath (FiniteOccurrenceLookup.gslt Nat SourceHeapEntry)
        (scanState
          ⟨sourceHeap heap, Control.lookup index⟩)
        (scanState
          ⟨sourceHeap heap, Control.foundOpaque index assertion⟩)) := by
  exact scan_step_has_path
    (Step.opaque (sourceHeap heap) index assertion
      (sourceHeap_get_assertion found))

/-- A missing authored heap position reaches only the explicit end of the
same occurrence sequence. -/
theorem source_missing_lookup_realizes_finite_frontier
    {source : SourcePrefix}
    (heap : List (SourceGSLTCompressedTheorem.HeapEntry source))
    (index : Nat) (absent : heap[index]? = none) :
    Nonempty
      (ExecutionPath (FiniteOccurrenceLookup.gslt Nat SourceHeapEntry)
        (scanState
          ⟨sourceHeap heap, Control.lookup index⟩)
        (scanState
          ⟨sourceHeap heap, Control.missing index⟩)) := by
  have projectedAbsent :
      GetElem?.getElem? (sourceHeap heap) index = none := by
    simpa [sourceHeap, List.getElem?_map] using
      congrArg (Option.map sourceHeapEntry) absent
  exact scan_step_has_path
    (Step.missing (sourceHeap heap) index projectedAbsent)

/-- Every authored compressed `step` action chooses exactly one of the two
heterogeneous finite-scan observations.  The proof branch retains the node
identity; the assertion branch retains the exact authored assertion. -/
theorem authored_step_realizes_exact_heap_branch
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {before after : MachineState source target} {index : Nat}
    (step : ActionStep before (.step index) after) :
    (∃ nodeId,
        before.heap[index]? = some (.proof nodeId) ∧
          Nonempty
            (ExecutionPath
              (FiniteOccurrenceLookup.gslt Nat SourceHeapEntry)
              (scanState
                ⟨sourceHeap before.heap, Control.lookup index⟩)
              (scanState
                ⟨sourceHeap before.heap,
                  Control.foundOccurrence index ⟨nodeId, ()⟩⟩))) ∨
      (∃ assertion,
        before.heap[index]? = some (.assertion assertion) ∧
          Nonempty
            (ExecutionPath
              (FiniteOccurrenceLookup.gslt Nat SourceHeapEntry)
              (scanState
                ⟨sourceHeap before.heap, Control.lookup index⟩)
              (scanState
                ⟨sourceHeap before.heap,
                  Control.foundOpaque index assertion⟩))) := by
  cases step with
  | proof index nodeId node heapLookup nodeLookup =>
      exact Or.inl
        ⟨nodeId, heapLookup,
          source_proof_lookup_realizes_finite_scan before.heap index nodeId
            heapLookup⟩
  | assertion index assertion retained parents children heapLookup
      member stack_eq node resolved =>
      exact Or.inr
        ⟨assertion, heapLookup,
          source_assertion_lookup_realizes_finite_scan before.heap index
            assertion heapLookup⟩

/-- Every cursor edge needed to reach an authored compressed `step` target is
present in any sufficiently large finite MM2 reservation.  This connects the
source semantic lookup witness to the concrete successor vocabulary consumed
by the target heap walker. -/
theorem authored_step_has_target_cursor_inventory
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {before after : MachineState source target} {index : Nat}
    (step : ActionStep before (.step index) after)
    (proofOwner : Atom) (capacity : Nat)
    (heapFits : before.heap.length ≤ capacity) :
    ∀ cursor < index,
      compressedIndexSuccessorRow (compressedHeapOwner proofOwner)
          (CompressedIndexCode.ofNat cursor).atom
          (CompressedIndexCode.ofNat (cursor + 1)).atom ∈
        compressedIndexSuccessorRows (compressedHeapOwner proofOwner)
          capacity := by
  intro cursor cursorBefore
  cases step with
  | proof index nodeId node heapLookup nodeLookup =>
      have indexLive : index < before.heap.length :=
        (List.getElem?_eq_some_iff.mp heapLookup).1
      exact source_live_heap_cursor_has_target_successor proofOwner before.heap
        capacity cursor heapFits (lt_trans cursorBefore indexLive)
  | assertion index assertion retained parents children heapLookup
      member stack_eq node resolved =>
      have indexLive : index < before.heap.length :=
        (List.getElem?_eq_some_iff.mp heapLookup).1
      exact source_live_heap_cursor_has_target_successor proofOwner before.heap
        capacity cursor heapFits (lt_trans cursorBefore indexLive)

#print axioms sourceHeapLookupRealization
#print axioms sourceHeapReservedCursorRealization
#print axioms sourceHeapLookupReachabilityNTT
#print axioms sourceHeapReservedCursorReachabilityNTT
#print axioms sourceHeapReservedCursorReachabilityNTT_factors
#print axioms source_live_heap_cursor_has_target_successor
#print axioms source_heap_frontier_has_no_live_successor
#print axioms reserved_capacity_may_extend_past_source_frontier
#print axioms source_proof_lookup_realizes_finite_scan
#print axioms source_assertion_lookup_realizes_finite_scan
#print axioms source_missing_lookup_realizes_finite_frontier
#print axioms authored_step_realizes_exact_heap_branch
#print axioms authored_step_has_target_cursor_inventory

end Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupTransformation
