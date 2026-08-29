import Mettapedia.GSLT.Core.SpeculativeFiniteHeapLookup
import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupTransformation

/-!
# Authored compressed heap lookup through the speculative GSLT

The generic speculative lookup calculus has a direct semantic hit and a
finite cursor fallback.  This module specializes that calculus to the
authored Metamath compressed heap and retains the proof-node/assertion split.
It is the semantic GSLT-to-GSLT stage corresponding to the presentation pass;
conformance of reflective MM2 atom execution remains a separate boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupTransformation

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.OccurrenceHeapProtocol
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupTransformation
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapSourceBridge
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceProjection

namespace Direct

abbrev Control :=
  Mettapedia.GSLT.FiniteHeapLookupRealization.Control Nat Unit SourceAssertion

abbrev State :=
  Mettapedia.GSLT.FiniteHeapLookupRealization.State Nat Unit SourceAssertion

end Direct

namespace Speculative

abbrev Control :=
  Mettapedia.GSLT.SpeculativeFiniteHeapLookup.Control SourceHeapEntry

abbrev State :=
  Mettapedia.GSLT.SpeculativeFiniteHeapLookup.State SourceHeapEntry

end Speculative

/-- The reusable direct-to-speculative realization specialized to the exact
heterogeneous carrier projected from an authored compressed heap. -/
noncomputable def sourceHeapSpeculativeRealization (reserve : Nat) :
    OperationalRealization
      (Mettapedia.GSLT.FiniteHeapLookupRealization.directGSLT
        Nat Unit SourceAssertion)
      (Mettapedia.GSLT.SpeculativeFiniteHeapLookup.gslt SourceHeapEntry) :=
  Mettapedia.GSLT.SpeculativeFiniteHeapLookup.realization reserve

/-- OSLF predicate transport for the source-derived speculative lookup
stage.  It is contravariant because modal predicates pull back along the
path-valued realization. -/
noncomputable def sourceHeapSpeculativeReachabilityNTT (reserve : Nat) :
    Mettapedia.OSLF.Framework.IndexedModalFunctor.ForwardModalPredicateTheory.Hom
      (Mettapedia.OSLF.Framework.IndexedModalFunctor.oslfForwardModalObject
        (Mettapedia.GSLT.SpeculativeFiniteHeapLookup.gslt
          SourceHeapEntry).closure)
      (Mettapedia.OSLF.Framework.IndexedModalFunctor.oslfForwardModalObject
        (Mettapedia.GSLT.FiniteHeapLookupRealization.directGSLT
          Nat Unit SourceAssertion).closure) :=
  (sourceHeapSpeculativeRealization reserve).closureOSLFPullback

/-- A proof heap occurrence becomes a one-step speculative hit at the same
index and with the same source proof-node identity. -/
theorem source_proof_lookup_realizes_speculative_hit
    {source : SourcePrefix}
    (heap : List (SourceGSLTCompressedTheorem.HeapEntry source))
    (reserve index nodeId : Nat)
    (found : heap[index]? = some (.proof nodeId)) :
    Nonempty
      (ExecutionPath
        (Mettapedia.GSLT.SpeculativeFiniteHeapLookup.gslt SourceHeapEntry)
        (Mettapedia.GSLT.SpeculativeFiniteHeapLookup.mapState reserve
          (⟨sourceHeap heap, .lookup index⟩ : Direct.State))
        (Mettapedia.GSLT.SpeculativeFiniteHeapLookup.mapState reserve
          (⟨sourceHeap heap,
            .foundOccurrence index ⟨nodeId, ()⟩⟩ :
              Direct.State))) := by
  exact Mettapedia.GSLT.SpeculativeFiniteHeapLookup.step_has_path reserve
    (Mettapedia.GSLT.FiniteHeapLookupRealization.Step.occurrence
      (sourceHeap heap) index ⟨nodeId, ()⟩ (sourceHeap_get_proof found))

/-- An assertion heap occurrence follows the independent opaque branch; it
cannot be reclassified as a proof node by speculative lookup. -/
theorem source_assertion_lookup_realizes_speculative_hit
    {source : SourcePrefix}
    (heap : List (SourceGSLTCompressedTheorem.HeapEntry source))
    (reserve index : Nat) (assertion : SourceAssertion)
    (found : heap[index]? = some (.assertion assertion)) :
    Nonempty
      (ExecutionPath
        (Mettapedia.GSLT.SpeculativeFiniteHeapLookup.gslt SourceHeapEntry)
        (Mettapedia.GSLT.SpeculativeFiniteHeapLookup.mapState reserve
          (⟨sourceHeap heap, .lookup index⟩ : Direct.State))
        (Mettapedia.GSLT.SpeculativeFiniteHeapLookup.mapState reserve
          (⟨sourceHeap heap,
            .foundOpaque index assertion⟩ : Direct.State))) := by
  exact Mettapedia.GSLT.SpeculativeFiniteHeapLookup.step_has_path reserve
    (Mettapedia.GSLT.FiniteHeapLookupRealization.Step.opaque
      (sourceHeap heap) index assertion (sourceHeap_get_assertion found))

/-- A missing source position takes the explicit fallback route and stops at
the live heap frontier, regardless of additional reserved capacity. -/
theorem source_missing_lookup_realizes_speculative_frontier
    {source : SourcePrefix}
    (heap : List (SourceGSLTCompressedTheorem.HeapEntry source))
    (reserve index : Nat) (absent : heap[index]? = none) :
    Nonempty
      (ExecutionPath
        (Mettapedia.GSLT.SpeculativeFiniteHeapLookup.gslt SourceHeapEntry)
        (Mettapedia.GSLT.SpeculativeFiniteHeapLookup.mapState reserve
          (⟨sourceHeap heap, .lookup index⟩ : Direct.State))
        (Mettapedia.GSLT.SpeculativeFiniteHeapLookup.mapState reserve
          (⟨sourceHeap heap, .missing index⟩ : Direct.State))) := by
  have projectedAbsent : GetElem?.getElem? (sourceHeap heap) index = none := by
    simpa [sourceHeap, List.getElem?_map] using
      congrArg (Option.map sourceHeapEntry) absent
  exact Mettapedia.GSLT.SpeculativeFiniteHeapLookup.step_has_path reserve
    (Mettapedia.GSLT.FiniteHeapLookupRealization.Step.missing
      (sourceHeap heap) index projectedAbsent)

/-- Successful speculative lookup has constant semantic cost, independent of
the requested source occurrence index. -/
theorem source_proof_lookup_speculative_cost_one
    {source : SourcePrefix}
    (heap : List (SourceGSLTCompressedTheorem.HeapEntry source))
    (reserve index nodeId : Nat)
    (found : heap[index]? = some (.proof nodeId)) :
    ∃ path : ExecutionPath
        (Mettapedia.GSLT.SpeculativeFiniteHeapLookup.gslt SourceHeapEntry)
        (Mettapedia.GSLT.SpeculativeFiniteHeapLookup.mapState reserve
          (⟨sourceHeap heap, .lookup index⟩ : Direct.State))
        (Mettapedia.GSLT.SpeculativeFiniteHeapLookup.mapState reserve
          (⟨sourceHeap heap,
            .foundOccurrence index ⟨nodeId, ()⟩⟩ :
              Direct.State)),
      path.length = 1 := by
  let step := Mettapedia.GSLT.SpeculativeFiniteHeapLookup.Step.hit
    (sourceHeap heap) reserve index (.occurrence ⟨nodeId, ()⟩)
      (sourceHeap_get_proof found)
  exact ⟨.cons ⟨step⟩ (.refl _), rfl⟩

/-- Missing lookup retains the exact finite cost: one fallback start, one
advance per live heap occurrence, and one frontier observation. -/
theorem source_missing_lookup_speculative_exact_cost
    {source : SourcePrefix}
    (heap : List (SourceGSLTCompressedTheorem.HeapEntry source))
    (reserve index : Nat) (absent : heap[index]? = none) :
    ∃ path : ExecutionPath
        (Mettapedia.GSLT.SpeculativeFiniteHeapLookup.gslt SourceHeapEntry)
        (Mettapedia.GSLT.SpeculativeFiniteHeapLookup.mapState reserve
          (⟨sourceHeap heap, .lookup index⟩ : Direct.State))
        (Mettapedia.GSLT.SpeculativeFiniteHeapLookup.mapState reserve
          (⟨sourceHeap heap, .missing index⟩ : Direct.State)),
      path.length = heap.length + 2 := by
  have projectedAbsent : GetElem?.getElem? (sourceHeap heap) index = none := by
    simpa [sourceHeap, List.getElem?_map] using
      congrArg (Option.map sourceHeapEntry) absent
  simpa [Mettapedia.GSLT.SpeculativeFiniteHeapLookup.mapState,
    sourceHeap_length] using
      (Mettapedia.GSLT.SpeculativeFiniteHeapLookup.finishMissing_has_exact_cost
        (sourceHeap heap) reserve index projectedAbsent)

/-- Every authored compressed proof `step` chooses the matching speculative
proof or assertion path.  The source action, not an MM2 rule name, determines
the branch. -/
theorem authored_step_realizes_exact_speculative_branch
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {before after : MachineState source target} {index : Nat}
    (step : ActionStep before (.step index) after) (reserve : Nat) :
    (∃ nodeId,
        before.heap[index]? = some (.proof nodeId) ∧
          Nonempty
            (ExecutionPath
              (Mettapedia.GSLT.SpeculativeFiniteHeapLookup.gslt SourceHeapEntry)
              (Mettapedia.GSLT.SpeculativeFiniteHeapLookup.mapState reserve
                (⟨sourceHeap before.heap, .lookup index⟩ :
                  Direct.State))
              (Mettapedia.GSLT.SpeculativeFiniteHeapLookup.mapState reserve
                (⟨sourceHeap before.heap,
                  .foundOccurrence index ⟨nodeId, ()⟩⟩ :
                    Direct.State)))) ∨
      (∃ assertion,
        before.heap[index]? = some (.assertion assertion) ∧
          Nonempty
            (ExecutionPath
              (Mettapedia.GSLT.SpeculativeFiniteHeapLookup.gslt SourceHeapEntry)
              (Mettapedia.GSLT.SpeculativeFiniteHeapLookup.mapState reserve
                (⟨sourceHeap before.heap, .lookup index⟩ :
                  Direct.State))
              (Mettapedia.GSLT.SpeculativeFiniteHeapLookup.mapState reserve
                (⟨sourceHeap before.heap,
                  .foundOpaque index assertion⟩ :
                    Direct.State)))) := by
  cases step with
  | proof index nodeId node heapLookup nodeLookup =>
      exact Or.inl
        ⟨nodeId, heapLookup,
          source_proof_lookup_realizes_speculative_hit before.heap reserve index
            nodeId heapLookup⟩
  | assertion index assertion retained parents children heapLookup
      member stack_eq node resolved =>
      exact Or.inr
        ⟨assertion, heapLookup,
          source_assertion_lookup_realizes_speculative_hit before.heap reserve
            index assertion heapLookup⟩

#print axioms sourceHeapSpeculativeRealization
#print axioms sourceHeapSpeculativeReachabilityNTT
#print axioms source_proof_lookup_realizes_speculative_hit
#print axioms source_assertion_lookup_realizes_speculative_hit
#print axioms source_missing_lookup_realizes_speculative_frontier
#print axioms source_proof_lookup_speculative_cost_one
#print axioms source_missing_lookup_speculative_exact_cost
#print axioms authored_step_realizes_exact_speculative_branch

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupTransformation
