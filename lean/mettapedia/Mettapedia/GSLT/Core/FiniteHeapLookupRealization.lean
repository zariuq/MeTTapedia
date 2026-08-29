import Mettapedia.GSLT.Core.FiniteOccurrenceLookup
import Mettapedia.GSLT.Core.HeterogeneousHeapDispatch
import Mettapedia.GSLT.Core.OperationalRealizationOSLF

/-!
# Finite realization of heterogeneous heap lookup

An abstract indexed heap lookup is one semantic step.  A set-oriented runtime
may instead walk an explicit occurrence-indexed inventory until it reaches the
requested position or the finite frontier.  This module proves that lowering
once, independently of any proof language or target atom syntax.

Owner admission remains outside this calculus.  The input is an already
owner-matched heterogeneous heap, so the three public observations are an
exact proof occurrence, an exact opaque occurrence, or an explicit missing
index.  A surrounding activation calculus is responsible for rejecting a
cross-owner request before entering this stage.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.FiniteHeapLookupRealization

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.OccurrenceHeapProtocol

variable {Identity Value Other : Type}

abbrev HeapEntry (Identity Value Other : Type) :=
  Entry Identity Value Other

/-- Public states of one direct, owner-matched heterogeneous heap lookup. -/
inductive Control (Identity Value Other : Type) where
  | lookup (index : Nat)
  | foundOccurrence (index : Nat) (occurrence : Occurrence Identity Value)
  | foundOpaque (index : Nat) (value : Other)
  | missing (index : Nat)
deriving DecidableEq

structure State (Identity Value Other : Type) where
  heap : List (HeapEntry Identity Value Other)
  control : Control Identity Value Other
deriving DecidableEq

/-- Direct lookup meaning.  Missing is justified by `getElem? = none`, not by
the temporary absence of a runtime match. -/
inductive Step :
    State Identity Value Other → State Identity Value Other → Prop where
  | occurrence
      (heap : List (HeapEntry Identity Value Other)) (index : Nat)
      (item : Occurrence Identity Value)
      (found : heap[index]? = some (.occurrence item)) :
      Step ⟨heap, .lookup index⟩ ⟨heap, .foundOccurrence index item⟩
  | opaque
      (heap : List (HeapEntry Identity Value Other)) (index : Nat)
      (value : Other) (found : heap[index]? = some (.opaque value)) :
      Step ⟨heap, .lookup index⟩ ⟨heap, .foundOpaque index value⟩
  | missing
      (heap : List (HeapEntry Identity Value Other)) (index : Nat)
      (absent : heap[index]? = none) :
      Step ⟨heap, .lookup index⟩ ⟨heap, .missing index⟩

def directGSLT (Identity Value Other : Type) : GSLT where
  Term := State Identity Value Other
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Step
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- Give every heterogeneous heap entry its exact list position. -/
def indexedHeapFrom : Nat → List (HeapEntry Identity Value Other) →
    List (FiniteOccurrenceLookup.Entry Nat (HeapEntry Identity Value Other))
  | _, [] => []
  | position, entry :: entries =>
      ⟨position, entry⟩ :: indexedHeapFrom (position + 1) entries

def indexedHeap (heap : List (HeapEntry Identity Value Other)) :
    List (FiniteOccurrenceLookup.Entry Nat (HeapEntry Identity Value Other)) :=
  indexedHeapFrom 0 heap

@[simp] theorem indexedHeapFrom_length (position : Nat)
    (heap : List (HeapEntry Identity Value Other)) :
    (indexedHeapFrom position heap).length = heap.length := by
  induction heap generalizing position with
  | nil => rfl
  | cons entry heap induction =>
      simp [indexedHeapFrom, induction]

@[simp] theorem indexedHeap_length
    (heap : List (HeapEntry Identity Value Other)) :
    (indexedHeap heap).length = heap.length := by
  simp [indexedHeap]

/-- Scanning the indexed encoding at a relative index is exactly `getElem?`
on the original heap. -/
theorem lookupFrom_indexedHeapFrom (offset index : Nat)
    (heap : List (HeapEntry Identity Value Other)) :
    FiniteOccurrenceLookup.lookupFrom offset (offset + index)
        (indexedHeapFrom offset heap) =
      match heap[index]? with
      | some entry => .found (offset + index) entry
      | none => .missing (offset + heap.length) := by
  induction heap generalizing offset index with
  | nil => simp [indexedHeapFrom, FiniteOccurrenceLookup.lookupFrom]
  | cons entry heap induction =>
      cases index with
      | zero => simp [indexedHeapFrom, FiniteOccurrenceLookup.lookupFrom]
      | succ index =>
          have different : offset ≠ offset + (index + 1) := by omega
          simp only [indexedHeapFrom, FiniteOccurrenceLookup.lookupFrom,
            different, if_false,
            List.getElem?_cons_succ, List.length_cons]
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
            Nat.add_one, Nat.add_succ, Nat.succ_add, Nat.zero_add] using
            induction (offset + 1) index

/-- Complete finite lookup agrees exactly with direct heap indexing. -/
theorem lookup_indexedHeap (index : Nat)
    (heap : List (HeapEntry Identity Value Other)) :
    FiniteOccurrenceLookup.lookup index (indexedHeap heap) =
      match heap[index]? with
      | some entry => .found index entry
      | none => .missing heap.length := by
  simpa [FiniteOccurrenceLookup.lookup, indexedHeap] using
    lookupFrom_indexedHeapFrom (Identity := Identity) (Value := Value)
      (Other := Other) 0 index heap

/-- A successful scan reflects to the exact requested heap occurrence. -/
theorem lookup_indexedHeap_found_iff (index position : Nat)
    (heap : List (HeapEntry Identity Value Other))
    (entry : HeapEntry Identity Value Other) :
    FiniteOccurrenceLookup.lookup index (indexedHeap heap) =
        .found position entry ↔
      position = index ∧ heap[index]? = some entry := by
  rw [lookup_indexedHeap]
  cases found : heap[index]? with
  | none => simp
  | some actual =>
      constructor
      · intro equal
        cases equal
        exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, exact⟩
        cases exact
        rfl

/-- Frontier failure is exact and cannot be confused with a present entry. -/
theorem lookup_indexedHeap_missing_iff (index : Nat)
    (heap : List (HeapEntry Identity Value Other)) :
    FiniteOccurrenceLookup.lookup index (indexedHeap heap) =
        .missing heap.length ↔
      heap[index]? = none := by
  rw [lookup_indexedHeap]
  cases found : heap[index]? <;> simp

/-- Encode a direct semantic state as the endpoints of the finite scan. -/
def scanState : State Identity Value Other →
    FiniteOccurrenceLookup.State Nat (HeapEntry Identity Value Other)
  | ⟨heap, .lookup index⟩ =>
      FiniteOccurrenceLookup.initial index (indexedHeap heap)
  | ⟨heap, .foundOccurrence index occurrence⟩ =>
      .finished index (indexedHeap heap)
        (.found index (.occurrence occurrence))
  | ⟨heap, .foundOpaque index value⟩ =>
      .finished index (indexedHeap heap) (.found index (.opaque value))
  | ⟨heap, .missing index⟩ =>
      .finished index (indexedHeap heap) (.missing heap.length)

/-- Every direct lookup step has the exact proof-relevant finite cursor path.
The proposition-valued wrapper permits elimination of the semantic step proof
without erasing the path selected inside the witness. -/
theorem scan_step_has_path
    {source target : State Identity Value Other}
    (step : Step source target) :
    Nonempty
      (ExecutionPath
        (FiniteOccurrenceLookup.gslt Nat
          (HeapEntry Identity Value Other))
        (scanState source) (scanState target)) := by
  cases step with
  | occurrence heap index item found =>
      have exactLookup :
          FiniteOccurrenceLookup.lookup index (indexedHeap heap) =
            .found index (.occurrence item) :=
        (lookup_indexedHeap_found_iff index index heap
          (.occurrence item)).2 ⟨rfl, found⟩
      have path :
          (FiniteOccurrenceLookup.gslt Nat
            (HeapEntry Identity Value Other)).RewritePath
              (scanState ⟨heap, .lookup index⟩)
              (scanState ⟨heap, .foundOccurrence index item⟩) := by
        simpa [scanState, exactLookup] using
          (FiniteOccurrenceLookup.complete index (indexedHeap heap))
      exact ⟨rewritePathToExecutionPath path⟩
  | «opaque» heap index value found =>
      have exactLookup :
          FiniteOccurrenceLookup.lookup index (indexedHeap heap) =
            .found index (.opaque value) :=
        (lookup_indexedHeap_found_iff index index heap
          (.opaque value)).2 ⟨rfl, found⟩
      have path :
          (FiniteOccurrenceLookup.gslt Nat
            (HeapEntry Identity Value Other)).RewritePath
              (scanState ⟨heap, .lookup index⟩)
              (scanState ⟨heap, .foundOpaque index value⟩) := by
        simpa [scanState, exactLookup] using
          (FiniteOccurrenceLookup.complete index (indexedHeap heap))
      exact ⟨rewritePathToExecutionPath path⟩
  | missing heap index absent =>
      have exactLookup :
          FiniteOccurrenceLookup.lookup index (indexedHeap heap) =
            .missing heap.length :=
        (lookup_indexedHeap_missing_iff index heap).2 absent
      have path :
          (FiniteOccurrenceLookup.gslt Nat
            (HeapEntry Identity Value Other)).RewritePath
              (scanState ⟨heap, .lookup index⟩)
              (scanState ⟨heap, .missing index⟩) := by
        simpa [scanState, exactLookup] using
          (FiniteOccurrenceLookup.complete index (indexedHeap heap))
      exact ⟨rewritePathToExecutionPath path⟩

/-- One abstract lookup is realized by the complete proof-relevant cursor
path.  A hit at position `n` takes `n + 1` target steps; a miss takes one step
past every finite occurrence. -/
noncomputable def scanRealization :
    OperationalRealization (directGSLT Identity Value Other)
      (FiniteOccurrenceLookup.gslt Nat
        (HeapEntry Identity Value Other)) where
  mapTerm := scanState
  mapEquiv := by
    intro left right equal
    subst right
    rfl
  mapStep := fun step => Classical.choice (scan_step_has_path step)

/-- OSLF native theory of the direct one-step lookup meaning. -/
def directNTT (Identity Value Other : Type) :
    Mettapedia.OSLF.Framework.IndexedModalFunctor.ForwardModalPredicateTheory :=
  Mettapedia.OSLF.Framework.IndexedModalFunctor.oslfForwardModalObject
    (directGSLT Identity Value Other)

/-- OSLF native theory of the finite cursor realization. -/
def scanNTT (Identity Value Other : Type) :
    Mettapedia.OSLF.Framework.IndexedModalFunctor.ForwardModalPredicateTheory :=
  FiniteOccurrenceLookup.lookupNTT Nat (HeapEntry Identity Value Other)

private def occurrenceCanary : Occurrence Nat String := ⟨17, "same"⟩

private def mixedHeapCanary : List (HeapEntry Nat String String) :=
  [.opaque "assertion", .occurrence occurrenceCanary]

/-- Positive control: an opaque cell retains position zero while the equal
proof value at position one is found through a two-step cursor path. -/
example :
    FiniteOccurrenceLookup.lookup 1 (indexedHeap mixedHeapCanary) =
      .found 1 (.occurrence occurrenceCanary) := by
  decide

/-- Negative control: the opaque position cannot be returned as a proof
occurrence merely because it shares the heterogeneous index space. -/
example :
    FiniteOccurrenceLookup.lookup 0 (indexedHeap mixedHeapCanary) =
      .found 0 (.opaque "assertion") := by
  decide

example :
    FiniteOccurrenceLookup.lookup 2 (indexedHeap mixedHeapCanary) =
      .missing 2 := by
  decide

#print axioms indexedHeapFrom_length
#print axioms lookupFrom_indexedHeapFrom
#print axioms lookup_indexedHeap
#print axioms lookup_indexedHeap_found_iff
#print axioms lookup_indexedHeap_missing_iff
#print axioms scan_step_has_path
#print axioms scanRealization

end Mettapedia.GSLT.FiniteHeapLookupRealization
