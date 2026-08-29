import Mettapedia.GSLT.Core.FiniteHeapLookupRealization

/-!
# Speculative finite heap lookup

A set-indexed runtime need not linearly scan every successful heap lookup.
It may first ask for the exact owner/index cell and return immediately when
that cell exists.  Only a failed exact probe enters a finite cursor walk whose
sole job is to reach the explicit live frontier and justify `missing`.

This is an operational fusion, not an absence oracle.  The semantic start of
the fallback is justified by `getElem? = none`; a concrete scheduled runtime
must separately prove that its direct-hit rule is exhausted before it enables
the fallback rule.  Reserved representation capacity is retained in the state
but never changes the live frontier.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.SpeculativeFiniteHeapLookup

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.IndexedModalFunctor

variable {Identity Value Other Cell : Type}

abbrev HeapEntry (Identity Value Other : Type) :=
  OccurrenceHeapProtocol.Entry Identity Value Other

/-- The fallback retains the requested index while walking only the live heap
frontier.  Terminal states retain both the query and its exact observation. -/
inductive Control (Cell : Type) where
  | request (index : Nat)
  | fallback (index cursor : Nat)
  | finished (index : Nat) (observation : FiniteOccurrenceLookup.Observation Cell)
deriving DecidableEq

structure State (Cell : Type) where
  heap : List Cell
  reserve : Nat
  control : Control Cell
deriving DecidableEq

namespace State

def liveFrontier (state : State Cell) : Nat := state.heap.length

def capacity (state : State Cell) : Nat := state.heap.length + state.reserve

end State

/-- Direct hits are single steps.  A missing exact cell begins a bounded walk;
the walk advances only over live cells and terminates at the explicit frontier. -/
inductive Step : State Cell → State Cell → Prop where
  | hit (heap : List Cell) (reserve index : Nat) (entry : Cell)
      (found : heap[index]? = some entry) :
      Step ⟨heap, reserve, .request index⟩
        ⟨heap, reserve, .finished index (.found index entry)⟩
  | startFallback (heap : List Cell) (reserve index : Nat)
      (absent : heap[index]? = none) :
      Step ⟨heap, reserve, .request index⟩
        ⟨heap, reserve, .fallback index 0⟩
  | advance (heap : List Cell) (reserve index cursor : Nat) (entry : Cell)
      (found : heap[cursor]? = some entry) :
      Step ⟨heap, reserve, .fallback index cursor⟩
        ⟨heap, reserve, .fallback index (cursor + 1)⟩
  | missing (heap : List Cell) (reserve index : Nat) :
      Step ⟨heap, reserve, .fallback index heap.length⟩
        ⟨heap, reserve, .finished index (.missing heap.length)⟩

def gslt (Cell : Type) : GSLT where
  Term := State Cell
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

/-- The semantic hybrid has one successor at every nonterminal state.  The
direct and fallback starts are separated by exact `getElem?` evidence, and a
live advance cannot compete with the frontier step. -/
theorem step_deterministic {source left right : State Cell}
    (first : Step source left) (second : Step source right) : left = right := by
  cases first <;> cases second <;> simp_all

/-- Every fallback advance begins strictly below the live frontier. -/
theorem advance_begins_live
    {heap : List Cell} {reserve index cursor : Nat} {target : State Cell}
    (step : Step ⟨heap, reserve, .fallback index cursor⟩ target)
    (advances : target.control = .fallback index (cursor + 1)) :
    cursor < heap.length := by
  cases step with
  | advance _ _ _ _ entry found =>
      exact (List.getElem?_eq_some_iff.mp found).1
  | missing => simp at advances

/-- Reserved capacity cannot license a walk step beginning at the live
frontier. -/
theorem no_advance_from_live_frontier
    (heap : List Cell) (reserve index : Nat) :
    ¬ Step ⟨heap, reserve, .fallback index heap.length⟩
        ⟨heap, reserve, .fallback index (heap.length + 1)⟩ := by
  intro step
  have live := advance_begins_live step rfl
  omega

/-- Walk a missing query from an arbitrary occurrence cursor to the exact
frontier.  The complete heap is preserved at every step. -/
def finishMissingFrom (reserve index : Nat)
    (visited remaining : List Cell) :
    ExecutionPath (gslt Cell)
      ⟨visited ++ remaining, reserve, .fallback index visited.length⟩
      ⟨visited ++ remaining, reserve,
        .finished index (.missing (visited ++ remaining).length)⟩ := by
  induction remaining generalizing visited with
  | nil =>
      let terminal : State Cell :=
        ⟨visited, reserve, .finished index (.missing visited.length)⟩
      simpa using
        (.cons
          ⟨Step.missing visited reserve index⟩
          (.refl terminal))
  | cons entry remaining induction =>
      have step : Step
          ⟨visited ++ entry :: remaining, reserve,
            .fallback index visited.length⟩
          ⟨visited ++ entry :: remaining, reserve,
            .fallback index (visited.length + 1)⟩ :=
        Step.advance (visited ++ entry :: remaining) reserve index
          visited.length entry (by simp)
      refine .cons ⟨step⟩ ?_
      simpa [List.append_assoc] using induction (visited ++ [entry])

/-- A semantically absent exact cell reaches the explicit live frontier and
returns `missing`. -/
def finishMissing (heap : List Cell) (reserve index : Nat)
    (absent : heap[index]? = none) :
    ExecutionPath (gslt Cell)
      ⟨heap, reserve, .request index⟩
      ⟨heap, reserve, .finished index (.missing heap.length)⟩ :=
  .cons ⟨Step.startFallback heap reserve index absent⟩
    (by simpa using finishMissingFrom reserve index [] heap)

/-- Endpoint transport does not change the retained number of operational
steps. -/
private def castPath {source target source' target' : State Cell}
    (sourceEqual : source = source') (targetEqual : target = target')
    (path : ExecutionPath (gslt Cell) source target) :
    ExecutionPath (gslt Cell) source' target' := by
  subst source'
  subst target'
  exact path

@[simp] private theorem castPath_length
    {source target source' target' : State Cell}
    (sourceEqual : source = source') (targetEqual : target = target')
    (path : ExecutionPath (gslt Cell) source target) :
    (castPath sourceEqual targetEqual path).length = path.length := by
  subst source'
  subst target'
  rfl

/-- There exists a fallback path with exactly one step per remaining live cell
followed by one frontier observation. -/
theorem finishMissingFrom_has_exact_cost (reserve index : Nat)
    (visited remaining : List Cell) :
    ∃ path : ExecutionPath (gslt Cell)
        ⟨visited ++ remaining, reserve, .fallback index visited.length⟩
        ⟨visited ++ remaining, reserve,
          .finished index (.missing (visited ++ remaining).length)⟩,
      path.length = remaining.length + 1 := by
  induction remaining generalizing visited with
  | nil =>
      let terminal : State Cell :=
        ⟨visited, reserve, .finished index (.missing visited.length)⟩
      let path : ExecutionPath (gslt Cell)
          ⟨visited, reserve, .fallback index visited.length⟩ terminal :=
        .cons ⟨Step.missing visited reserve index⟩ (.refl terminal)
      have sourceEqual :
          (⟨visited, reserve, .fallback index visited.length⟩ : State Cell) =
          ⟨visited ++ [], reserve, .fallback index visited.length⟩ := by
        simp
      have targetEqual : terminal =
          ⟨visited ++ [], reserve,
            .finished index (.missing (visited ++ []).length)⟩ := by
        simp [terminal]
      let path' := castPath sourceEqual targetEqual path
      refine ⟨path', ?_⟩
      have lengthEqual : path'.length = path.length := by
        simp [path']
      rw [lengthEqual]
      rfl
  | cons entry remaining induction =>
      obtain ⟨rest, restLength⟩ := induction (visited ++ [entry])
      have sourceEqual :
          (⟨(visited ++ [entry]) ++ remaining, reserve,
            .fallback index (visited ++ [entry]).length⟩ : State Cell) =
          ⟨visited ++ entry :: remaining, reserve,
            .fallback index (visited.length + 1)⟩ := by
        simp [List.append_assoc]
      have targetEqual :
          (⟨(visited ++ [entry]) ++ remaining, reserve,
            .finished index
              (.missing ((visited ++ [entry]) ++ remaining).length)⟩ :
            State Cell) =
          ⟨visited ++ entry :: remaining, reserve,
            .finished index (.missing
              (visited ++ entry :: remaining).length)⟩ := by
        simp [List.append_assoc]
      let rest' : ExecutionPath (gslt Cell)
          ⟨visited ++ entry :: remaining, reserve,
            .fallback index (visited.length + 1)⟩
          ⟨visited ++ entry :: remaining, reserve,
            .finished index (.missing (visited ++ entry :: remaining).length)⟩ := by
        exact castPath sourceEqual targetEqual rest
      have restLength' : rest'.length = remaining.length + 1 := by
        simpa [rest'] using restLength
      let first : Step
          ⟨visited ++ entry :: remaining, reserve,
            .fallback index visited.length⟩
          ⟨visited ++ entry :: remaining, reserve,
            .fallback index (visited.length + 1)⟩ :=
        Step.advance (visited ++ entry :: remaining) reserve index
          visited.length entry (by simp)
      let path : ExecutionPath (gslt Cell)
          ⟨visited ++ entry :: remaining, reserve,
            .fallback index visited.length⟩
          ⟨visited ++ entry :: remaining, reserve,
            .finished index (.missing (visited ++ entry :: remaining).length)⟩ :=
        .cons ⟨first⟩ rest'
      refine ⟨path, ?_⟩
      change rest'.length + 1 = remaining.length + 1 + 1
      rw [restLength']

/-- A complete missing query has an exact-cost path: fallback start, one step
per live cell, and the terminal frontier step. -/
theorem finishMissing_has_exact_cost (heap : List Cell) (reserve index : Nat)
    (absent : heap[index]? = none) :
    ∃ path : ExecutionPath (gslt Cell)
        ⟨heap, reserve, .request index⟩
        ⟨heap, reserve, .finished index (.missing heap.length)⟩,
      path.length = heap.length + 2 := by
  obtain ⟨rest, restLength⟩ :=
    finishMissingFrom_has_exact_cost reserve index [] heap
  let first : Step ⟨heap, reserve, .request index⟩
      ⟨heap, reserve, .fallback index 0⟩ :=
    Step.startFallback heap reserve index absent
  let path : ExecutionPath (gslt Cell)
      ⟨heap, reserve, .request index⟩
      ⟨heap, reserve, .finished index (.missing heap.length)⟩ :=
    .cons ⟨first⟩ (by simpa using rest)
  refine ⟨path, ?_⟩
  change rest.length + 1 = heap.length + 2
  rw [restLength]

/-- Embed the direct heterogeneous heap meaning into the speculative target.
Owner matching remains a preceding activation obligation, exactly as in the
direct source calculus. -/
def mapState (reserve : Nat) :
    FiniteHeapLookupRealization.State Identity Value Other →
      State (HeapEntry Identity Value Other)
  | ⟨heap, .lookup index⟩ =>
      ⟨heap, reserve, .request index⟩
  | ⟨heap, .foundOccurrence index occurrence⟩ =>
      ⟨heap, reserve,
        .finished index (.found index (.occurrence occurrence))⟩
  | ⟨heap, .foundOpaque index value⟩ =>
      ⟨heap, reserve, .finished index (.found index (.opaque value))⟩
  | ⟨heap, .missing index⟩ =>
      ⟨heap, reserve, .finished index (.missing heap.length)⟩

/-- One direct semantic lookup has either one indexed-hit path or the finite
frontier-witness path.  The proposition-valued wrapper permits elimination of
the semantic step proof without erasing the selected path inside the witness. -/
theorem step_has_path (reserve : Nat)
    {source target : FiniteHeapLookupRealization.State Identity Value Other}
    (step : FiniteHeapLookupRealization.Step source target) :
    Nonempty
      (ExecutionPath (gslt (HeapEntry Identity Value Other))
        (mapState reserve source) (mapState reserve target)) := by
  cases step with
  | occurrence heap index occurrence found =>
      exact ⟨.cons
        ⟨Step.hit heap reserve index (.occurrence occurrence) found⟩
        (.refl _)⟩
  | «opaque» heap index value found =>
      exact ⟨.cons ⟨Step.hit heap reserve index (.opaque value) found⟩
        (.refl _)⟩
  | missing heap index absent =>
      exact ⟨finishMissing heap reserve index absent⟩

/-- Reusable GSLT-to-GSLT realization of direct indexed heap meaning by the
speculative MM2-shaped machine. -/
noncomputable def realization (reserve : Nat) :
    OperationalRealization
      (FiniteHeapLookupRealization.directGSLT Identity Value Other)
      (gslt (HeapEntry Identity Value Other)) where
  mapTerm := mapState reserve
  mapEquiv := by
    intro left right equal
    subst right
    rfl
  mapStep := fun step => Classical.choice (step_has_path reserve step)

/-- OSLF transport for the finite macro-step behavior of the speculative
realization. -/
noncomputable def reachabilityNTT (reserve : Nat) :
    ForwardModalPredicateTheory.Hom
      (oslfForwardModalObject
        (gslt (HeapEntry Identity Value Other)).closure)
      (oslfForwardModalObject
        (FiniteHeapLookupRealization.directGSLT Identity Value Other).closure) :=
  (realization (Identity := Identity) (Value := Value) (Other := Other)
    reserve).closureOSLFPullback

private def occurrenceCanary : OccurrenceHeapProtocol.Occurrence Nat String :=
  ⟨41, "same"⟩

private def heapCanary : List (HeapEntry Nat String String) :=
  [.opaque "assertion", .occurrence occurrenceCanary]

/-- Positive control: a direct proof-cell hit is one primitive target step. -/
example :
    Step ⟨heapCanary, 3, .request 1⟩
      ⟨heapCanary, 3,
        .finished 1 (.found 1 (.occurrence occurrenceCanary))⟩ := by
  exact Step.hit heapCanary 3 1 (.occurrence occurrenceCanary) (by decide)

/-- Positive missing control: a query outside the heap has a complete finite
fallback path even when representation capacity is reserved. -/
example : Nonempty
    (ExecutionPath (gslt (HeapEntry Nat String String))
      ⟨heapCanary, 3, .request 7⟩
      ⟨heapCanary, 3, .finished 7 (.missing 2)⟩) := by
  exact ⟨finishMissing heapCanary 3 7 (by decide)⟩

/-- Negative control: an opaque entry is not reclassified as a proof
occurrence by the direct path. -/
example :
    ¬ Step ⟨heapCanary, 3, .request 0⟩
      ⟨heapCanary, 3,
        .finished 0 (.found 0 (.occurrence occurrenceCanary))⟩ := by
  intro step
  cases step
  simp_all [heapCanary]

#print axioms step_deterministic
#print axioms advance_begins_live
#print axioms no_advance_from_live_frontier
#print axioms finishMissingFrom
#print axioms finishMissing
#print axioms finishMissingFrom_has_exact_cost
#print axioms finishMissing_has_exact_cost
#print axioms step_has_path
#print axioms realization
#print axioms reachabilityNTT

end Mettapedia.GSLT.SpeculativeFiniteHeapLookup
