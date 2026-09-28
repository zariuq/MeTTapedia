import Mettapedia.Machines.ResourceOwnershipOptimality
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort

/-!
# A finite worklist tracer and its graph work

`run` maintains disjoint expanded and pending sets. It selects a pending
address, reads its references, marks the address, and inserts its successors
after subtracting the expanded set. Thus cycles and shared descendants do not
cause repeated expansion. Its executable definitions never use `Live` or
`footprint`. The allocation cardinality supplies a termination bound, not an
enumeration of all allocated cells' references.

The counters concern heap expansions and the explicit reference loop's visits.
Root enumeration, the allocation-cardinality bound, frontier selection, set
membership/insertion/difference, and the retained audit log have separate
representation costs, including sorting the outgoing reference enumeration.
In particular, these theorems do not make the `Finset`
implementation a constant-time set or establish physical linear runtime.
References in the existing heap model are sets: repeated pointer slots within
one concrete runtime cell would require a slot enumeration and its own cost.

Address ordering supplies executable frontier selection. No finite address
universe, acyclicity, exclusive ownership, or bound on future heaps is required.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ResourceOwnership.TraceWork

open Mettapedia.GSLT.Dynamics.StoreReachability (Reach)

universe uValue uOwner

variable {Address : Type} {Value : Type uValue} {Owner : Type uOwner}
  [LinearOrder Address]

/-- One lookup exposes a cell's distinct outgoing references. -/
def successors (heap : Heap Address Value) (address : Address) : Finset Address :=
  ((heap.lookup address).map Cell.references).getD ∅

omit [LinearOrder Address] in
theorem mem_successors (heap : Heap Address Value) (address next : Address) :
    next ∈ successors heap address ↔
      ∃ cell, heap.lookup address = some cell ∧ next ∈ cell.references := by
  cases found : heap.lookup address <;> simp [successors, found]

theorem successors_live (heap : Heap Address Value) (roots : Roots Owner Address)
    {address next : Address} (live : Live heap roots address)
    (edge : next ∈ successors heap address) : Live heap roots next := by
  obtain ⟨cell, found, reference⟩ := (mem_successors heap address next).mp edge
  exact live_step heap roots live found reference

structure State (Address : Type) where
  seen : Finset Address
  pending : Finset Address
  deriving DecidableEq

/-- The address is marked before successors enter the frontier. -/
def advance (state : State Address) (address : Address)
    (references : Finset Address) : State Address where
  seen := insert address state.seen
  pending := (state.pending ∪ references) \ insert address state.seen

/-- An explicit reference-enumeration loop, with one tick for every list
entry even when the target is already expanded or pending. Set operations
inside each iteration are not charged as constant-time operations. -/
def scanReferences (seen : Finset Address) :
    Finset Address → List Address → Finset Address × Nat
  | pending, [] => (pending, 0)
  | pending, address :: rest =>
      let pending := if address ∈ seen then pending else insert address pending
      let scanned := scanReferences seen pending rest
      (scanned.1, scanned.2 + 1)

theorem scanReferences_eq (seen pending : Finset Address) (references : List Address) :
    scanReferences seen pending references =
      (pending ∪ (references.toFinset \ seen), references.length) := by
  induction references generalizing pending with
  | nil => simp [scanReferences]
  | cons address rest ih =>
      simp only [scanReferences, ih, List.toFinset_cons, List.length_cons]
      apply Prod.ext
      · ext node
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert]
        split <;> rename_i condition
        · constructor
          · tauto
          · rintro (old | ⟨same | later, fresh⟩)
            · exact Or.inl old
            · subst node
              exact False.elim (fresh condition)
            · exact Or.inr ⟨later, fresh⟩
        · simp only [Finset.mem_insert]
          constructor
          · rintro ((rfl | old) | later)
            · exact Or.inr ⟨Or.inl rfl, condition⟩
            · exact Or.inl old
            · exact Or.inr ⟨Or.inr later.1, later.2⟩
          · tauto
      · rfl

/-- Prepare one expansion by reading each reference through `scanReferences`.
Sorting supplies a concrete enumeration of the finite reference set. -/
def expansion (state : State Address) (address : Address)
    (references : Finset Address) : State Address × Nat :=
  let seen := insert address state.seen
  let scanned := scanReferences seen (state.pending \ seen) (references.sort (· ≤ ·))
  (⟨seen, scanned.1⟩, scanned.2)

theorem expansion_eq (state : State Address) (address : Address)
    (references : Finset Address) :
    expansion state address references = (advance state address references, references.card) := by
  simp only [expansion, scanReferences_eq, Finset.sort_toFinset, Finset.length_sort]
  congr 2
  ext node
  simp only [Finset.mem_union, Finset.mem_sdiff]
  tauto

structure Trace (Address : Type) where
  final : State Address
  expanded : List Address
  edgeVisits : Nat
  deriving DecidableEq

/-- Fuel bounds expansion rounds. An empty frontier returns immediately. -/
def run (heap : Heap Address Value) : Nat → State Address → Trace Address
  | 0, state => ⟨state, [], 0⟩
  | fuel + 1, state =>
      if nonempty : state.pending.Nonempty then
        let address := state.pending.min' nonempty
        let references := successors heap address
        let step := expansion state address references
        let rest := run heap fuel step.1
        ⟨rest.final, address :: rest.expanded, step.2 + rest.edgeVisits⟩
      else ⟨state, [], 0⟩

/-- Invalid roots are ignored, just as in `Heap.toStore`; no validity premise
is needed for the tracer's equivalence with the existing semantics. -/
def initial (heap : Heap Address Value) (roots : Roots Owner Address) : State Address where
  seen := ∅
  pending := rootAddresses roots ∩ heap.allocated

def trace (heap : Heap Address Value) (roots : Roots Owner Address) : Trace Address :=
  run heap heap.allocated.card (initial heap roots)

/-- Local frontier invariant: expanded nodes have exposed all their outgoing
edges, and every exposed but unexpanded address is pending. -/
structure Invariant (heap : Heap Address Value) (roots : Roots Owner Address)
    (state : State Address) : Prop where
  seen_live : ∀ address ∈ state.seen, Live heap roots address
  pending_live : ∀ address ∈ state.pending, Live heap roots address
  disjoint : Disjoint state.seen state.pending
  roots_covered : rootAddresses roots ∩ heap.allocated ⊆ state.seen ∪ state.pending
  edges_covered : ∀ address ∈ state.seen,
    successors heap address ⊆ state.seen ∪ state.pending

theorem initial_invariant (heap : Heap Address Value) (roots : Roots Owner Address) :
    Invariant heap roots (initial heap roots) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [initial]
  · intro address member
    rcases Finset.mem_inter.mp member with ⟨root, allocated⟩
    exact Reach.root ⟨allocated, root⟩
  · simp [initial]
  · simp [initial]
  · simp [initial]

theorem advance_union (state : State Address) (address : Address)
    (references : Finset Address) :
    (advance state address references).seen ∪
      (advance state address references).pending =
        insert address (state.seen ∪ state.pending ∪ references) := by
  ext node
  simp only [advance, Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert]
  tauto

theorem advance_invariant (heap : Heap Address Value) (roots : Roots Owner Address)
    (state : State Address) (invariant : Invariant heap roots state)
    {address : Address} (member : address ∈ state.pending) :
    Invariant heap roots (advance state address (successors heap address)) := by
  have live := invariant.pending_live address member
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro node inside
    rcases Finset.mem_insert.mp inside with rfl | old
    · exact live
    · exact invariant.seen_live node old
  · intro node inside
    rcases Finset.mem_sdiff.mp inside with ⟨exposed, _⟩
    rcases Finset.mem_union.mp exposed with pending | edge
    · exact invariant.pending_live node pending
    · exact successors_live heap roots live edge
  · apply Finset.disjoint_left.mpr
    intro node expanded pending
    exact (Finset.mem_sdiff.mp pending).2 expanded
  · rw [advance_union]
    intro node rooted
    exact Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (invariant.roots_covered rooted))
  · intro node inside next edge
    rw [advance_union]
    rcases Finset.mem_insert.mp inside with rfl | old
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ edge)
    · exact Finset.mem_insert_of_mem
        (Finset.mem_union_left _ (invariant.edges_covered node old edge))

theorem run_invariant (heap : Heap Address Value) (roots : Roots Owner Address)
    (fuel : Nat) (state : State Address) (invariant : Invariant heap roots state) :
    Invariant heap roots (run heap fuel state).final := by
  induction fuel generalizing state with
  | zero => exact invariant
  | succ fuel ih =>
      simp only [run, expansion_eq]
      split
      next nonempty =>
        exact ih _ (advance_invariant heap roots state invariant
          (Finset.min'_mem _ nonempty))
      next _ => exact invariant

theorem selected_fresh (heap : Heap Address Value) (roots : Roots Owner Address)
    (state : State Address) (invariant : Invariant heap roots state)
    {address : Address} (member : address ∈ state.pending) : address ∉ state.seen :=
  fun old => Finset.disjoint_left.mp invariant.disjoint old member

theorem run_seen (heap : Heap Address Value) (fuel : Nat) (state : State Address)
    (address : Address) :
    address ∈ (run heap fuel state).final.seen ↔
      address ∈ state.seen ∨ address ∈ (run heap fuel state).expanded := by
  induction fuel generalizing state with
  | zero => simp [run]
  | succ fuel ih =>
      simp only [run, expansion_eq]
      split
      next nonempty =>
        rw [ih]
        simp only [advance, Finset.mem_insert, List.mem_cons]
        tauto
      next _ => simp

theorem expanded_fresh (heap : Heap Address Value) (roots : Roots Owner Address)
    (fuel : Nat) (state : State Address) (invariant : Invariant heap roots state) :
    ∀ address ∈ (run heap fuel state).expanded, address ∉ state.seen := by
  induction fuel generalizing state with
  | zero => simp [run]
  | succ fuel ih =>
      simp only [run, expansion_eq]
      split
      next nonempty =>
        intro address member
        rcases List.mem_cons.mp member with rfl | later
        · exact selected_fresh heap roots state invariant (Finset.min'_mem _ nonempty)
        · have fresh := ih _ (advance_invariant heap roots state invariant
            (Finset.min'_mem _ nonempty)) address later
          exact fun old => fresh (Finset.mem_insert_of_mem old)
      next _ => simp

theorem expanded_nodup (heap : Heap Address Value) (roots : Roots Owner Address)
    (fuel : Nat) (state : State Address) (invariant : Invariant heap roots state) :
    (run heap fuel state).expanded.Nodup := by
  induction fuel generalizing state with
  | zero => simp [run]
  | succ fuel ih =>
      simp only [run, expansion_eq]
      split
      next nonempty =>
        have nextInvariant := advance_invariant heap roots state invariant
          (Finset.min'_mem _ nonempty)
        refine List.nodup_cons.mpr ⟨?_, ih _ nextInvariant⟩
        intro repeated
        exact expanded_fresh heap roots fuel _ nextInvariant _ repeated
          (Finset.mem_insert_self _ _)
      next _ => simp

theorem run_exhausted (heap : Heap Address Value) (roots : Roots Owner Address)
    (fuel : Nat) (state : State Address) (invariant : Invariant heap roots state)
    (enough : heap.allocated.card ≤ state.seen.card + fuel) :
    (run heap fuel state).final.pending = ∅ := by
  induction fuel generalizing state with
  | zero =>
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro address member
      have fresh := selected_fresh heap roots state invariant member
      have subset : insert address state.seen ⊆ heap.allocated := by
        intro node inside
        rcases Finset.mem_insert.mp inside with rfl | old
        · exact live_allocated heap roots (invariant.pending_live node member)
        · exact live_allocated heap roots (invariant.seen_live node old)
      have bound := Finset.card_le_card subset
      rw [Finset.card_insert_of_notMem fresh] at bound
      omega
  | succ fuel ih =>
      simp only [run, expansion_eq]
      split
      next nonempty =>
        apply ih _ (advance_invariant heap roots state invariant
          (Finset.min'_mem _ nonempty))
        have fresh := selected_fresh heap roots state invariant (Finset.min'_mem _ nonempty)
        simp only [advance, Finset.card_insert_of_notMem fresh]
        omega
      next empty => exact Finset.not_nonempty_iff_eq_empty.mp empty

theorem exhausted_seen (heap : Heap Address Value) (roots : Roots Owner Address)
    (state : State Address) (invariant : Invariant heap roots state)
    (empty : state.pending = ∅) : state.seen = footprint heap roots := by
  apply Finset.ext
  intro address
  rw [mem_footprint]
  constructor
  · exact invariant.seen_live address
  · intro live
    induction live with
    | root rooted =>
        simpa only [empty, Finset.union_empty] using
          invariant.roots_covered (Finset.mem_inter.mpr ⟨rooted.2, rooted.1⟩)
    | @step previous address _ edge ih =>
        simpa only [empty, Finset.union_empty] using
          invariant.edges_covered previous ih ((mem_successors heap previous address).mpr edge)

theorem trace_exhausted (heap : Heap Address Value) (roots : Roots Owner Address) :
    (trace heap roots).final.pending = ∅ := by
  apply run_exhausted heap roots _ _ (initial_invariant heap roots)
  simp [initial]

/-- Two-sided adequacy with the semantic collector's live set. -/
theorem trace_eq_footprint (heap : Heap Address Value) (roots : Roots Owner Address) :
    (trace heap roots).final.seen = footprint heap roots :=
  exhausted_seen heap roots _
    (run_invariant heap roots _ _ (initial_invariant heap roots)) (trace_exhausted heap roots)

theorem trace_expanded_nodup (heap : Heap Address Value) (roots : Roots Owner Address) :
    (trace heap roots).expanded.Nodup :=
  expanded_nodup heap roots _ _ (initial_invariant heap roots)

theorem trace_expanded_iff_live (heap : Heap Address Value) (roots : Roots Owner Address)
    (address : Address) : address ∈ (trace heap roots).expanded ↔ Live heap roots address := by
  have seen := run_seen heap heap.allocated.card (initial heap roots) address
  change address ∈ (trace heap roots).final.seen ↔ _ at seen
  rw [trace_eq_footprint, mem_footprint] at seen
  simpa [initial, trace] using seen.symm

theorem trace_expanded_toFinset (heap : Heap Address Value) (roots : Roots Owner Address) :
    (trace heap roots).expanded.toFinset = footprint heap roots := by
  ext address
  simp only [List.mem_toFinset, trace_expanded_iff_live, mem_footprint]

theorem trace_expansion_count (heap : Heap Address Value) (roots : Roots Owner Address) :
    (trace heap roots).expanded.length = (footprint heap roots).card := by
  rw [← trace_expanded_toFinset]
  exact (List.toFinset_card_of_nodup (trace_expanded_nodup heap roots)).symm

theorem run_edgeVisits (heap : Heap Address Value) (fuel : Nat) (state : State Address) :
    (run heap fuel state).edgeVisits =
      ((run heap fuel state).expanded.map fun address => (successors heap address).card).sum := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      simp only [run, expansion_eq]
      split
      next _ => simp only [List.map_cons, List.sum_cons, ih]
      next _ => rfl

/-- The explicit scan loop visits every distinct outgoing reference of each
live cell once. Edges leading to an already seen cell still contribute a tick.
Sorting and set operations may themselves inspect addresses additionally. -/
theorem trace_edge_count (heap : Heap Address Value) (roots : Roots Owner Address) :
    (trace heap roots).edgeVisits =
      ∑ address ∈ footprint heap roots, (successors heap address).card := by
  rw [show (trace heap roots).edgeVisits =
      ((trace heap roots).expanded.map fun address => (successors heap address).card).sum from
      run_edgeVisits heap _ _, ← trace_expanded_toFinset]
  exact (List.sum_toFinset _ (trace_expanded_nodup heap roots)).symm

/-- A heap built from the computed marking set, rather than deciding semantic
reachability at lookup time. The marking set is retained in this heap value. -/
def collectTraced (heap : Heap Address Value) (roots : Roots Owner Address) :
    Heap Address Value :=
  let marked := (trace heap roots).final.seen
  { lookup := fun address => if address ∈ marked then heap.lookup address else none
    allocated := marked
    allocated_iff := by
      intro address
      by_cases inside : address ∈ marked
      · simp only [inside, if_pos, true_iff]
        apply (heap.allocated_iff address).mp
        exact live_allocated heap roots ((mem_footprint heap roots address).mp
          (trace_eq_footprint heap roots ▸ inside))
      · simp [inside]
    closed := by
      intro address cell found next reference
      split at found
      next inside =>
        change next ∈ (trace heap roots).final.seen
        rw [trace_eq_footprint, mem_footprint]
        apply live_step heap roots _ found reference
        exact (mem_footprint heap roots address).mp (trace_eq_footprint heap roots ▸ inside)
      next _ => cases found }

theorem collectTraced_allocated (heap : Heap Address Value) (roots : Roots Owner Address) :
    (collectTraced heap roots).allocated = (collect heap roots).allocated :=
  trace_eq_footprint heap roots

theorem collectTraced_lookup (heap : Heap Address Value) (roots : Roots Owner Address)
    (address : Address) :
    (collectTraced heap roots).lookup address = (collect heap roots).lookup address := by
  classical
  simp only [collectTraced, trace_eq_footprint, mem_footprint, collect]

/-- Changing root labels or duplicating an address under another owner does
not repeat graph work. Enumerating those owner roots still has its own cost. -/
theorem trace_congr_rootAddresses (heap : Heap Address Value)
    (roots other : Roots Owner Address) (same : rootAddresses roots = rootAddresses other) :
    trace heap roots = trace heap other := by
  simp only [trace, initial, same]

/-! ## Lower bounds for complete traversal surveys

The comparison class starts from root occurrences, queries complete cells,
and certifies closure by following every outgoing reference of each queried
cell. Its local obligations mention roots and one-step edges, not the desired
transitive footprint. Reachability induction then forces every live cell to
occur in its query log. Repeated queries and unrelated queried cells are
permitted, but cannot improve the resulting graph-work lower bounds.

This excludes algorithms reusing a previous marking summary, special semantic
knowledge of the heap, reference counting, region reclamation, and moving or
compressed representations. It is not a black-box lower bound on all possible
collectors or a lower bound on wall-clock time.
-/

/-- The local requirements of a completed, full-reference traversal survey. -/
structure CompleteSurvey (heap : Heap Address Value) (roots : Roots Owner Address)
    (queries : List Address) : Prop where
  roots_queried : ∀ pair ∈ roots, pair.2 ∈ heap.allocated → pair.2 ∈ queries
  references_queried : ∀ address ∈ queries, ∀ next ∈ successors heap address, next ∈ queries

theorem completeSurvey_covers (heap : Heap Address Value) (roots : Roots Owner Address)
    (queries : List Address) (survey : CompleteSurvey heap roots queries) :
    footprint heap roots ⊆ queries.toFinset := by
  intro address member
  rw [List.mem_toFinset]
  have live := (mem_footprint heap roots address).mp member
  clear member
  induction live with
  | root rooted =>
      obtain ⟨pair, member, same⟩ := Finset.mem_image.mp rooted.2
      exact same ▸ survey.roots_queried pair member (same.symm ▸ rooted.1)
  | @step previous address _ edge ih =>
      exact survey.references_queried previous ih address
        ((mem_successors heap previous address).mpr edge)

theorem trace_completeSurvey (heap : Heap Address Value) (roots : Roots Owner Address) :
    CompleteSurvey heap roots (trace heap roots).expanded := by
  constructor
  · intro pair member allocated
    exact (trace_expanded_iff_live heap roots pair.2).mpr
      (live_of_root heap roots member allocated)
  · intro address queried next edge
    exact (trace_expanded_iff_live heap roots next).mpr
      (successors_live heap roots ((trace_expanded_iff_live heap roots address).mp queried) edge)

/-- Each query in this comparison class enumerates its complete reference
set. This includes repeated enumeration when a cell is queried repeatedly. -/
def surveyEdgeWork (heap : Heap Address Value) (queries : List Address) : Nat :=
  (queries.map fun address => (successors heap address).card).sum

theorem finiteSum_le_listSum (weight : Address → Nat) (queries : List Address) :
    (∑ address ∈ queries.toFinset, weight address) ≤ (queries.map weight).sum := by
  induction queries with
  | nil => simp
  | cons address rest ih =>
      simp only [List.toFinset_cons, List.map_cons, List.sum_cons]
      by_cases repeated : address ∈ rest.toFinset
      · rw [Finset.insert_eq_of_mem repeated]
        omega
      · rw [Finset.sum_insert repeated]
        omega

theorem trace_minimal_expansions (heap : Heap Address Value) (roots : Roots Owner Address)
    (queries : List Address) (survey : CompleteSurvey heap roots queries) :
    (trace heap roots).expanded.length ≤ queries.length := by
  rw [trace_expansion_count]
  exact (Finset.card_le_card (completeSurvey_covers heap roots queries survey)).trans
    (List.toFinset_card_le queries)

theorem trace_minimal_edgeVisits (heap : Heap Address Value) (roots : Roots Owner Address)
    (queries : List Address) (survey : CompleteSurvey heap roots queries) :
    (trace heap roots).edgeVisits ≤ surveyEdgeWork heap queries := by
  rw [trace_edge_count]
  exact (Finset.sum_le_sum_of_subset
    (f := fun address => (successors heap address).card)
    (completeSurvey_covers heap roots queries survey)).trans
      (finiteSum_le_listSum _ queries)

/-- Both graph-work lower bounds are attained by the actual worklist run. -/
theorem trace_attains_graph_work_minimum (heap : Heap Address Value)
    (roots : Roots Owner Address) :
    CompleteSurvey heap roots (trace heap roots).expanded ∧
      (trace heap roots).edgeVisits = surveyEdgeWork heap (trace heap roots).expanded ∧
      ∀ queries, CompleteSurvey heap roots queries →
        (trace heap roots).expanded.length ≤ queries.length ∧
          (trace heap roots).edgeVisits ≤ surveyEdgeWork heap queries := by
  refine ⟨trace_completeSurvey heap roots, run_edgeVisits heap _ _, ?_⟩
  intro queries survey
  exact ⟨trace_minimal_expansions heap roots queries survey,
    trace_minimal_edgeVisits heap roots queries survey⟩

theorem trace_graph_work_exact (heap : Heap Address Value) (roots : Roots Owner Address) :
    (trace heap roots).expanded.length + (trace heap roots).edgeVisits =
      (footprint heap roots).card +
        ∑ address ∈ footprint heap roots, (successors heap address).card := by
  rw [trace_expansion_count, trace_edge_count]

/-! ## Executable controls -/

namespace Controls

open Examples

/-- The same algorithm handles arbitrarily long current heaps over `Nat`;
there is no fixed global address cap hidden in the finite allocation set. -/
theorem chain_expansion_count (last : Nat) :
    (trace (chainHeap last) oneRoot).expanded.length = last + 1 := by
  rw [trace_expansion_count, chain_footprint]
  exact Finset.card_range _

def sharedCycleRoots : Roots Nat (Fin 3) := {(0, 0), (1, 2)}

/-- The second root and the back edge share node 2, but every node is expanded
once. The closing edge 2 -> 1 is still counted. -/
theorem shared_cycle_once :
    (trace cyclicHeap sharedCycleRoots).expanded = [0, 1, 2] ∧
      (trace cyclicHeap sharedCycleRoots).edgeVisits = 3 := by
  change (run cyclicHeap 3 (initial cyclicHeap sharedCycleRoots)).expanded = [0, 1, 2] ∧
    (run cyclicHeap 3 (initial cyclicHeap sharedCycleRoots)).edgeVisits = 3
  simp only [run, expansion_eq]
  decide

theorem unrelated_garbage_not_expanded :
    (trace cyclicHeap ({(0, 1)} : Roots Nat (Fin 3))).expanded = [1, 2] ∧
      (trace cyclicHeap ({(0, 1)} : Roots Nat (Fin 3))).edgeVisits = 2 ∧
      (collectTraced cyclicHeap ({(0, 1)} : Roots Nat (Fin 3))).lookup 0 = none := by
  change (run cyclicHeap 3 (initial cyclicHeap ({(0, 1)} : Roots Nat (Fin 3)))).expanded = [1, 2] ∧
    (run cyclicHeap 3 (initial cyclicHeap ({(0, 1)} : Roots Nat (Fin 3)))).edgeVisits = 2 ∧ _
  simp only [collectTraced, trace]
  change (run cyclicHeap 3 (initial cyclicHeap ({(0, 1)} : Roots Nat (Fin 3)))).expanded = [1, 2] ∧
    (run cyclicHeap 3 (initial cyclicHeap ({(0, 1)} : Roots Nat (Fin 3)))).edgeVisits = 2 ∧
    (if 0 ∈ (run cyclicHeap 3 (initial cyclicHeap ({(0, 1)} : Roots Nat (Fin 3)))).final.seen
      then cyclicHeap.lookup 0 else none) = none
  simp only [run, expansion_eq]
  decide

theorem duplicate_root_addresses_same_graph_work :
    trace cyclicHeap ({(0, 1), (1, 1)} : Roots Nat (Fin 3)) =
      trace cyclicHeap ({(0, 1)} : Roots Nat (Fin 3)) :=
  trace_congr_rootAddresses cyclicHeap _ _ (by decide)

/-- Repeated entries in an input enumeration still consume visits, even when
the queue correctly deduplicates their target. -/
theorem repeated_reference_is_counted :
    scanReferences ({0} : Finset Nat) ∅ [0, 1, 1] = ({1}, 3) := by decide

/-- Stopping after one expansion leaves a live descendant unexpanded. A
budget boundary therefore cannot be reported as completed tracing. -/
theorem premature_stop_loses_live_descendant :
    (run cyclicHeap 1 (initial cyclicHeap sharedCycleRoots)).final.pending ≠ ∅ ∧
      1 ∉ (run cyclicHeap 1 (initial cyclicHeap sharedCycleRoots)).final.seen ∧
      Live cyclicHeap sharedCycleRoots 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [run, expansion_eq]
    decide
  · simp only [run, expansion_eq]
    decide
  · apply (trace_expanded_iff_live cyclicHeap sharedCycleRoots 1).mp
    rw [shared_cycle_once.1]
    decide

theorem root_queries_alone_do_not_certify_closure :
    ¬ CompleteSurvey cyclicHeap ({(0, 0)} : Roots Nat (Fin 3)) [0] := by
  intro survey
  have impossible := survey.references_queried 0 (by decide) 1 (by decide)
  simp at impossible

theorem redundant_queries_strictly_more_work :
    CompleteSurvey cyclicHeap sharedCycleRoots [0, 1, 2, 1] ∧
      (trace cyclicHeap sharedCycleRoots).expanded.length < ([0, 1, 2, 1] : List (Fin 3)).length ∧
      (trace cyclicHeap sharedCycleRoots).edgeVisits <
        surveyEdgeWork cyclicHeap [0, 1, 2, 1] := by
  refine ⟨?_, ?_, ?_⟩
  swap
  · rw [shared_cycle_once.1]
    decide
  swap
  · rw [shared_cycle_once.2]
    decide
  constructor
  · intro pair member _
    simp only [sharedCycleRoots, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl <;> decide
  · intro address _ next _
    have bound := next.isLt
    have cases : next = 0 ∨ next = 1 ∨ next = 2 := by
      have : next.val = 0 ∨ next.val = 1 ∨ next.val = 2 := by omega
      rcases this with h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Fin.ext h))
    rcases cases with rfl | rfl | rfl <;> decide

end Controls

end Mettapedia.Machines.ResourceOwnership.TraceWork
