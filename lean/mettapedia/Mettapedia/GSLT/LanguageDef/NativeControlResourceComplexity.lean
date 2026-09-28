import Mettapedia.GSLT.LanguageDef.NativeControlResources
import Mettapedia.Machines.ResourceTraceWork
import Mettapedia.Machines.ResourceCollectionSchedule
import Mettapedia.Machines.Cursor.QueryLowerBound
import Mettapedia.Machines.Cursor.QueueCost

/-!
# Resource correctness and fragment-specific work bounds

The computed worklist collector now meets the retained-cell and declared-byte
lower bounds of `ResourceOwnershipOptimality`. Its expansion/reference meter
has a separate traversal-class optimum. Set operations, allocator work and
collector workspace remain distinct costs.

The cursor contributions use the same interactive execution protocol as native
controls. `QueryLowerBound` proves a genuine opaque-input query lower bound;
`QueueCost` proves sequential amortized queue work and a persistent-fork
counterexample; `RelationalAmortized` accounts for proposal and conversion work
when changing representations. `ResourceCollectionSchedule` isolates the
space/time tradeoff of repeated full tracing.

These are complementary comparison classes. None states that every language
program has an optimal executor, that minimum retained bytes minimize time,
or that a native implementation satisfies a meter without correspondence.
The contracts quantify over finite requested interactions without requiring
an eventual end to the surrounding computation. Observer-specific relations
can retain answers, bindings, effects or richer evidence as their types require.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ResourceOwnership.TraceWork

universe uValue uOwner

variable {Address : Type} {Value : Type uValue} {Owner : Type uOwner}
  [LinearOrder Address]

theorem collectTraced_allocatedBytes (heap : Heap Address Value) (roots : Roots Owner Address) :
    allocatedBytes (collectTraced heap roots) = allocatedBytes (collect heap roots) := by
  unfold allocatedBytes
  rw [collectTraced_allocated]
  apply Finset.sum_congr rfl
  intro address _
  simp only [cellBytes, collectTraced_lookup]

/-- The actual computed marking set inherits both storage minima from the
path-observation proof, through the separate tracer-correctness theorems. -/
theorem collectTraced_minimal_storage (heap candidate : Heap Address Value)
    (roots : Roots Owner Address)
    (observations : Optimality.SameRootPaths heap candidate roots) :
    (collectTraced heap roots).allocated.card ≤ candidate.allocated.card ∧
      allocatedBytes (collectTraced heap roots) ≤ allocatedBytes candidate := by
  rw [collectTraced_allocated, collectTraced_allocatedBytes]
  exact ⟨Optimality.collect_minimal_cells heap candidate roots observations,
    Optimality.collect_minimal_bytes heap candidate roots observations⟩

/-- Work and space guarantees apply simultaneously, with their distinct
competitor classes visible in the hypotheses. -/
theorem computed_space_and_graph_work (heap candidate : Heap Address Value)
    (roots : Roots Owner Address) (queries : List Address)
    (observations : Optimality.SameRootPaths heap candidate roots)
    (survey : CompleteSurvey heap roots queries) :
    (collectTraced heap roots).allocated.card ≤ candidate.allocated.card ∧
      allocatedBytes (collectTraced heap roots) ≤ allocatedBytes candidate ∧
      (trace heap roots).expanded.length ≤ queries.length ∧
      (trace heap roots).edgeVisits ≤ surveyEdgeWork heap queries := by
  have storage := collectTraced_minimal_storage heap candidate roots observations
  exact ⟨storage.1, storage.2, trace_minimal_expansions heap roots queries survey,
    trace_minimal_edgeVisits heap roots queries survey⟩

end Mettapedia.Machines.ResourceOwnership.TraceWork
