import Mettapedia.Algebra.WorkSpan

/-!
# Resource valuations beyond work and span

`ConcurrentCostAlgebra` is the interface a resource readout must satisfy
to compose along sequential phases and independent branches.  `WorkSpan`
is one instance.  This module adds the other readouts a costed run
admits, and — more usefully — shows that **they do not all fit**.

Three families appear:

* **Additive** resources — energy, communication, message counts.  Both
  compositions accumulate: running two things in parallel does not make
  them cheaper.  These are instances.
* **Work-like / span-like** — the two coordinates of `WorkSpan`: work
  accumulates in both, span accumulates sequentially and takes the slower
  branch in parallel.  Already an instance.
* **Peak allocation** — the high-water mark of concurrently live storage.
  Sequential phases take the *maximum*; independent branches *add*, since
  their allocations coexist.  This is the exact dual of span, and it is
  **not** a `ConcurrentCostAlgebra`: the lax interchange law fails.

The last point is the reason the interface is stated rather than assumed.
Parallelism improves span and *worsens* peak allocation, so no single
scalar readout can stand for "cost"; the resources genuinely conflict and
must be carried plurally.
-/

namespace Mettapedia.Algebra

/-! ## Additive resources: energy, communication -/

/-- Energy, message counts, and similar resources accumulate under both
compositions: two branches running at once spend both their budgets. -/
def additiveAlgebra : ConcurrentCostAlgebra Nat where
  zero := 0
  sequential := (· + ·)
  parallel := (· + ·)
  sequential_zero_left := Nat.zero_add
  sequential_zero_right := Nat.add_zero
  sequential_assoc := fun _ _ _ => Nat.add_assoc _ _ _
  parallel_zero_left := Nat.zero_add
  parallel_zero_right := Nat.add_zero
  parallel_assoc := fun _ _ _ => Nat.add_assoc _ _ _
  parallel_comm := Nat.add_comm
  sequential_mono := fun first second => Nat.add_le_add first second
  parallel_mono := fun first second => Nat.add_le_add first second
  lax_interchange := by
    intro first second third fourth
    omega

/-! ## Peak allocation: the dual, and why it does not fit -/

/-- Peak concurrently-live storage.  Sequential phases reuse storage, so
the peak is the maximum; independent branches hold their allocations at
the same time, so the peak adds. -/
def peakSequential (first second : Nat) : Nat := max first second

/-- Independent branches coexist, so their peaks add. -/
def peakParallel (left right : Nat) : Nat := left + right

/-- **Peak allocation is not a `ConcurrentCostAlgebra`.**  The lax
interchange law fails: splitting two sequential phases across two branches
can strictly increase the peak, because the phases that would have reused
storage now coexist. -/
theorem peakAllocation_violates_lax_interchange :
    ¬ ∀ first second third fourth : Nat,
      peakParallel (peakSequential first second)
          (peakSequential third fourth) ≤
        peakSequential (peakParallel first third)
          (peakParallel second fourth) := by
  intro interchange
  have collision := interchange 1 0 0 1
  simp only [peakSequential, peakParallel] at collision
  omega

/-- The witness, stated positively: one unit allocated in the first phase
of one branch and the second phase of the other.  Serialized the peak is
one; run as independent branches it is two. -/
theorem peakAllocation_parallel_strictly_worse :
    peakSequential (peakParallel 1 0) (peakParallel 0 1) <
      peakParallel (peakSequential 1 0) (peakSequential 0 1) := by
  simp only [peakSequential, peakParallel]
  omega

/-! ## The tension: parallelism cannot improve everything -/

/-- **Span and peak allocation pull in opposite directions.**  For the
same two branches, running them in parallel never increases span and can
strictly increase peak allocation.  No single scalar readout expresses
both, which is why a costed run carries several valuations rather than
one number. -/
theorem parallelism_improves_span_worsens_allocation :
    (∀ left right : WorkSpan,
      (WorkSpan.parallel left right).span ≤
        (WorkSpan.sequential left right).span) ∧
    (∃ first second : Nat,
      peakSequential first second < peakParallel first second) := by
  refine ⟨fun left right => ?_, ⟨1, 1, ?_⟩⟩
  · simp only [WorkSpan.parallel, WorkSpan.sequential]
    omega
  · simp only [peakSequential, peakParallel]
    omega

/-- A scalar that tracks the allocation coordinate faithfully is strictly
increasing in that coordinate at the smallest split.

**This is not a non-existence result**, and it was previously misnamed as one.
It uses only `respectsAllocation`; the span hypothesis plays no part, because
the two hypotheses constrain *different arguments* of a two-argument function
and therefore cannot clash. A genuine "no single scalar serves both" theorem
has to constrain one scalar under one composition — improving like span and
worsening like allocation simultaneously — and that statement is **not proved
here**.

The honest joint obstruction available today is
`peakAllocation_violates_lax_interchange`, which shows peak allocation is not
an instance of the concurrent-cost interface at all. -/
theorem allocationRespecting_scalar_strictMono_at_unitSplit
    (scalar : WorkSpan → Nat → Nat)
    (respectsAllocation : ∀ (value : WorkSpan) (first second : Nat),
      scalar value (peakSequential first second) <
        scalar value (peakParallel first second)) :
    ∀ value : WorkSpan, scalar value 1 < scalar value 2 := by
  intro value
  simpa [peakSequential, peakParallel] using respectsAllocation value 1 1

end Mettapedia.Algebra
