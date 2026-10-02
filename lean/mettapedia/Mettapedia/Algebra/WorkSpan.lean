import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Tactic

/-!
# Work/span cost algebra

Concurrent cost has two independent coordinates and two compositions:

* sequential composition adds both total work and critical-path span;
* independent parallel composition adds work and takes the maximum span.

These operations do not form an ordinary semiring.  Their interaction is a
lax interchange inequality: scheduling two sequential pairs in parallel is
no slower than first synchronizing the two left stages and then the two right
stages.  The distinction is operationally important: parallel execution can
reduce span without erasing work.

`ConcurrentCostAlgebra` packages only the laws shared by such models.  The
concrete `WorkSpan` instance is intentionally small enough to serve as a
readout of richer resource vectors and of occurrence-indexed execution traces.
-/

namespace Mettapedia.Algebra

/-- Two monoidal compositions over one ordered carrier, related by lax
interchange.  The operations are fields rather than global type-class
notation so a carrier may support more than one accounting policy. -/
structure ConcurrentCostAlgebra (A : Type*) [Preorder A] where
  zero : A
  sequential : A → A → A
  parallel : A → A → A
  sequential_zero_left : ∀ value, sequential zero value = value
  sequential_zero_right : ∀ value, sequential value zero = value
  sequential_assoc : ∀ first second third,
    sequential (sequential first second) third =
      sequential first (sequential second third)
  parallel_zero_left : ∀ value, parallel zero value = value
  parallel_zero_right : ∀ value, parallel value zero = value
  parallel_assoc : ∀ first second third,
    parallel (parallel first second) third =
      parallel first (parallel second third)
  parallel_comm : ∀ left right, parallel left right = parallel right left
  sequential_mono : ∀ {first first' second second'},
    first ≤ first' → second ≤ second' →
      sequential first second ≤ sequential first' second'
  parallel_mono : ∀ {first first' second second'},
    first ≤ first' → second ≤ second' →
      parallel first second ≤ parallel first' second'
  lax_interchange : ∀ first second third fourth,
    parallel (sequential first second) (sequential third fourth) ≤
      sequential (parallel first third) (parallel second fourth)

/-- Total work and critical-path span. -/
@[ext] structure WorkSpan where
  work : Nat
  span : Nat
  deriving DecidableEq, Repr

namespace WorkSpan

instance : LE WorkSpan where
  le left right := left.work ≤ right.work ∧ left.span ≤ right.span

instance : PartialOrder WorkSpan where
  le_refl value := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ first second :=
    ⟨first.1.trans second.1, first.2.trans second.2⟩
  le_antisymm first second firstSecond secondFirst := by
    ext
    · exact Nat.le_antisymm firstSecond.1 secondFirst.1
    · exact Nat.le_antisymm firstSecond.2 secondFirst.2

/-- No work and no span. -/
def zero : WorkSpan := ⟨0, 0⟩

instance : Zero WorkSpan := ⟨zero⟩

/-- Sequential phases: both coordinates accumulate. -/
def sequential (first second : WorkSpan) : WorkSpan :=
  ⟨first.work + second.work, first.span + second.span⟩

/-- Independent branches: work accumulates while span is the slower branch. -/
def parallel (left right : WorkSpan) : WorkSpan :=
  ⟨left.work + right.work, max left.span right.span⟩

@[simp] theorem zero_work : (0 : WorkSpan).work = 0 := rfl
@[simp] theorem zero_span : (0 : WorkSpan).span = 0 := rfl

@[simp] theorem sequential_zero_left (value : WorkSpan) :
    sequential 0 value = value := by
  ext <;> simp [sequential]

@[simp] theorem sequential_zero_right (value : WorkSpan) :
    sequential value 0 = value := by
  ext <;> simp [sequential]

theorem sequential_assoc (first second third : WorkSpan) :
    sequential (sequential first second) third =
      sequential first (sequential second third) := by
  ext <;> simp [sequential, Nat.add_assoc]

@[simp] theorem parallel_zero_left (value : WorkSpan) :
    parallel 0 value = value := by
  ext <;> simp [parallel]

@[simp] theorem parallel_zero_right (value : WorkSpan) :
    parallel value 0 = value := by
  ext <;> simp [parallel]

theorem parallel_assoc (first second third : WorkSpan) :
    parallel (parallel first second) third =
      parallel first (parallel second third) := by
  ext <;> simp [parallel, Nat.add_assoc, Nat.max_assoc]

theorem parallel_comm (left right : WorkSpan) :
    parallel left right = parallel right left := by
  ext <;> simp [parallel, Nat.add_comm, Nat.max_comm]

theorem sequential_mono {first first' second second' : WorkSpan}
    (firstLe : first ≤ first') (secondLe : second ≤ second') :
    sequential first second ≤ sequential first' second' :=
  ⟨Nat.add_le_add firstLe.1 secondLe.1,
    Nat.add_le_add firstLe.2 secondLe.2⟩

theorem parallel_mono {first first' second second' : WorkSpan}
    (firstLe : first ≤ first') (secondLe : second ≤ second') :
    parallel first second ≤ parallel first' second' :=
  ⟨Nat.add_le_add firstLe.1 secondLe.1,
    max_le_max firstLe.2 secondLe.2⟩

/-- Lax interchange for work/span accounting.  Work is merely reassociated;
span uses `max (a+b) (c+d) ≤ max a c + max b d`. -/
theorem lax_interchange (first second third fourth : WorkSpan) :
    parallel (sequential first second) (sequential third fourth) ≤
      sequential (parallel first third) (parallel second fourth) := by
  constructor
  · simp only [parallel, sequential]
    omega
  · exact max_add_add_le_max_add_max

/-- The reusable concurrent-cost algebra carried by work/span pairs. -/
def algebra : ConcurrentCostAlgebra WorkSpan where
  zero := 0
  sequential := sequential
  parallel := parallel
  sequential_zero_left := sequential_zero_left
  sequential_zero_right := sequential_zero_right
  sequential_assoc := sequential_assoc
  parallel_zero_left := parallel_zero_left
  parallel_zero_right := parallel_zero_right
  parallel_assoc := parallel_assoc
  parallel_comm := parallel_comm
  sequential_mono := sequential_mono
  parallel_mono := parallel_mono
  lax_interchange := lax_interchange

/-- Parallel execution never has more span than serial execution of the same
two branches; total work is identical. -/
theorem parallel_le_sequential (left right : WorkSpan) :
    parallel left right ≤ sequential left right := by
  constructor
  · rfl
  · exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)

/-- Fold the independent composition over a finite family of branch receipts.
Each branch may itself retain a parallel critical path. Independence and the
accuracy of the input receipts are obligations of the execution model. -/
def parallelAll (branches : List WorkSpan) : WorkSpan :=
  branches.foldr parallel 0

/-- Sequential execution of a finite family of receipts. In a fixed worker
assignment, successive slices on the same worker use this composition. -/
def sequentialAll (stages : List WorkSpan) : WorkSpan :=
  stages.foldr sequential 0

@[simp] theorem sequentialAll_nil : sequentialAll [] = 0 := rfl

@[simp] theorem sequentialAll_cons (head : WorkSpan) (tail : List WorkSpan) :
    sequentialAll (head :: tail) = sequential head (sequentialAll tail) := rfl

theorem sequentialAll_append (first second : List WorkSpan) :
    sequentialAll (first ++ second) =
      sequential (sequentialAll first) (sequentialAll second) := by
  induction first with
  | nil => simp
  | cons head tail ih =>
      simp only [List.cons_append, sequentialAll_cons, ih, sequential_assoc]

@[simp] theorem sequentialAll_work (stages : List WorkSpan) :
    (sequentialAll stages).work = (stages.map WorkSpan.work).sum := by
  induction stages with
  | nil => rfl
  | cons head tail ih =>
      change head.work + (sequentialAll tail).work = head.work + (tail.map WorkSpan.work).sum
      rw [ih]

@[simp] theorem sequentialAll_span (stages : List WorkSpan) :
    (sequentialAll stages).span = (stages.map WorkSpan.span).sum := by
  induction stages with
  | nil => rfl
  | cons head tail ih =>
      change head.span + (sequentialAll tail).span = head.span + (tail.map WorkSpan.span).sum
      rw [ih]

@[simp] theorem parallelAll_nil : parallelAll [] = 0 := rfl

@[simp] theorem parallelAll_cons (head : WorkSpan) (tail : List WorkSpan) :
    parallelAll (head :: tail) = parallel head (parallelAll tail) := rfl

theorem parallelAll_append (first second : List WorkSpan) :
    parallelAll (first ++ second) = parallel (parallelAll first) (parallelAll second) := by
  induction first with
  | nil => simp
  | cons head tail ih =>
      simp only [List.cons_append, parallelAll_cons, ih, parallel_assoc]

@[simp] theorem parallelAll_work (branches : List WorkSpan) :
    (parallelAll branches).work = (branches.map WorkSpan.work).sum := by
  induction branches with
  | nil => rfl
  | cons head tail ih =>
      change head.work + (parallelAll tail).work = head.work + (tail.map WorkSpan.work).sum
      rw [ih]

@[simp] theorem parallelAll_span (branches : List WorkSpan) :
    (parallelAll branches).span = (branches.map WorkSpan.span).foldr max 0 := by
  induction branches with
  | nil => rfl
  | cons head tail ih =>
      change max head.span (parallelAll tail).span =
        max head.span ((tail.map WorkSpan.span).foldr max 0)
      rw [ih]

/-- Publication order cannot change this declared cost readout. Semantic
coefficients and result order may have different, noncommutative laws. -/
theorem parallelAll_perm {first second : List WorkSpan} (order : first.Perm second) :
    parallelAll first = parallelAll second := by
  induction order with
  | nil => rfl
  | cons head order ih => simp only [parallelAll_cons, ih]
  | swap first second tail =>
      simp only [parallelAll_cons]
      rw [← parallel_assoc, parallel_comm second first, parallel_assoc]
  | trans first second ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- A fork retains its shared prefix once, followed by the independent
children and the join suffix. This is a causal cost construction, not an
authorization to execute branches independently. -/
def forkJoin (before : WorkSpan) (children : List WorkSpan) (after : WorkSpan) : WorkSpan :=
  sequential before (sequential (parallelAll children) after)

@[simp] theorem forkJoin_work (before after : WorkSpan) (children : List WorkSpan) :
    (forkJoin before children after).work =
      before.work + (children.map WorkSpan.work).sum + after.work := by
  simp [forkJoin, sequential, Nat.add_assoc]

@[simp] theorem forkJoin_span (before after : WorkSpan) (children : List WorkSpan) :
    (forkJoin before children after).span =
      before.span + (children.map WorkSpan.span).foldr max 0 + after.span := by
  simp [forkJoin, sequential, Nat.add_assoc]

/-- Positive control: an already parallel child retains its smaller span,
and a common prefix is charged once. -/
theorem nested_forkJoin_control :
    forkJoin ⟨3, 3⟩ [parallel ⟨5, 5⟩ ⟨5, 5⟩, ⟨7, 7⟩] ⟨2, 2⟩ = ⟨22, 12⟩ := by
  decide

/-- Negative control: copying the shared prefix into each child changes
both the reported work and the critical path. -/
theorem repeated_prefix_changes_cost :
    forkJoin ⟨3, 3⟩ [⟨5, 5⟩, ⟨7, 7⟩] ⟨2, 2⟩ ≠
      forkJoin ⟨3, 3⟩ [sequential ⟨3, 3⟩ ⟨5, 5⟩,
        sequential ⟨3, 3⟩ ⟨7, 7⟩] ⟨2, 2⟩ := by
  decide

/-- Positive example: two unit jobs have work two and parallel span one. -/
example : parallel ⟨1, 1⟩ ⟨1, 1⟩ = ⟨2, 1⟩ := rfl

/-- Negative example: parallel and sequential composition are genuinely
different, so collapsing the two operations would lose span information. -/
example : parallel ⟨1, 1⟩ ⟨1, 1⟩ ≠ sequential ⟨1, 1⟩ ⟨1, 1⟩ := by
  intro equal
  have spans := congrArg WorkSpan.span equal
  norm_num [parallel, sequential] at spans

end WorkSpan

end Mettapedia.Algebra
