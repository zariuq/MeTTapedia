import Mettapedia.GSLT.Dynamics.UnfoldingTraversal
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs

/-!
# Semiring-weighted traversals: one invariance theorem for every answer algebra

The bag-invariance results say every complete traversal of an unfolding tree
produces the same answers with the same multiplicities.  This module draws the
quantitative consequence: give each answer a **weight** in a commutative
monoid, and every complete traversal has the same **aggregate**.  One theorem,
instantiated per algebra, covers

* counting (`ℕ`, every answer weighs `1`) — the license for counted queries
  that never materialize their answers;
* probability- and evidence-shaped weights (any commutative addition — in
  particular evidence *counts*, whose revision is addition);
* cost and resource accounting (additive monoids of receipts);
* optimization (min-plus and max-plus algebras);
* security and trust levels (join-semilattices as commutative idempotent
  monoids);
* provenance (the free instance — see below).

Two further results give the algebra its multiplicative half and its
universality:

* `weightSum_orderedProd` — over a commutative semiring, the aggregate of a
  conjunction (an ordered product of alternative lists) is the **product of
  the aggregates**: sum-of-products equals product-of-sums.  Weighting
  distributes over joint answers, which is what lets weighted conjunctive
  queries be planned factor-by-factor.
* `bagOf_eq_coe` — aggregating with singleton weights into multisets returns
  the answer bag itself: the bag is the **free** aggregate *of answers*, and
  every commutative aggregate of answers factors through it
  (`weightSum_eq_bag_fold`).  The bag is NOT intensional provenance: two
  derivations of one answer are counted while their causes are forgotten.
  Cause-labelled provenance and its universality live in
  `ProvenanceInterpretation`.

Everything is schedule-independent by construction: the aggregation theorems
consume only `Complete` (bag-respecting) traversals, so a weighted query means
the same thing under an eager engine, a backtracking engine, and a
demand-driven engine.
-/

namespace Mettapedia.GSLT.Dynamics.SemiringTraversal

open Mettapedia.GSLT.Dynamics.UnfoldingTraversal

variable {Ans : Type} {R : Type}

/-! ## Aggregation -/

/-- The aggregate of a list of answers under a weight function. -/
def weightSum [AddCommMonoid R] (w : Ans → R) (l : List Ans) : R :=
  (l.map w).sum

@[simp] theorem weightSum_nil [AddCommMonoid R] (w : Ans → R) :
    weightSum w ([] : List Ans) = 0 := rfl

@[simp] theorem weightSum_cons [AddCommMonoid R] (w : Ans → R) (a : Ans) (l : List Ans) :
    weightSum w (a :: l) = w a + weightSum w l := by
  simp [weightSum]

theorem weightSum_append [AddCommMonoid R] (w : Ans → R) (l l' : List Ans) :
    weightSum w (l ++ l') = weightSum w l + weightSum w l' := by
  simp [weightSum]

/-- Permuted answer lists aggregate identically: the aggregate is a bag
quantity. -/
theorem weightSum_perm [AddCommMonoid R] (w : Ans → R) {l l' : List Ans}
    (h : l.Perm l') : weightSum w l = weightSum w l' :=
  (h.map w).sum_eq

/-- **The invariance theorem.**  Every complete traversal of an unfolding tree
has the same aggregate, in every commutative-monoid weight algebra.  A weighted
query is schedule-independent by construction. -/
theorem weightSum_complete [AddCommMonoid R] (w : Ans → R)
    {trav trav' : Unfold Ans → List Ans}
    (h : Complete trav) (h' : Complete trav') (t : Unfold Ans) :
    weightSum w (trav t) = weightSum w (trav' t) :=
  weightSum_perm w (complete_perm h h' t)

/-! ## Counting: the first instance

Weight every answer `1` and the aggregate is the count.  Counted queries may
therefore be answered by any complete schedule — including one that never
materializes an answer — and must agree. -/

/-- Constant weight `1` aggregates to the length. -/
theorem weightSum_count (l : List Ans) :
    weightSum (fun _ => (1 : ℕ)) l = l.length := by
  induction l with
  | nil => rfl
  | cons a rest ih => simp [ih, Nat.add_comm]

/-- **Count invariance.**  Every complete traversal reports the same answer
count. -/
theorem count_complete {trav trav' : Unfold Ans → List Ans}
    (h : Complete trav) (h' : Complete trav') (t : Unfold Ans) :
    (trav t).length = (trav' t).length := by
  rw [← weightSum_count (trav t), ← weightSum_count (trav' t)]
  exact weightSum_complete _ h h' t

/-! ## Conjunction: the multiplicative half

Joint answers are tuples drawn from an ordered product of alternative lists;
their natural weight is the product of the component weights.  Over any
semiring — multiplication need not commute, because conjunction is ordered —
the aggregate of the product is the product of the aggregates: weighting
distributes over conjunction. -/

/-- Ordered cartesian product of alternative lists (order and duplicate
occurrences preserved). -/
def orderedProd : List (List Ans) → List (List Ans)
  | [] => [[]]
  | a :: rest => a.flatMap fun v => (orderedProd rest).map fun vs => v :: vs

/-- The weight of a joint answer: the product of its components' weights. -/
def tupleWeight [Semiring R] (w : Ans → R) (tup : List Ans) : R :=
  (tup.map w).prod

/-- Aggregation distributes over `flatMap`. -/
theorem weightSum_flatMap [AddCommMonoid R] (f : Ans → R) {β : Type}
    (g : β → List Ans) (l : List β) :
    weightSum f (l.flatMap g)
      = ((l.map fun b => weightSum f (g b))).sum := by
  induction l with
  | nil => rfl
  | cons b rest ih => simp [List.flatMap_cons, weightSum_append, ih]

/-- Scaling every weight on the left scales the aggregate. -/
theorem weightSum_mul_left [Semiring R] {β : Type}
    (f : β → R) (c : R) (l : List β) :
    ((l.map fun b => c * f b)).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons b rest ih => simp [ih, mul_add]

/-- Scaling every weight on the right scales the aggregate. -/
theorem sum_mul_right [Semiring R] {β : Type} (f : β → R) (c : R)
    (l : List β) :
    ((l.map fun b => f b * c)).sum = (l.map f).sum * c := by
  induction l with
  | nil => simp
  | cons b rest ih => simp [ih, add_mul]

/-- **Sum of products equals product of sums.**  The aggregate of the joint
answers is the product of the per-factor aggregates: weighted conjunctive
queries decompose factor-by-factor. -/
theorem weightSum_orderedProd [Semiring R] (w : Ans → R) :
    ∀ ls : List (List Ans),
      weightSum (tupleWeight w) (orderedProd ls)
        = (ls.map (weightSum w)).prod
  | [] => by simp [orderedProd, weightSum, tupleWeight]
  | a :: rest => by
    have hinner : ∀ v : Ans,
        weightSum (tupleWeight w) ((orderedProd rest).map fun vs => v :: vs)
          = w v * weightSum (tupleWeight w) (orderedProd rest) := by
      intro v
      have hmap : ((orderedProd rest).map fun vs => v :: vs).map (tupleWeight w)
          = (orderedProd rest).map fun vs => w v * tupleWeight w vs := by
        rw [List.map_map]
        apply List.map_congr_left
        intro vs _
        simp [tupleWeight]
      unfold weightSum
      rw [hmap, weightSum_mul_left]
    calc weightSum (tupleWeight w) (orderedProd (a :: rest))
        = ((a.map fun v => weightSum (tupleWeight w)
            ((orderedProd rest).map fun vs => v :: vs))).sum := by
          simp only [orderedProd]
          exact weightSum_flatMap _ _ a
      _ = ((a.map fun v =>
            w v * weightSum (tupleWeight w) (orderedProd rest))).sum := by
          congr 1
          exact List.map_congr_left fun v _ => hinner v
      _ = ((a.map w).sum) * weightSum (tupleWeight w) (orderedProd rest) := by
          exact sum_mul_right w _ a
      _ = (( (a :: rest).map (weightSum w))).prod := by
          rw [weightSum_orderedProd w rest]
          simp [weightSum]

/-! ## Universality: the bag is the free aggregate

Weighting each answer by its own singleton multiset aggregates to the answer
bag itself.  Every commutative-monoid aggregate is then a fold of that bag:
the bag is the universal (free) quantitative reading, and counting,
probability, cost, and provenance are its homomorphic images. -/

/-- Aggregating with singleton weights returns the answer bag. -/
theorem bagOf_eq_coe (l : List Ans) :
    weightSum (fun a => ({a} : Multiset Ans)) l = (l : Multiset Ans) := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    rw [weightSum_cons, ih]
    simp [Multiset.singleton_add]

/-- Every aggregate factors through the bag: `weightSum` is the multiset fold
of the weights.  Quantitative readings are shadows of the bag. -/
theorem weightSum_eq_bag_fold [AddCommMonoid R] (w : Ans → R) (l : List Ans) :
    weightSum w l = ((l : Multiset Ans).map w).sum := by
  simp [weightSum]

/-- **Bag invariance, restated at the free instance.**  Complete traversals
agree on the bag itself — the strongest aggregate, of which every other
instance in this module is a homomorphic image. -/
theorem bag_complete {trav trav' : Unfold Ans → List Ans}
    (h : Complete trav) (h' : Complete trav') (t : Unfold Ans) :
    ((trav t) : Multiset Ans) = ((trav' t) : Multiset Ans) := by
  rw [← bagOf_eq_coe (trav t), ← bagOf_eq_coe (trav' t)]
  exact weightSum_complete _ h h' t

end Mettapedia.GSLT.Dynamics.SemiringTraversal
