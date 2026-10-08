import Mettapedia.Machines.RationalTermGraph
import Mettapedia.Logic.LP.FiniteDependencyClosure
import Mathlib.Data.List.Shortlex
import Mathlib.Order.PiLex
import Mathlib.Order.WithBot
import Mathlib.Data.Prod.Lex

/-!
# Comparing ordered term graphs

The runtime comparison first builds reachable pairs of graph views. A pair
whose labels or arities differ is unequal; inequality propagates to parents.
The complement is a bisimulation, including cyclic pairs. This file connects
that finite marking calculation to the existing unfolding semantics. It uses
the shared finite dependency closure, rather than another reachability model.

The closure computation here is a reference calculation over a finite carrier.
It does not assert that its saturation cost is the native reverse-edge worklist
cost, or that these proofs verify compiled C memory operations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RationalTermGraph.Order

open Mettapedia.Logic.LP

universe u v w x

section Product

variable {A : Type u} {B : Type v} {Label : Type w}
variable [DecidableEq A] [DecidableEq B] [DecidableEq Label]
variable [Fintype A] [Fintype B]

/-- A label or arity difference is visible before descending into children. -/
def mismatch (g : Graph A Label) (h : Graph B Label) (pair : A × B) : Bool :=
  decide (g.label pair.1 ≠ h.label pair.2 ∨
    (g.children pair.1).length ≠ (h.children pair.2).length)

/-- Child pairs are ordered, and repeated positions remain repeated edges. -/
def pairChildren (g : Graph A Label) (h : Graph B Label) (pair : A × B) : List (A × B) :=
  if mismatch g h pair then [] else (g.children pair.1).zip (h.children pair.2)

def parents (g : Graph A Label) (h : Graph B Label) (child : A × B) : Finset (A × B) :=
  Finset.univ.filter fun parent => child ∈ pairChildren g h parent

def mismatches (g : Graph A Label) (h : Graph B Label) : Finset (A × B) :=
  Finset.univ.filter fun pair => mismatch g h pair

/-- Propagate the observable differences backwards through the product. -/
def unequalPairs (g : Graph A Label) (h : Graph B Label) : Finset (A × B) :=
  FiniteDependencyClosure.closure (parents g h) (mismatches g h)

theorem unequalPairs_sound {g : Graph A Label} {h : Graph B Label} {pair : A × B}
    (marked : pair ∈ unequalPairs g h) : ¬ Bisimilar g h pair.1 pair.2 := by
  classical
  have included : unequalPairs g h ⊆
      Finset.univ.filter (fun pair => ¬ Bisimilar g h pair.1 pair.2) := by
    apply FiniteDependencyClosure.least
    · intro pair seed
      simp only [mismatches, Finset.mem_filter, Finset.mem_univ, true_and] at seed
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro related
      obtain ⟨labels, children⟩ := related.layer
      simp [mismatch, labels, children.length_eq] at seed
    · intro child bad parent dependency
      simp only [parents, Finset.mem_filter, Finset.mem_univ, true_and] at dependency
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at bad ⊢
      intro related
      obtain ⟨labels, children⟩ := related.layer
      have noMismatch : mismatch g h parent = false := by
        simp [mismatch, labels, children.length_eq]
      simp only [pairChildren, noMismatch, Bool.false_eq_true, ↓reduceIte] at dependency
      exact bad (List.forall₂_zip children dependency)
  exact (Finset.mem_filter.mp (included marked)).2

theorem unmarked_isBisimulation (g : Graph A Label) (h : Graph B Label) :
    IsBisimulation g h (fun a b => (a, b) ∉ unequalPairs g h) := by
  intro a b unmarked
  have noMismatch : mismatch g h (a, b) = false := by
    by_contra different
    have seed : (a, b) ∈ mismatches g h := by
      simp [mismatches, Bool.eq_true_of_not_eq_false different]
    exact unmarked (FiniteDependencyClosure.roots_subset _ _ seed)
  have localAgreement : g.label a = h.label b ∧
      (g.children a).length = (h.children b).length := by
    simpa [mismatch] using noMismatch
  refine ⟨localAgreement.1, List.forall₂_iff_zip.mpr ⟨localAgreement.2, ?_⟩⟩
  intro childA childB edge marked
  have parent : (a, b) ∈ parents g h (childA, childB) := by
    simp [parents, pairChildren, noMismatch, edge]
  exact unmarked (FiniteDependencyClosure.closed _ _ marked parent)

/-- The computed marking decides the already-defined unfolding equality.
Cycles do not require unfolding, and an active pair alone is no certificate. -/
theorem unmarked_iff_bisimilar (g : Graph A Label) (h : Graph B Label) (a : A) (b : B) :
    (a, b) ∉ unequalPairs g h ↔ Bisimilar g h a b := by
  constructor
  · intro unmarked
    exact ⟨_, unmarked_isBisimulation g h, unmarked⟩
  · intro related marked
    exact unequalPairs_sound marked related

/-- Every marked pair exposes a difference at a finite observation depth. -/
theorem unequalPairs_iff_distinguishing_observation
    (g : Graph A Label) (h : Graph B Label) (a : A) (b : B) :
    (a, b) ∈ unequalPairs g h ↔ ∃ depth, observe g depth a ≠ observe h depth b := by
  classical
  rw [← not_iff_not, unmarked_iff_bisimilar, bisimilar_iff_observe_eq]
  simp only [not_exists, not_not]

end Product

namespace Traversal

variable {Node : Type u} [DecidableEq Node]

/-- Append each newly discovered pair at its first encounter. Children keep
their original order and repeated edges are inspected, but a repeated pair
does not acquire a second queue entry. The list membership test is a semantic
reference for the native pair table, not its implementation cost. -/
def enqueue : List Node → List Node → List Node
  | queue, [] => queue
  | queue, child :: children =>
      enqueue (if child ∈ queue then queue else queue ++ [child]) children

theorem enqueue_nodup (queue children : List Node) (unique : queue.Nodup) :
    (enqueue queue children).Nodup := by
  induction children generalizing queue with
  | nil => exact unique
  | cons child children ih =>
      simp only [enqueue]
      apply ih
      by_cases present : child ∈ queue
      · simpa [present] using unique
      · simp only [if_neg present, List.nodup_append, List.nodup_singleton, true_and,
          List.mem_singleton]
        refine ⟨unique, ?_⟩
        intro node member other same collision
        subst other
        exact present (collision ▸ member)

theorem enqueue_length (queue children : List Node) :
    queue.length ≤ (enqueue queue children).length := by
  induction children generalizing queue with
  | nil => exact Nat.le_refl _
  | cons child children ih =>
      simp only [enqueue]
      apply le_trans _ (ih _)
      split <;> simp

theorem enqueue_mem (queue children : List Node) (node : Node) :
    node ∈ enqueue queue children ↔ node ∈ queue ∨ node ∈ children := by
  induction children generalizing queue with
  | nil => simp [enqueue]
  | cons child children ih =>
      by_cases present : child ∈ queue
      · simp only [enqueue, if_pos present, ih, List.mem_cons]
        constructor
        · intro h; rcases h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · intro h; rcases h with h | h | h
          · exact Or.inl h
          · exact Or.inl (h ▸ present)
          · exact Or.inr h
      · simp only [enqueue, if_neg present, ih, List.mem_append, List.mem_cons]
        tauto

theorem enqueue_take (queue children : List Node) (count : Nat)
    (within : count ≤ queue.length) :
    (enqueue queue children).take count = queue.take count := by
  induction children generalizing queue with
  | nil => rfl
  | cons child children ih =>
      simp only [enqueue]
      split
      · exact ih queue within
      · rw [ih (queue ++ [child]) (by simp; omega)]
        exact List.take_append_of_le_length within

structure Frontier (Node : Type u) where
  queue : List Node
  offset : Nat

/-- One processed pair emits its child edges; the next pair is chosen from the
front of the existing queue. Fuel records processed rows, not tree depth. -/
def run (children : Node → List Node) : Nat → Frontier Node → Frontier Node
  | 0, state => state
  | fuel + 1, state =>
      if present : state.offset < state.queue.length then
        run children fuel
          ⟨enqueue state.queue (children state.queue[state.offset]), state.offset + 1⟩
      else state

theorem run_nodup (children : Node → List Node) (fuel : Nat) (state : Frontier Node)
    (unique : state.queue.Nodup) : (run children fuel state).queue.Nodup := by
  induction fuel generalizing state with
  | zero => exact unique
  | succ fuel ih =>
      simp only [run]
      split
      · exact ih _ (enqueue_nodup _ _ unique)
      · exact unique

theorem run_offset_le_length (children : Node → List Node) (fuel : Nat)
    (state : Frontier Node) (valid : state.offset ≤ state.queue.length) :
    (run children fuel state).offset ≤ (run children fuel state).queue.length := by
  induction fuel generalizing state with
  | zero => exact valid
  | succ fuel ih =>
      simp only [run]
      split
      · apply ih
        change state.offset + 1 ≤ (enqueue state.queue (children state.queue[state.offset])).length
        have extended := enqueue_length state.queue (children state.queue[state.offset])
        omega
      · exact valid

/-- Every already processed row has had all of its edges enqueued. -/
def ProcessedClosed (children : Node → List Node) (state : Frontier Node) : Prop :=
  ∀ node ∈ state.queue.take state.offset, ∀ child ∈ children node, child ∈ state.queue

theorem run_processedClosed (children : Node → List Node) (fuel : Nat)
    (state : Frontier Node) (closed : ProcessedClosed children state) :
    ProcessedClosed children (run children fuel state) := by
  induction fuel generalizing state with
  | zero => exact closed
  | succ fuel ih =>
      simp only [run]
      split
      · rename_i present
        apply ih
        intro node member child edge
        change node ∈ (enqueue state.queue (children state.queue[state.offset])).take
          (state.offset + 1) at member
        rw [enqueue_take _ _ _ (by omega), List.take_succ_eq_append_getElem present] at member
        simp only [List.mem_append, List.mem_singleton] at member
        apply (enqueue_mem _ _ child).mpr
        rcases member with processed | current
        · exact Or.inl (closed node processed child edge)
        · subst node
          exact Or.inr edge
      · exact closed

def Reachable (children : Node → List Node) (root node : Node) : Prop :=
  Relation.ReflTransGen (fun parent child => child ∈ children parent) root node

theorem run_reachable (children : Node → List Node) (root : Node) (fuel : Nat)
    (state : Frontier Node)
    (reachable : ∀ node ∈ state.queue, Reachable children root node) :
    ∀ node ∈ (run children fuel state).queue, Reachable children root node := by
  induction fuel generalizing state with
  | zero => exact reachable
  | succ fuel ih =>
      simp only [run]
      split
      · apply ih
        intro node member
        rcases (enqueue_mem _ _ node).mp member with previous | new
        · exact reachable node previous
        · exact (reachable state.queue[state.offset] (List.getElem_mem _)).tail new
      · exact reachable

variable [Fintype Node]

/-- A finite pair carrier supplies enough fuel even when every edge cycles.
This bound is on distinct processed pairs, not the sum of the input sizes. -/
theorem run_complete (children : Node → List Node) (fuel : Nat) (state : Frontier Node)
    (unique : state.queue.Nodup) (valid : state.offset ≤ state.queue.length)
    (enough : Fintype.card Node ≤ fuel + state.offset) :
    (run children fuel state).offset = (run children fuel state).queue.length := by
  induction fuel generalizing state with
  | zero =>
      simp only [run]
      have bounded := unique.length_le_card
      omega
  | succ fuel ih =>
      simp only [run]
      split
      · apply ih _ (enqueue_nodup _ _ unique)
        · change state.offset + 1 ≤ (enqueue state.queue (children state.queue[state.offset])).length
          have extended := enqueue_length state.queue (children state.queue[state.offset])
          omega
        · change Fintype.card Node ≤ fuel + (state.offset + 1)
          omega
      · omega

def fromRoot (children : Node → List Node) (root : Node) : Frontier Node :=
  run children (Fintype.card Node) ⟨[root], 0⟩

theorem fromRoot_complete (children : Node → List Node) (root : Node) :
    (fromRoot children root).offset = (fromRoot children root).queue.length :=
  run_complete _ _ _ (by simp) (by simp) (by simp)

theorem fromRoot_unique (children : Node → List Node) (root : Node) :
    (fromRoot children root).queue.Nodup := run_nodup _ _ _ (by simp)

theorem fromRoot_processed_bound (children : Node → List Node) (root : Node) :
    (fromRoot children root).offset ≤ Fintype.card Node := by
  rw [fromRoot_complete]
  exact (fromRoot_unique children root).length_le_card

/-- Finishing the worklist covers precisely the reachable graph, including
cycles. Duplicate edges affect the edge account, not queue membership. -/
theorem fromRoot_mem_iff_reachable (children : Node → List Node) (root node : Node) :
    node ∈ (fromRoot children root).queue ↔ Reachable children root node := by
  have covered := run_processedClosed children (Fintype.card Node) ⟨[root], 0⟩
    (by simp [ProcessedClosed])
  change ProcessedClosed children (fromRoot children root) at covered
  have complete := fromRoot_complete children root
  simp only [ProcessedClosed, complete, List.take_length] at covered
  have discovered := run_reachable children root (Fintype.card Node) ⟨[root], 0⟩
    (by intro n member; have same : n = root := by simpa using member
        subst n; exact Relation.ReflTransGen.refl)
  constructor
  · exact discovered node
  · intro reached
    have rootMember : root ∈ (fromRoot children root).queue := by
      have monotone : ∀ fuel (state : Frontier Node), ∀ x ∈ state.queue,
          x ∈ (run children fuel state).queue := by
        intro fuel
        induction fuel with
        | zero => simp [run]
        | succ fuel ih =>
          intro state x member
          simp only [run]
          split
          · exact ih _ x ((enqueue_mem _ _ x).mpr (Or.inl member))
          · exact member
      exact monotone _ _ root (by simp)
    induction reached with
    | refl => exact rootMember
    | tail _ edge ih => exact covered _ ih _ edge

def edgeCount (children : Node → List Node) : List Node → Nat
  | [] => 0
  | node :: nodes => (children node).length + edgeCount children nodes

omit [DecidableEq Node] [Fintype Node] in
theorem edgeCount_le (children : Node → List Node) (width : Nat) (nodes : List Node)
    (bounded : ∀ node ∈ nodes, (children node).length ≤ width) :
    edgeCount children nodes ≤ width * nodes.length := by
  induction nodes with
  | nil => simp [edgeCount]
  | cons node nodes ih =>
      have first := bounded node (by simp)
      have rest := ih (fun n member => bounded n (by simp [member]))
      simp only [edgeCount, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

theorem fromRoot_edge_bound (children : Node → List Node) (root : Node) (width : Nat)
    (bounded : ∀ node, (children node).length ≤ width) :
    edgeCount children (fromRoot children root).queue ≤ width * Fintype.card Node := by
  exact (edgeCount_le children width _ (fun n _ => bounded n)).trans
    (Nat.mul_le_mul_left width (fromRoot_unique children root).length_le_card)

/-- The product-pair visit counter has a product bound. Actual reachable pairs
can be far fewer; neither shared argument edges nor equal answer occurrences
are removed by this queue law. -/
theorem product_processed_bound {A : Type u} {B : Type v} [DecidableEq A]
    [DecidableEq B] [Fintype A] [Fintype B] (children : A × B → List (A × B))
    (root : A × B) :
    (fromRoot children root).offset ≤ Fintype.card A * Fintype.card B := by
  simpa only [Fintype.card_prod] using fromRoot_processed_bound children root

theorem repeated_edges_keep_one_queue_entry :
    enqueue ([0] : List Nat) [1, 1, 0, 2] = [0, 1, 2] := by decide

theorem self_cycle_terminates :
    (fromRoot (fun _ : Fin 1 => [0, 0]) 0).queue = [0] ∧
    (fromRoot (fun _ : Fin 1 => [0, 0]) 0).offset = 1 := by decide

end Traversal

section FiniteOrder

variable {Node : Type u} {Label : Type v}

/-- Recursive label/child comparison of finite observations. The depth bound
is a specification device: native acyclic comparison uses a worklist instead
of materializing these observations. -/
def compareDepth (g : Graph Node Label) (cmp : Label → Label → Ordering) :
    Nat → Node → Node → Ordering
  | 0, _, _ => .eq
  | depth + 1, a, b => (cmp (g.label a) (g.label b)).then
      (List.compareLex (compareDepth g cmp depth) (g.children a) (g.children b))

private theorem list_compare_eq_iff {α : Type u} (cmp : α → α → Ordering)
    (xs ys : List α) :
    List.compareLex cmp xs ys = .eq ↔ List.Forall₂ (fun a b => cmp a b = .eq) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [List.compareLex]
  | cons x xs ih =>
    cases ys with
    | nil => simp [List.compareLex]
    | cons y ys => simp [List.compareLex_cons_cons, Ordering.then_eq_eq, ih]

private theorem list_compare_congr {α : Type u} (first second : α → α → Ordering)
    (xs ys : List α) (agree : ∀ a ∈ xs, ∀ b ∈ ys, first a b = second a b) :
    List.compareLex first xs ys = List.compareLex second xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      simp only [List.compareLex_cons_cons, agree x (by simp) y (by simp)]
      rw [ih ys (fun a ha b hb => agree a (by simp [ha]) b (by simp [hb]))]

/-- The comparison's equality is the independent finite-unfolding equality. -/
theorem compareDepth_eq_iff (g : Graph Node Label) (cmp : Label → Label → Ordering)
    [Std.LawfulEqCmp cmp] (depth : Nat) (a b : Node) :
    compareDepth g cmp depth a b = .eq ↔ observe g depth a = observe g depth b := by
  induction depth generalizing a b with
  | zero => simp [compareDepth, observe]
  | succ depth ih =>
    simp only [compareDepth, observe, Ordering.then_eq_eq,
      Std.LawfulEqCmp.compare_eq_iff_eq, list_compare_eq_iff,
      Observation.node.injEq]
    rw [← List.forall₂_eq_eq_eq, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    apply and_congr_right
    intro _
    constructor
    · exact fun related => related.imp fun a b => (ih a b).mp
    · exact fun related => related.imp fun a b => (ih a b).mpr

/-- Every observation depth has an oriented, transitive comparison provided
the admitted leaf comparison does. Equality may identify different graph nodes. -/
theorem compareDepth_transCmp (g : Graph Node Label) (cmp : Label → Label → Ordering)
    [Std.TransCmp cmp] (depth : Nat) : Std.TransCmp (compareDepth g cmp depth) := by
  induction depth with
  | zero => exact { eq_swap := by intros; rfl, isLE_trans := by intros; rfl }
  | succ depth ih =>
    let _ := ih
    let head := fun a b => cmp (g.label a) (g.label b)
    let tail := fun a b => List.compareLex (compareDepth g cmp depth) (g.children a) (g.children b)
    have : Std.TransCmp head := {
      eq_swap := Std.OrientedCmp.eq_swap (cmp := cmp)
      isLE_trans := Std.TransCmp.isLE_trans (cmp := cmp) }
    have : Std.TransCmp tail := {
      eq_swap := Std.OrientedCmp.eq_swap (cmp := List.compareLex (compareDepth g cmp depth))
      isLE_trans := Std.TransCmp.isLE_trans (cmp := List.compareLex (compareDepth g cmp depth)) }
    exact inferInstanceAs (Std.TransCmp (compareLex head tail))

/-- At a common observation depth, swapping terms swaps the answer. -/
theorem compareDepth_swap (g : Graph Node Label) (cmp : Label → Label → Ordering)
    [Std.TransCmp cmp] (depth : Nat) (a b : Node) :
    compareDepth g cmp depth a b = (compareDepth g cmp depth b a).swap := by
  let _ := compareDepth_transCmp g cmp depth
  exact Std.OrientedCmp.eq_swap

theorem compareDepth_trans (g : Graph Node Label) (cmp : Label → Label → Ordering)
    [Std.TransCmp cmp] (depth : Nat) {a b c : Node}
    (ab : compareDepth g cmp depth a b = .lt)
    (bc : compareDepth g cmp depth b c = .lt) : compareDepth g cmp depth a c = .lt := by
  let _ := compareDepth_transCmp g cmp depth
  exact Std.TransCmp.lt_trans ab bc

/-- A decreasing node rank certifies that the admitted graph is acyclic. It
does not restrict how many incoming edges share a node. -/
def Decreasing (g : Graph Node Label) (rank : Node → Nat) : Prop :=
  ∀ node child, child ∈ g.children node → rank child < rank node

/-- Once both finite unfoldings fit, increasing the observation budget cannot
change an ordering result. This justifies comparing a DAG without expanding it
to an arbitrary common tree depth. -/
theorem compareDepth_stable (g : Graph Node Label) (cmp : Label → Label → Ordering)
    (rank : Node → Nat) (decreasing : Decreasing g rank) (depth extra : Nat)
    (a b : Node) (ha : rank a < depth) (hb : rank b < depth) :
    compareDepth g cmp (depth + extra) a b = compareDepth g cmp depth a b := by
  induction depth generalizing a b with
  | zero => omega
  | succ depth ih =>
    simp only [Nat.succ_add, compareDepth]
    congr 1
    apply list_compare_congr
    intro childA memberA childB memberB
    exact ih childA childB (by have := decreasing a childA memberA; omega)
      (by have := decreasing b childB memberB; omega)

/-- Finite graph comparison separates exactly the different unfolded terms,
not the different storage presentations. -/
theorem finite_compare_eq_iff_bisimilar (g : Graph Node Label)
    (cmp : Label → Label → Ordering) [Std.LawfulEqCmp cmp]
    (rank : Node → Nat) (decreasing : Decreasing g rank) (depth : Nat)
    (a b : Node) (ha : rank a < depth) (hb : rank b < depth) :
    compareDepth g cmp depth a b = .eq ↔ Bisimilar g g a b := by
  constructor
  · intro equal
    let relation := fun x y => ∃ n, rank x < n ∧ rank y < n ∧ compareDepth g cmp n x y = .eq
    refine ⟨relation, ?_, depth, ha, hb, equal⟩
    intro x y related
    obtain ⟨n, hx, hy, compared⟩ := related
    cases n with
    | zero => omega
    | succ n =>
      simp only [compareDepth, Ordering.then_eq_eq, Std.LawfulEqCmp.compare_eq_iff_eq,
        list_compare_eq_iff] at compared
      refine ⟨compared.1, ?_⟩
      apply List.forall₂_iff_zip.mpr
      refine ⟨compared.2.length_eq, ?_⟩
      intro childX childY member
      obtain ⟨memberX, memberY⟩ := List.of_mem_zip member
      exact ⟨n, by have := decreasing x childX memberX; omega,
        by have := decreasing y childY memberY; omega,
        List.forall₂_zip compared.2 member⟩
  · intro related
    exact (compareDepth_eq_iff _ _ _ _ _).mpr (bisimilar_iff_observe_eq.mp related depth)

end FiniteOrder

namespace Breadth

variable {A : Type u} {B : Type v} {C : Type w} {Label : Type x}

/-- A position exposes its admitted label and arity. Missing positions do not
pretend to be nodes. Arity is visible at the parent before its children. -/
def viewAt (g : Graph A Label) : A → List Nat → Option (Lex (Label × Nat))
  | node, [] => Option.some (toLex (g.label node, (g.children node).length))
  | node, index :: path => Option.bind (g.children node)[index]?
      (fun child => viewAt g child path)

theorem bisimilar_viewAt {g : Graph A Label} {h : Graph B Label} {a : A} {b : B}
    (related : Bisimilar g h a b) (path : List Nat) : viewAt g a path = viewAt h b path := by
  induction path generalizing a b with
  | nil =>
      obtain ⟨labels, children⟩ := related.layer
      simp [viewAt, labels, children.length_eq]
  | cons index path ih =>
      obtain ⟨_, children⟩ := related.layer
      by_cases present : index < (g.children a).length
      · have other : index < (h.children b).length := by simpa [children.length_eq] using present
        simpa only [viewAt, List.getElem?_eq_getElem present, List.getElem?_eq_getElem other,
          Option.bind_some, List.get_eq_getElem] using ih (children.get present other)
      · have other : ¬ index < (h.children b).length := by simpa [children.length_eq] using present
        simp [viewAt, List.getElem?_eq_none (Nat.le_of_not_gt present),
          List.getElem?_eq_none (Nat.le_of_not_gt other)]

/-- All finite positional readings recover the existing bisimilarity. This
does not require acyclicity or an expanded tree presentation. -/
theorem views_iff_bisimilar (g : Graph A Label) (h : Graph B Label) (a : A) (b : B) :
    (∀ path, viewAt g a path = viewAt h b path) ↔ Bisimilar g h a b := by
  constructor
  · intro readings
    refine ⟨fun left right => ∀ path, viewAt g left path = viewAt h right path, ?_, readings⟩
    intro left right equal
    have root := equal []
    simp only [viewAt, Option.some.injEq] at root
    have labels : g.label left = h.label right := congrArg Prod.fst root
    have lengths : (g.children left).length = (h.children right).length := congrArg Prod.snd root
    refine ⟨labels, List.forall₂_iff_get.mpr ⟨lengths, ?_⟩⟩
    intro index first second path
    simpa only [viewAt, List.getElem?_eq_getElem first, List.getElem?_eq_getElem second,
      Option.bind_some, List.get_eq_getElem] using equal (index :: path)
  · exact fun related path => bisimilar_viewAt related path

/-- Breadth-first positions are ordered first by depth, then by argument
position. The well-founded order includes unused positions; equal missing
readings cannot become the first difference. -/
def PositionLT : List Nat → List Nat → Prop := List.Shortlex (· < ·)

private theorem position_trans {first second third : List Nat}
    (one : PositionLT first second) (two : PositionLT second third) : PositionLT first third := by
  rcases List.shortlex_def.mp one with one | ⟨oneLength, oneLex⟩
  · rcases List.shortlex_def.mp two with two | ⟨twoLength, _⟩
    · exact List.Shortlex.of_length_lt (one.trans two)
    · exact List.Shortlex.of_length_lt (by omega)
  · rcases List.shortlex_def.mp two with two | ⟨twoLength, twoLex⟩
    · exact List.Shortlex.of_length_lt (by omega)
    · exact List.Shortlex.of_lex (oneLength.trans twoLength)
        (List.lex_trans (fun one two => Nat.lt_trans one two) oneLex twoLex)

section OrderedLabels

variable [LinearOrder Label]

/-- Missing positions use the bottom element of the header order. -/
def orderedView (g : Graph A Label) (a : A) : List Nat → WithBot (Lex (Label × Nat)) :=
  fun path => viewAt g a path

/-- Lexicographic comparison of readings is transitive whenever the position
order is transitive and trichotomous. Well-foundedness is needed separately
for totality, not for this order law. -/
theorem reading_less_trans (positionOrder : List Nat → List Nat → Prop)
    (transitive : ∀ {first middle last}, positionOrder first middle →
      positionOrder middle last → positionOrder first last)
    (trichotomous : ∀ first second, positionOrder first second ∨ first = second ∨
      positionOrder second first)
    {first middle last : List Nat → WithBot (Lex (Label × Nat))}
    (one : Pi.Lex positionOrder (· < ·) first middle)
    (two : Pi.Lex positionOrder (· < ·) middle last) :
    Pi.Lex positionOrder (· < ·) first last := by
  obtain ⟨p, beforeP, smallerP⟩ := one
  obtain ⟨q, beforeQ, smallerQ⟩ := two
  rcases trichotomous p q with earlier | same | later
  · refine ⟨p, ?_, ?_⟩
    · intro path before
      exact (beforeP path before).trans (beforeQ path (transitive before earlier))
    · simpa only [beforeQ p earlier] using smallerP
  · subst q
    exact ⟨p, fun path before => (beforeP path before).trans (beforeQ path before),
      smallerP.trans smallerQ⟩
  · refine ⟨q, ?_, ?_⟩
    · intro path before
      exact (beforeP path (transitive before later)).trans (beforeQ path before)
    · simpa only [beforeP q later] using smallerQ

/-- The first different positional reading defines the breadth policy.
The admitted header order is label-then-arity; a native compound label may
already contain its class, arity and name. This is an unfolding order,
not an allocation-address or graph-presentation order. -/
def Less (g : Graph A Label) (h : Graph B Label) (a : A) (b : B) : Prop :=
  Pi.Lex PositionLT (· < ·) (orderedView g a) (orderedView h b)

theorem less_irrefl (g : Graph A Label) (a : A) : ¬ Less g g a a := by
  rintro ⟨path, _, smaller⟩
  exact lt_irrefl _ smaller

theorem less_trans {g : Graph A Label} {h : Graph B Label} {k : Graph C Label}
    {a : A} {b : B} {c : C} (one : Less g h a b) (two : Less h k b c) : Less g k a c := by
  exact reading_less_trans PositionLT position_trans
    (trichotomous_of (List.Shortlex (· < ·))) one two

theorem less_asymm {g : Graph A Label} {h : Graph B Label} {a : A} {b : B}
    (one : Less g h a b) : ¬ Less h g b a := fun two => less_irrefl g a (less_trans one two)

/-- Finite and cyclic terms have a total ordering modulo the independent
bisimilarity observation. No recursive child-lexicographic law is asserted. -/
theorem trichotomy (g : Graph A Label) (h : Graph B Label) (a : A) (b : B) :
    Less g h a b ∨ Bisimilar g h a b ∨ Less h g b a := by
  let _ : Std.Trichotomous (Pi.Lex PositionLT (fun x y : WithBot (Lex (Label × Nat)) => x < y)) :=
    Pi.trichotomous_lex PositionLT (· < ·) (List.Shortlex.wf Nat.lt_wfRel.wf)
  rcases trichotomous_of (Pi.Lex PositionLT (· < ·)) (orderedView g a) (orderedView h b) with
    smaller | equal | larger
  · exact Or.inl smaller
  · exact Or.inr (Or.inl ((views_iff_bisimilar g h a b).mp (fun path => congrFun equal path)))
  · exact Or.inr (Or.inr larger)

theorem neither_less_iff_bisimilar (g : Graph A Label) (h : Graph B Label) (a : A) (b : B) :
    (¬ Less g h a b ∧ ¬ Less h g b a) ↔ Bisimilar g h a b := by
  constructor
  · rintro ⟨notSmaller, notLarger⟩
    rcases trichotomy g h a b with smaller | equal | larger
    · exact (notSmaller smaller).elim
    · exact equal
    · exact (notLarger larger).elim
  · intro related
    have equal : orderedView g a = orderedView h b := by
      funext path
      exact bisimilar_viewAt related path
    constructor <;> intro smaller
    · exact less_irrefl h b (by simpa only [Less, equal] using smaller)
    · exact less_irrefl h b (by simpa only [Less, equal] using smaller)

theorem transport_less_iff {g : Graph A Label} {h : Graph B Label} {k : Graph C Label}
    {a : A} {b : B} {c : C} (related : Bisimilar g h a b) :
    Less g k a c ↔ Less h k b c := by
  have equal : orderedView g a = orderedView h b := by
    funext path
    exact bisimilar_viewAt related path
  simp only [Less, equal]

end OrderedLabels

end Breadth

namespace DepthFirst

variable {A : Type u} {B : Type v} {C : Type w} {Label : Type x}
variable [LinearOrder Label]

/-- Recursive lexicographic comparison has a finite distinguishing-position
witness. Some unequal cyclic terms have no such first position, so this
relation is deliberately partial. -/
def Less (g : Graph A Label) (h : Graph B Label) (a : A) (b : B) : Prop :=
  Pi.Lex (List.Lex (· < ·)) (· < ·) (Breadth.orderedView g a) (Breadth.orderedView h b)

theorem less_irrefl (g : Graph A Label) (a : A) : ¬ Less g g a a := by
  rintro ⟨path, _, smaller⟩
  exact lt_irrefl _ smaller

theorem less_trans {g : Graph A Label} {h : Graph B Label} {k : Graph C Label}
    {a : A} {b : B} {c : C} (one : Less g h a b) (two : Less h k b c) : Less g k a c := by
  apply Breadth.reading_less_trans (List.Lex (· < ·)) _
    (trichotomous_of (List.Lex (· < ·))) one two
  intro first second third one two
  exact List.lex_trans (fun one two => Nat.lt_trans one two) one two

theorem less_asymm {g : Graph A Label} {h : Graph B Label} {a : A} {b : B}
    (one : Less g h a b) : ¬ Less h g b a := fun two => less_irrefl g a (less_trans one two)

theorem transport_less_iff {g : Graph A Label} {h : Graph B Label} {k : Graph C Label}
    {a : A} {b : B} {c : C} (related : Bisimilar g h a b) :
    Less g k a c ↔ Less h k b c := by
  have equal : Breadth.orderedView g a = Breadth.orderedView h b := by
    funext path
    exact Breadth.bisimilar_viewAt related path
  simp only [Less, equal]

theorem bisimilar_not_less {g : Graph A Label} {h : Graph B Label} {a : A} {b : B}
    (related : Bisimilar g h a b) : ¬ Less g h a b := by
  rw [transport_less_iff related]
  exact less_irrefl h b

end DepthFirst

namespace Controls

/-- The first arguments point to each other; the second arguments differ.
This finite graph separates total breadth ordering from recursive child
ordering. -/
def crossed : Graph (Fin 4) Nat where
  label node := if node = 2 then 0 else if node = 3 then 1 else 2
  children node := if node = 0 then [1, 2] else if node = 1 then [0, 3] else []

theorem crossed_not_bisimilar : ¬ Bisimilar crossed crossed 0 1 := by
  intro related
  have different := Breadth.bisimilar_viewAt related [1]
  simp [Breadth.viewAt, crossed] at different

/-- For a recursive lexicographic order, unequal first children decide the
comparison when the parent headers agree. -/
def FirstChildLaw {Node : Type u} {Label : Type v}
    (g : Graph Node Label) (less : Node → Node → Prop) : Prop :=
  ∀ a b first tail second rest,
    g.children a = first :: tail → g.children b = second :: rest →
    g.label a = g.label b → (g.children a).length = (g.children b).length →
    ¬ Bisimilar g g first second → (less a b ↔ less first second)

/-- A total asymmetric order cannot also obey recursive first-child
dominance on every rational term. Choosing a total policy therefore changes
that law; it does not repair recursive lexicographic ordering. -/
theorem no_total_recursive_child_order (less : Fin 4 → Fin 4 → Prop)
    (asymmetric : ∀ a b, less a b → ¬ less b a)
    (total : ∀ a b, less a b ∨ Bisimilar crossed crossed a b ∨ less b a)
    (recursive : FirstChildLaw crossed less) : False := by
  have reverseUnequal : ¬ Bisimilar crossed crossed 1 0 :=
    fun related => crossed_not_bisimilar related.symm
  have flipped : less 0 1 ↔ less 1 0 :=
    recursive 0 1 1 [2] 0 [3] (by decide) (by decide) (by decide) (by decide)
      reverseUnequal
  rcases total 0 1 with smaller | related | larger
  · exact asymmetric 0 1 smaller (flipped.mp smaller)
  · exact crossed_not_bisimilar related
  · exact asymmetric 1 0 larger (flipped.mpr larger)

end Controls

end Mettapedia.Machines.RationalTermGraph.Order
