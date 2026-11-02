import Mathlib.Tactic

/-!
# Collection points in every engine loop

A loop the open equation machine runs inside one statement sends its host
goals to the outer machine, which reaches its collection points between
them; but the machine exports each goal's ground structure straight into
the outer machine's tenured arena, past the nursery, and a collection was
due only when the nursery filled.  A parse loop's fresh term per iteration
stayed for the whole statement: 160 B an iteration, 102 MB at 640,000.  A
collection is now due once the tenured arena has grown by its window as
well.

Where a collection may run at all is the other half: the engines open on a
thread form a stack of activations; each lists what it holds, and is clean
while it holds nothing unlisted (no id or pointer kept only in C locals
across a nested call).  A collection is legal where every open activation
is clean.

The model: activations with listed and hidden holdings, a collector keeping
what the roots reach, and a loop that allocates every step and collects
every K steps.  This file proves:
* `collect_keeps_held`: where every activation is clean, a collection frees
  nothing an activation holds;
* `unclean_frees_held`: one activation holding an unlisted object makes a
  collection free it (the case the legality check excludes);
* `run_card_le`: with a collection once `K` steps have passed since the
  last, each keeping at most `R` objects, and at most `a` objects made a
  step, the heap never exceeds `R + (K - 1) * a`, however long the loop runs;
* `runMade_card_lt`: collecting once `W` was made since the last collection,
  the heap stays below `R + W`, and within `R + W + a` before a collection;
* `uncollected_card_ge`: without a collection, a loop whose steps make
  disjoint sets of `a` objects holds at least `t * a` after `t` steps.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NestedSafePoints

variable {α : Type} [DecidableEq α]

/-- An engine open on a thread: what it lists to the collector, and what it
holds without listing it. -/
structure Activation (α : Type) where
  listed : Finset α
  hidden : Finset α

/-- Everything an activation holds. -/
def Activation.holds (act : Activation α) : Finset α := act.listed ∪ act.hidden

/-- An activation is clean while it holds nothing unlisted. -/
def Activation.Clean (act : Activation α) : Prop := act.hidden = ∅

/-- The roots a collection sees: what the open activations list. -/
def roots : List (Activation α) → Finset α
  | [] => ∅
  | act :: rest => act.listed ∪ roots rest

theorem listed_subset_roots {stack : List (Activation α)} {act : Activation α}
    (h : act ∈ stack) : act.listed ⊆ roots stack := by
  induction stack with
  | nil => simp at h
  | cons head rest ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Finset.subset_union_left
    · exact (ih h).trans Finset.subset_union_right

/-- A collector keeps what its closure of the roots holds. -/
structure Collector (α : Type) where
  reach : Finset α → Finset α
  extensive : ∀ s, s ⊆ reach s

/-- A collection keeps of the heap what the roots reach. -/
def collect (c : Collector α) (stack : List (Activation α)) (heap : Finset α) :
    Finset α :=
  heap.filter (· ∈ c.reach (roots stack))

/-- Where every open activation is clean, a collection frees nothing any of
them holds. -/
theorem collect_keeps_held (c : Collector α) (stack : List (Activation α))
    (heap : Finset α) (clean : ∀ act ∈ stack, act.Clean)
    {act : Activation α} (h : act ∈ stack) :
    act.holds ∩ heap ⊆ collect c stack heap := by
  intro x hx
  rcases Finset.mem_inter.mp hx with ⟨held, inHeap⟩
  have listed : x ∈ act.listed := by
    have hidden : act.hidden = ∅ := clean act h
    simpa [Activation.holds, hidden] using held
  exact Finset.mem_filter.mpr
    ⟨inHeap, c.extensive _ (listed_subset_roots h listed)⟩

/-- The collector of an identity closure: it keeps the roots and nothing
else. -/
def rootsOnly : Collector α where
  reach := id
  extensive := fun _ => le_rfl

/-- One activation holding an object it does not list: a collection frees
it. -/
theorem unclean_frees_held :
    ∃ (stack : List (Activation ℕ)) (heap : Finset ℕ) (act : Activation ℕ),
      act ∈ stack ∧ ¬ act.Clean ∧ ¬ (act.holds ∩ heap ⊆ collect rootsOnly stack heap) := by
  refine ⟨[⟨∅, {0}⟩], {0}, ⟨∅, {0}⟩, by simp, ?_, ?_⟩
  · simp [Activation.Clean]
  · decide

/-- A loop that makes `alloc t` at step `t` and collects once `K` steps have
passed since the last collection, `keep` choosing what a collection keeps.
The state is the heap and the steps since the last collection. -/
def run (K : ℕ) (alloc : ℕ → Finset α) (keep : ℕ → Finset α → Finset α)
    (start : Finset α) : ℕ → Finset α × ℕ
  | 0 => (start, 0)
  | t + 1 =>
    if (run K alloc keep start t).2 + 1 = K then
      (keep (t + 1) ((run K alloc keep start t).1 ∪ alloc t), 0)
    else
      ((run K alloc keep start t).1 ∪ alloc t, (run K alloc keep start t).2 + 1)

/-- Fewer than `K` steps pass between collections, and the heap holds at most
`R` plus `a` for each of them. -/
theorem run_inv (K R a : ℕ) (hK : 0 < K) (alloc : ℕ → Finset α)
    (keep : ℕ → Finset α → Finset α) (start : Finset α)
    (hstart : start.card ≤ R) (hkeep : ∀ t s, (keep t s).card ≤ R)
    (halloc : ∀ t, (alloc t).card ≤ a) (t : ℕ) :
    (run K alloc keep start t).2 < K ∧
      (run K alloc keep start t).1.card ≤ R + (run K alloc keep start t).2 * a := by
  induction t with
  | zero => exact ⟨by simpa [run] using hK, by simpa [run] using hstart⟩
  | succ t ih =>
    obtain ⟨hlt, hcard⟩ := ih
    by_cases hz : (run K alloc keep start t).2 + 1 = K
    · simp only [run, hz, if_true, zero_mul, add_zero]
      exact ⟨hK, hkeep _ _⟩
    · simp only [run, hz, if_false]
      refine ⟨by omega, ?_⟩
      calc ((run K alloc keep start t).1 ∪ alloc t).card
          ≤ (run K alloc keep start t).1.card + (alloc t).card := Finset.card_union_le _ _
        _ ≤ R + (run K alloc keep start t).2 * a + a := by
          have := halloc t
          omega
        _ = R + ((run K alloc keep start t).2 + 1) * a := by ring

/-- However long the loop runs, the heap stays within `R + (K - 1) * a`. -/
theorem run_card_le (K R a : ℕ) (hK : 0 < K) (alloc : ℕ → Finset α)
    (keep : ℕ → Finset α → Finset α) (start : Finset α)
    (hstart : start.card ≤ R) (hkeep : ∀ t s, (keep t s).card ≤ R)
    (halloc : ∀ t, (alloc t).card ≤ a) (t : ℕ) :
    (run K alloc keep start t).1.card ≤ R + (K - 1) * a := by
  obtain ⟨hlt, hcard⟩ := run_inv K R a hK alloc keep start hstart hkeep halloc t
  have hsince : (run K alloc keep start t).2 ≤ K - 1 := by omega
  exact hcard.trans (by nlinarith [hsince])

/-- A loop that collects once what it made since the last collection
reaches `W`, as the outer machine collects once its tenured arena has grown
by its window: the state is the heap and what was made since. -/
def runMade (W : ℕ) (alloc : ℕ → Finset α) (keep : ℕ → Finset α → Finset α)
    (start : Finset α) : ℕ → Finset α × ℕ
  | 0 => (start, 0)
  | t + 1 =>
    if (runMade W alloc keep start t).2 + (alloc t).card ≥ W then
      (keep (t + 1) ((runMade W alloc keep start t).1 ∪ alloc t), 0)
    else
      ((runMade W alloc keep start t).1 ∪ alloc t,
        (runMade W alloc keep start t).2 + (alloc t).card)

/-- Less than `W` was made since the last collection, and the heap holds at
most `R` plus that. -/
theorem runMade_inv (W R : ℕ) (alloc : ℕ → Finset α)
    (keep : ℕ → Finset α → Finset α) (start : Finset α) (hW : 0 < W)
    (hstart : start.card ≤ R) (hkeep : ∀ t s, (keep t s).card ≤ R) (t : ℕ) :
    (runMade W alloc keep start t).2 < W ∧
      (runMade W alloc keep start t).1.card ≤ R + (runMade W alloc keep start t).2 := by
  induction t with
  | zero => exact ⟨by simpa [runMade] using hW, by simpa [runMade] using hstart⟩
  | succ t ih =>
    obtain ⟨hlt, hcard⟩ := ih
    by_cases hz : (runMade W alloc keep start t).2 + (alloc t).card ≥ W
    · simp only [runMade, hz, if_true, add_zero]
      exact ⟨hW, hkeep _ _⟩
    · simp only [runMade, hz, if_false]
      refine ⟨by omega, ?_⟩
      calc ((runMade W alloc keep start t).1 ∪ alloc t).card
          ≤ (runMade W alloc keep start t).1.card + (alloc t).card :=
            Finset.card_union_le _ _
        _ ≤ R + ((runMade W alloc keep start t).2 + (alloc t).card) := by omega

/-- However long the loop runs, the heap stays below `R + W`, and the heap
a step makes before its collection within `R + W + a`. -/
theorem runMade_card_lt (W R a : ℕ) (alloc : ℕ → Finset α)
    (keep : ℕ → Finset α → Finset α) (start : Finset α) (hW : 0 < W)
    (hstart : start.card ≤ R) (hkeep : ∀ t s, (keep t s).card ≤ R)
    (halloc : ∀ t, (alloc t).card ≤ a) (t : ℕ) :
    (runMade W alloc keep start t).1.card < R + W ∧
      ((runMade W alloc keep start t).1 ∪ alloc t).card ≤ R + W + a := by
  obtain ⟨hlt, hcard⟩ := runMade_inv W R alloc keep start hW hstart hkeep t
  refine ⟨by omega, ?_⟩
  calc ((runMade W alloc keep start t).1 ∪ alloc t).card
      ≤ (runMade W alloc keep start t).1.card + (alloc t).card :=
        Finset.card_union_le _ _
    _ ≤ R + W + a := by have := halloc t; omega

/-- A loop that never collects keeps everything it made. -/
def uncollected (alloc : ℕ → Finset α) (start : Finset α) : ℕ → Finset α
  | 0 => start
  | t + 1 => uncollected alloc start t ∪ alloc t

theorem uncollected_eq (alloc : ℕ → Finset α) (start : Finset α) (t : ℕ) :
    uncollected alloc start t = start ∪ (Finset.range t).biUnion alloc := by
  induction t with
  | zero => simp [uncollected]
  | succ t ih =>
    rw [uncollected, ih, Finset.range_add_one, Finset.biUnion_insert]
    ext x
    simp only [Finset.mem_union]
    tauto

/-- Without a collection, steps making disjoint sets of `a` objects leave at
least `t * a` after `t` steps. -/
theorem uncollected_card_ge (a : ℕ) (alloc : ℕ → Finset α) (start : Finset α)
    (hcard : ∀ t, (alloc t).card = a)
    (hdisj : ∀ i j, i ≠ j → Disjoint (alloc i) (alloc j)) (t : ℕ) :
    t * a ≤ (uncollected alloc start t).card := by
  rw [uncollected_eq]
  have hbu : ((Finset.range t).biUnion alloc).card = t * a := by
    rw [Finset.card_biUnion (fun i _ j _ hij => hdisj i j hij)]
    simp [hcard]
  calc t * a = ((Finset.range t).biUnion alloc).card := hbu.symm
    _ ≤ (start ∪ (Finset.range t).biUnion alloc).card :=
      Finset.card_le_card Finset.subset_union_right

/-! ## Whole-form slices bounded by their parsed work -/

/-- Read whole forms until their accumulated work reaches the allowance.
The final form is indivisible, even when it alone exceeds the allowance. -/
def sliceWork (allowance : ℕ) : List ℕ → List ℕ
  | [] => []
  | cost :: rest =>
      if allowance ≤ cost then [cost]
      else cost :: sliceWork (allowance - cost) rest

/-- A slice's work is bounded by its allowance plus one largest form,
independently of the number or nesting depths of the other forms. -/
theorem sliceWork_sum_le (allowance largest : ℕ) (costs : List ℕ)
    (hcost : ∀ c ∈ costs, c ≤ largest) :
    (sliceWork allowance costs).sum ≤ allowance + largest := by
  induction costs generalizing allowance with
  | nil => simp [sliceWork]
  | cons cost rest ih =>
    have hc := hcost cost (by simp)
    have hr : ∀ c ∈ rest, c ≤ largest := by
      intro c h
      exact hcost c (by simp [h])
    by_cases stop : allowance ≤ cost
    · simp [sliceWork, stop]
      omega
    · simp only [sliceWork, stop, if_false, List.sum_cons]
      have bound := ih (allowance - cost) hr
      omega

/-- Increasing the cost of a form reduces the forms admitted in a slice. -/
example : sliceWork 10 [4, 4, 4, 4] = [4, 4, 4] := by decide

/-- A large form is retained whole; a fixed form count cannot supply this bound. -/
example : sliceWork 10 [40, 1, 1] = [40] := by decide

/-! ## Examples -/

/-- A clean activation's holdings survive a collection of a heap holding them. -/
example : ({1, 2} : Finset ℕ) ∩ {1, 2, 3} ⊆
    collect rootsOnly [⟨{1, 2}, ∅⟩] ({1, 2, 3} : Finset ℕ) := by decide

/-- An object no activation lists is collected. -/
example : (3 : ℕ) ∉ collect rootsOnly [⟨{1, 2}, ∅⟩] ({1, 2, 3} : Finset ℕ) := by decide

end Mettapedia.Machines.NestedSafePoints
