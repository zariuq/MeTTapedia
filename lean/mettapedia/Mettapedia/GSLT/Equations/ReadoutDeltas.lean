import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.List.Basic

/-! # What an incremental readout must know

A query counts the occurrences carried by the raw keys it accepts. Editing
recipes may change the acceptance mask; editing rows changes the weight at
a key. They act on different parts of the read, even when both edit the same
key. The signed identity below separates their work, and only inspects keys
in their respective footprints. It assumes the occurrence deltas are known;
a count does not determine whether a named occurrence is live.

For a whole family of future masks, class histograms are exact information
when the masks can distinguish every class separately. A consumer that
can remove the first result repeatedly is different: it can recover the
entire ordered stream, so its current first and count are not sufficient.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Equations.ReadoutDeltas

open scoped BigOperators

variable {K : Type*}

def contribution {M : Type*} [Zero M] (accept : K → Bool) (weight : K → M) (k : K) : M :=
  if accept k then weight k else 0

def mass {M : Type*} [AddCommMonoid M] (keys : Finset K) (accept : K → Bool)
    (weight : K → M) : M :=
  ∑ k ∈ keys, contribution accept weight k

/-! ## A mixed update over a single coherent cut -/

def maskDelta (changed : Finset K) (before after : K → Bool) (old : K → Int) : Int :=
  ∑ k ∈ changed, (contribution after old k - contribution before old k)

def rowDelta (changed : Finset K) (after : K → Bool) (old new : K → Int) : Int :=
  mass changed after (fun k => new k - old k)

theorem full_delta (keys : Finset K) (before after : K → Bool) (old new : K → Int) :
    mass keys after new =
      mass keys before old + maskDelta keys before after old + rowDelta keys after old new := by
  simp only [mass, maskDelta, rowDelta, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  cases b : before k <;> cases a : after k <;> simp [contribution, b, a]

/-- Update a materialized scalar from the two delta footprints. The
membership change uses the old multiplicities, and the row change uses
the new membership. Using both old projections silently misses the
cross term when a key is edited on both axes. -/
theorem sparse_delta (keys changedMask changedRows : Finset K)
    (before after : K → Bool) (old new : K → Int)
    (maskIn : changedMask ⊆ keys) (rowIn : changedRows ⊆ keys)
    (maskFrame : ∀ k ∈ keys, k ∉ changedMask → before k = after k)
    (rowFrame : ∀ k ∈ keys, k ∉ changedRows → old k = new k) :
    mass keys after new =
      mass keys before old + maskDelta changedMask before after old +
        rowDelta changedRows after old new := by
  have hm : maskDelta changedMask before after old = maskDelta keys before after old := by
    apply Finset.sum_subset maskIn
    intro k member outside
    simp [contribution, maskFrame k member outside]
  have hr : rowDelta changedRows after old new = rowDelta keys after old new := by
    apply Finset.sum_subset rowIn
    intro k member outside
    simp [contribution, rowFrame k member outside]
  rw [hm, hr]
  exact full_delta keys before after old new

/-! ## What can be forgotten when later masks are known -/

section Fibres

variable {Class M : Type*} [DecidableEq Class] [AddCommMonoid M]

def histogram (keys : Finset K) (group : K → Class) (weights : K → M) (c : Class) : M :=
  ∑ k ∈ keys.filter (fun k => group k = c), weights k

theorem regroup (keys : Finset K) (group : K → Class) (weights : K → M) (mask : Class → Bool) :
    mass keys (mask ∘ group) weights =
      mass (keys.image group) mask (histogram keys group weights) := by
  unfold mass
  rw [← Finset.sum_fiberwise_of_maps_to (g := group) (t := keys.image group)
    (fun k member => Finset.mem_image_of_mem group member) (contribution (mask ∘ group) weights)]
  apply Finset.sum_congr rfl
  intro c _
  cases h : mask c with
  | false =>
    simp only [contribution, h, Bool.false_eq_true, if_false]
    apply Finset.sum_eq_zero
    intro k present
    have key : group k = c := (Finset.mem_filter.mp present).2
    simp [Function.comp_apply, key, h]
  | true =>
    simp only [contribution, h, if_true, histogram]
    apply Finset.sum_congr rfl
    intro k present
    have key : group k = c := (Finset.mem_filter.mp present).2
    simp [Function.comp_apply, key, h]

/-- Equal histograms are both necessary and sufficient for every mask
factoring through the given signature. Necessity uses the future request
that selects one signature fibre. A smaller family may not observe every
fibre, so this is not a universal lower bound for one fixed query. -/
theorem all_masks_iff_histogram (keys : Finset K) (group : K → Class) (left right : K → M) :
    (∀ mask : Class → Bool, mass keys (mask ∘ group) left = mass keys (mask ∘ group) right) ↔
      ∀ c, histogram keys group left c = histogram keys group right c := by
  constructor
  · intro same c
    have pick := same (fun d => decide (d = c))
    simpa only [mass, contribution, Function.comp_apply, decide_eq_true_eq,
      ← Finset.sum_filter, histogram] using pick
  · intro same mask
    rw [regroup, regroup]
    apply Finset.sum_congr rfl
    intro c _
    simp [contribution, same c]

end Fibres

/-! ## First is cheap once; repeated first exposes the whole run -/

theorem repeated_first_iff_ordered {Row : Type*} (left right : List Row) :
    (∀ consumed : Nat, (left.drop consumed).head? = (right.drop consumed).head?) ↔
      left = right := by
  constructor
  · intro same
    exact List.ext_getElem? fun i => by simpa only [List.head?_drop] using same i
  · rintro rfl _
    rfl

namespace Examples

/-- The two edits can hit the same key. Applying the row delta through the
old mask gives zero; the new complete count is two. -/
theorem simultaneous_edit_sees_new_rows :
    mass ({()} : Finset Unit) (fun _ => true) (fun _ => (2 : Int)) = 2 ∧
      maskDelta ({()} : Finset Unit) (fun _ => false) (fun _ => true) (fun _ => 1) = 1 ∧
      rowDelta ({()} : Finset Unit) (fun _ => false) (fun _ => 1) (fun _ => 2) = 0 ∧
      rowDelta ({()} : Finset Unit) (fun _ => true) (fun _ => 1) (fun _ => 2) = 1 := by
  simp [mass, contribution, maskDelta, rowDelta]

private def coldOnly (k : Bool) : Nat := if k then 0 else 1
private def warmOnly (k : Bool) : Nat := if k then 1 else 0
private def bothKeys : Finset Bool := {false, true}

/-- An aggregate cached while Cold and Warm are one class cannot answer
a later split that distinguishes their original buckets. -/
theorem merged_count_does_not_survive_a_split :
    mass bothKeys (fun _ => true) coldOnly = mass bothKeys (fun _ => true) warmOnly ∧
    mass bothKeys (fun key => !key) coldOnly ≠ mass bothKeys (fun key => !key) warmOnly := by
  simp [mass, contribution, coldOnly, warmOnly, bothKeys]

theorem count_and_first_do_not_support_delete_first :
    let xs := [0, 4]
    let ys := [0, 7]
    (xs.length, xs.head?) = (ys.length, ys.head?) ∧ xs.tail.head? ≠ ys.tail.head? := by
  decide

end Examples

end Mettapedia.GSLT.Equations.ReadoutDeltas
