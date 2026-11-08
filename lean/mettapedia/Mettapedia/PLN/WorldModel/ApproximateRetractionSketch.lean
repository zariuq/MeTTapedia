import Mettapedia.PLN.WorldModel.ApproximateRetraction
import Mathlib.Data.Fintype.BigOperators

/-!
# A linear sketch with deletions: bounded manufacture

Claims are hashed into buckets, and a bucket holds the summed evidence of its claims (`sketch`).  A
claim is read from its bucket (`estimate`), so its reading includes the evidence of the claims it
collides with (`collision`).  It never undercounts, and it overcounts by exactly the colliding
evidence (`estimate_eq`, `sketch_encloses`).  Lineage deletion, truncation and caps err downward;
the sketch errs upward: it manufactures evidence, boundedly.

* **Deletion is exact on the sketch.**  Subtracting the sketch of the withdrawn contributions gives
  the sketch of the remaining evidence (`sketch_sub`); the whole error is in the reading.  A source
  can be withdrawn only through a contribution vector the sketch can represent.
* **A collision bound survives every deletion** (`collision_sub_le`) and adds under revision
  (`collision_add`), so repeated deletion accumulates nothing.
* **Relevance fails by the withdrawn colliding evidence.**  After a deletion a claim reads its
  remaining evidence plus the remaining colliding evidence (`estimate_sub`).  Withdrawing a source
  that touched only the other claim of a bucket moves this claim's reading from `2` to `1`, although
  its own evidence stays `1` (`Controls.relevance_fails`).
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.ApproximateRetractionSketch

open scoped NNReal
open Mettapedia.PLN.WorldModel.ApproximateRetraction

variable {Claim Bucket : Type*} [Fintype Claim] [DecidableEq Bucket]

/-- The sketch of an evidence profile: each bucket holds the summed evidence of its claims. -/
noncomputable def sketch (h : Claim → Bucket) (f : Claim → ℝ≥0) (b : Bucket) : ℝ≥0 :=
  ∑ q ∈ Finset.univ.filter (fun q => h q = b), f q

/-- A claim is read from its bucket. -/
def estimate (h : Claim → Bucket) (z : Bucket → ℝ≥0) (q : Claim) : ℝ≥0 := z (h q)

/-- **Deletion is exact on the sketch**: subtracting the sketch of withdrawn contributions that the
profile covers gives the sketch of what remains. -/
theorem sketch_sub (h : Claim → Bucket) {f r : Claim → ℝ≥0} (le : ∀ q, r q ≤ f q) (b : Bucket) :
    sketch h f b - sketch h r b = sketch h (fun q => f q - r q) b := by
  unfold sketch
  rw [Finset.sum_tsub_distrib _ fun q _ => le q]

/-- A bucket holding every claim sums all of them. -/
theorem sketch_of_const (h : Claim → Bucket) (f : Claim → ℝ≥0) {b : Bucket} (all : ∀ q, h q = b) :
    sketch h f b = ∑ q, f q := by
  unfold sketch
  rw [Finset.filter_true_of_mem fun q _ => all q]

variable [DecidableEq Claim]

/-- The evidence of the other claims in a claim's bucket. -/
noncomputable def collision (h : Claim → Bucket) (f : Claim → ℝ≥0) (q : Claim) : ℝ≥0 :=
  ∑ q' ∈ (Finset.univ.filter fun q' => h q' = h q).erase q, f q'

/-- **The reading is the claim's evidence plus the colliding evidence.** -/
theorem estimate_eq (h : Claim → Bucket) (f : Claim → ℝ≥0) (q : Claim) :
    estimate h (sketch h f) q = f q + collision h f q := by
  unfold estimate sketch collision
  rw [← Finset.add_sum_erase (Finset.univ.filter fun q' => h q' = h q) f
    (Finset.mem_filter.mpr ⟨Finset.mem_univ q, rfl⟩)]

/-- **The sketch never undercounts and overcounts by the colliding evidence**: the exact evidence
encloses the reading from below, with the collision as width. -/
theorem sketch_encloses (h : Claim → Bucket) (f : Claim → ℝ≥0) (q : Claim) :
    Encloses (f q) (collision h f q) (estimate h (sketch h f) q) := by
  rw [estimate_eq]
  exact ⟨le_self_add, le_rfl⟩

/-- **After a deletion a claim reads its remaining evidence plus the remaining colliding
evidence.** -/
theorem estimate_sub (h : Claim → Bucket) {f r : Claim → ℝ≥0} (le : ∀ q, r q ≤ f q) (q : Claim) :
    estimate h (fun b => sketch h f b - sketch h r b) q =
      (f q - r q) + collision h (fun q => f q - r q) q := by
  show sketch h f (h q) - sketch h r (h q) = _
  rw [sketch_sub h le]
  exact estimate_eq h (fun q => f q - r q) q

/-- **A collision bound survives every deletion.** -/
theorem collision_sub_le (h : Claim → Bucket) (f r : Claim → ℝ≥0) (q : Claim) :
    collision h (fun q => f q - r q) q ≤ collision h f q := by
  unfold collision
  exact Finset.sum_le_sum fun _ _ => tsub_le_self

/-- **Revision adds collisions.** -/
theorem collision_add (h : Claim → Bucket) (f g : Claim → ℝ≥0) (q : Claim) :
    collision h (fun q => f q + g q) q = collision h f q + collision h g q := by
  unfold collision
  exact Finset.sum_add_distrib

namespace Controls

/-- Two claims sharing one bucket. -/
def oneBucket : Bool → Unit := fun _ => ()

/-- Each claim holds one observation. -/
def held : Bool → ℝ≥0 := fun _ => 1

/-- The withdrawn source touched only the claim `false`. -/
def withdrawn : Bool → ℝ≥0 := fun q => if q then 0 else 1

/-- **Relevance fails, and the reading manufactured evidence.**  The withdrawn source did not touch
`true`, whose evidence is `1` before and after; its reading is `2` before the deletion and `1`
after. -/
theorem relevance_fails :
    withdrawn true = 0 ∧ held true - withdrawn true = 1 ∧
      estimate oneBucket (sketch oneBucket held) true = 2 ∧
      estimate oneBucket (fun b => sketch oneBucket held b - sketch oneBucket withdrawn b) true =
        1 := by
  have before : sketch oneBucket held () = 2 := by
    rw [sketch_of_const oneBucket held fun _ => rfl, Fintype.sum_bool]
    exact one_add_one_eq_two
  have gone : sketch oneBucket withdrawn () = 1 := by
    rw [sketch_of_const oneBucket withdrawn fun _ => rfl, Fintype.sum_bool]
    simp [withdrawn]
  refine ⟨rfl, ?_, before, ?_⟩
  · simp [held, withdrawn]
  · show sketch oneBucket held () - sketch oneBucket withdrawn () = 1
    rw [before, gone]
    exact tsub_eq_of_eq_add one_add_one_eq_two.symm

end Controls

end Mettapedia.PLN.WorldModel.ApproximateRetractionSketch

open Mettapedia.PLN.WorldModel.ApproximateRetractionSketch in
#print axioms sketch_sub
open Mettapedia.PLN.WorldModel.ApproximateRetractionSketch in
#print axioms estimate_eq
open Mettapedia.PLN.WorldModel.ApproximateRetractionSketch in
#print axioms sketch_encloses
open Mettapedia.PLN.WorldModel.ApproximateRetractionSketch in
#print axioms estimate_sub
open Mettapedia.PLN.WorldModel.ApproximateRetractionSketch in
#print axioms collision_sub_le
open Mettapedia.PLN.WorldModel.ApproximateRetractionSketch in
#print axioms collision_add
open Mettapedia.PLN.WorldModel.ApproximateRetractionSketch in
#print axioms Controls.relevance_fails
